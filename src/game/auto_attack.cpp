#include "mind.h"
#include "hero_profile.h"
#include "game/act.h"
#include "game/auto_attack.h"
#include "game/combat_learn.h"
#include "game/gear.h"
#include "game/auto_start.h"
#include "game/agent_save.h"
#include "game/teleports.h"
#include "game/portals.h"
#include "game/route_net.h"
#include "game/agent_cursor.h"
#include "game/agent_overlay.h"
#include "game/hero_build.h"
#include "game/lore.h"
#include "game/click_walk.h"
#include "game/hero_move.h"
#include "game/map_memory.h"
#include "game/whereabouts.h"
#include "game/findings.h"
#include "config/auto_attack.h"
#include "config/controller.h"
#include "config/tactics.h"
#include "game/aim_assist.h"
#include "game/combat_state.h"
#include "game/controller.h"
#include "game/focus.h"
#include "game/frame_hooks.h"
#include "game/modkit_menu.h"
#include "game/tactics.h"
#include "game/granny_async.h"
#include "game/ui_nav.h"
#include "input/inject.h"
#include "log.h"
#include "sacred/engine.h"
#include "sacred/object.h"
#include "sacred/ui.h"

#include <imgui.h>
#include <windows.h>
#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cmath>
#include <cstring>
#include <cstdlib>
#include <iterator>
#include <mutex>
#include <thread>
#include <format>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <deque>
#include <vector>

using namespace Sacred;

namespace
{
    // The order a left click on a creature or object gives (the world mouse handler, ENG 006172C0, at 00617935):
    // cOrder's layout with type 7, the picked id at +0x18 and the clicked world point after it. The handler hands
    // it straight to the controlled creature's order handler (vtable +0x18), not through cEngine::sendOrder, which
    // would snap +0x18/+0x1C as a walk target. On an enemy the hero walks up to it and attacks it.
    struct UseOrder
    {
        uintptr_t vtable = Addr::cOrder_vtable;
        uint32_t type = 7;
        uint8_t _08[0x18 - 0x08] = {};
        uint32_t target = 0;
        int32_t x = 0, y = 0;
        uint8_t _24[0x44 - 0x24] = {};
    };
    static_assert(sizeof(UseOrder) == sizeof(cOrder));
    static_assert(offsetof(UseOrder, target) == 0x18 && offsetof(UseOrder, x) == 0x1C && offsetof(UseOrder, y) == 0x20);

    // cCreature's order handler, thiscall (order*), callee pops.
    using OrderHandler = void(__fastcall*)(cCreature* self, void* edx, UseOrder* order);

    // MSVC's RTTI behind every vtable (vtable[-1], the complete object locator): the object's own class.
    struct TypeDescriptor
    {
        const void* vtable;
        void* spare;
        char name[1];
    };
    struct CompleteObjectLocator
    {
        uint32_t signature, offset, cdOffset;
        const TypeDescriptor* type;
        const void* hierarchy;
    };

    enum class Loot : uint8_t
    {
        None,
        Item,       // cItemBase: lying on the ground, a click picks it up
        Container,  // cChest3D: chests, coffers and the like, a click opens them
        Fixed,      // a fixed thing of the map the cursor shows the hand on (id with bit 31): magic hiding places,
                    // wells, gold (not runes and signposts, see fixedUsable); a click uses it. No object behind it, only its place in the pick list.
    };

    // The pick list's ids with bit 31 set are the map's fixed things the cursor can use (the world mouse handler,
    // ENG 00617939, gives them the same order 7 as objects, with the world point under the cursor).
    constexpr uint32_t kFixedId = 0x80000000u;
    bool isFixed(uint32_t id)
    {
        return (id & kFixedId) != 0;
    }

    // The map's fixed things (ENG 0053B713: the low 16 bits of the id index it): records of 0x58 bytes, a kind at +4
    // and a script name at +0x18. Seen in a whole map (2026-11-07): the usable ones, kind 0x00010000, are VERSTECK
    // (magic hiding places), BRUNNEN (wells) and F_Gold; the rest, kind 0.25f, are scripts and texts: F_Stein (runes),
    // Wegweiser (signposts), setvar triggers, Powerup. Only the usable ones are taken: a text is not loot.
    constexpr uintptr_t kFixedBegin = 0xAB45B8, kFixedEnd = 0xAB45BC;
    constexpr size_t kFixedSize = 0x58, kFixedKind = 0x04, kFixedName = 0x18;
    constexpr uint32_t kFixedUsable = 0x00010000;

    size_t fixedCount()
    {
        const auto* begin = *reinterpret_cast<const uint8_t* const*>(kFixedBegin);
        const auto* end = *reinterpret_cast<const uint8_t* const*>(kFixedEnd);
        return begin && end >= begin ? static_cast<size_t>(end - begin) / kFixedSize : 0;
    }

    const uint8_t* fixedRecord(uint32_t id)
    {
        const size_t index = id & 0xFFFF;
        return index < fixedCount() ? *reinterpret_cast<const uint8_t* const*>(kFixedBegin) + index * kFixedSize
                                    : nullptr;
    }

    // Where the fixed thing stands (world): its tile (+0, +2), where the game sends a creature using it (ENG 0053B784).
    constexpr double kFixedTile = 53.66563;
    bool fixedPosition(uint32_t id, int32_t& x, int32_t& y)
    {
        const uint8_t* record = fixedRecord(id);
        if (!record)
        {
            return false;
        }
        x = static_cast<int32_t>((*reinterpret_cast<const uint16_t*>(record) + 0.5) * kFixedTile);
        y = static_cast<int32_t>((*reinterpret_cast<const uint16_t*>(record + 2) + 0.5) * kFixedTile);
        return true;
    }

    // What the bookkeeping below keys loot by: an object's id, a fixed thing's tile (the game drops a used hiding
    // place from the table, which moves the later ones down: their ids change).
    uint32_t lootKey(uint32_t id)
    {
        int32_t x = 0, y = 0;
        if (!isFixed(id) || !fixedPosition(id, x, y))
        {
            return id;
        }
        const uint32_t tx = static_cast<uint32_t>(x / kFixedTile) & 0x7FFF, ty = static_cast<uint32_t>(y / kFixedTile) & 0xFFFF;
        return kFixedId | (tx << 16) | ty;
    }

    // Stones with the hand cursor (F_Stein): runes, plaques and gravestones (seen live, 2026-11-09: a click opens
    // the gravestone's dialog, "Abrir" / "Salir"; "Abrir" gives a second one with the outcome, "Aceptar": empty, an
    // item, or enemies). Each is tried once: the dialogs are answered with their first answer (Enter), and a stone
    // with only text closes the same way.
    bool fixedStone(const uint8_t* record)
    {
        return record && std::memcmp(record + kFixedName, "F_Stein", 7) == 0;
    }

    bool fixedStone(uint32_t id)
    {
        return isFixed(id) && fixedStone(fixedRecord(id));
    }

    bool fixedUsable(uint32_t id)
    {
        const uint8_t* record = fixedRecord(id);
        if (!record)
        {
            return false;
        }
        const bool usable =
            *reinterpret_cast<const uint32_t*>(record + kFixedKind) == kFixedUsable || fixedStone(record);
        static std::unordered_set<uint32_t> logged;
        if (logged.insert(id).second && logged.size() < 512)
        {
            char name[0x40 + 1] = {};
            std::memcpy(name, record + kFixedName, 0x40);
            LOG("AutoAttack: fixed thing {} ({:x}) is {}", name, id, usable ? "taken" : "left alone");
        }
        return usable;
    }

    // The pick category the world pick ranks by (cObject::Vtable::pickCategory): Alt puts 2 first, the things lying
    // on the ground that Alt shows the names of.
    constexpr uint16_t kPickItem = 2;

    // The object's flags (cObject +0x14). Bit 0 marks fixtures the game still ranks as ground items: signposts and
    // plaques (cSpecial3D like gold and quest items, whose click only opens their text). Seen: signpost 04000001;
    // weapons, rings, gold 04000000, gold a monster dropped 04100000.
    constexpr size_t kObjectFlags = 0x14;
    constexpr uint32_t kFixtureFlag = 0x1;

    // A town's storage chest (TYPE_OBJECT_CHEST_STATIC): all of them open the hero's one storage, inventory entry 0x11
    // ([0xAD4448] + 0x11 * 0x1180, the backpack's layout: cells of 12 bytes from +0x18, width +0x115C, height +0x115E;
    // live 20x10, Manolito block BH). Its contents are read through the game's own functions (Gear's GetEntry and
    // GetInfo): reading the pointers by hand here crashed every copy 35 s after loading (2026-11-16, DDRAW.dll+d801).
    constexpr uint16_t kStorageChest = 0x1450;

    // The storage chest last seen (the one to go to when Gear wants it): its id, place and layer.
    struct StorageSeen
    {
        uint32_t id = 0;
        int32_t x = 0, y = 0;
        int layer = -1;
    };
    // Every storage chest seen (the world holds every town's at once: 29 at a load in A7, 2026-11-16), and the one
    // gone to: the nearest on the hero's layer, chosen at each roam.
    std::unordered_map<uint32_t, StorageSeen> g_storages;
    StorageSeen g_storage;
    std::atomic<int> g_destRegion{-1};
    std::atomic<bool> g_storageNear{false};

    void storageSeen(cObject* object)
    {
        static std::unordered_set<uint32_t> s_marked;
        g_storages[object->id] = {object->id, object->x, object->y, *(reinterpret_cast<const uint8_t*>(object) + 0x24)};
        if (!s_marked.insert(object->id).second)
        {
            return;
        }
        const int layer = *(reinterpret_cast<const uint8_t*>(object) + 0x24);
        const int tx = static_cast<int>(object->x / 53.66563), ty = static_cast<int>(object->y / 53.66563);  // kTileSize, defined further on
        MapMemory::mark(MapMemory::Mark::Storage, layer, object->x, object->y);
        LOG("AutoAttack: storage chest {:x} at tile {},{} (layer {}): the hero's store, never loot", object->id, tx, ty, layer);
    }

    // What the object is: a cChest3D (its own class, by RTTI; it derives from cItemBase) is a container; anything
    // else the game ranks as a ground item is an item, whatever its class (gold included), but fixtures.
    Loot lootOf(cObject* object)
    {
        const void* vtable = object->vtable;
        const auto* locator = reinterpret_cast<const CompleteObjectLocator* const*>(vtable)[-1];
        const char* name = locator && locator->type ? locator->type->name : "?";
        const uint16_t category = object->vtable->pickCategory(object, nullptr, 1, 0);
        Loot loot = Loot::None;
        if (std::strcmp(name, ".?AVcChest3D@@") == 0 &&
            *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(object) + 0x10) == kStorageChest)
        {
            // A town's storage chest: the hero's own store, never loot (the player, 2026-11-16: «lo abren mucho pero
            // no lo usan para nada»; A5 went three times for «a chest not yet opened» d8, its town's storage). Kept on
            // the map, and its contents told once.
            storageSeen(object);
        }
        else if (std::strcmp(name, ".?AVcChest3D@@") == 0)
        {
            loot = Loot::Container;
        }
        else if (category == kPickItem)
        {
            const uint32_t flags = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) +
                                                                     kObjectFlags);
            // A quest item (0x800, Gear's kQuestItem) is taken though it carries the fixture bit too (the player,
            // 2026-11-12: A5 walked to a shining TYPE_OBJECT_QI_WATERSKIN, flags 04000801, on its quest's goal and
            // never picked it up).
            loot = (flags & kFixtureFlag) && !(flags & 0x800) ? Loot::None : Loot::Item;
        }
        // Each class and category once, to see in the log what is taken and what is not.
        static std::unordered_set<uint64_t> logged;
        if (logged.insert(reinterpret_cast<uintptr_t>(vtable) | (static_cast<uint64_t>(category) << 32)).second)
        {
            LOG("AutoAttack: class {} category {} (id {:x}) is {}", name, category, object->id,
                loot == Loot::Item ? "an item" : loot == Loot::Container ? "a container" : "left alone");
        }
        return loot;
    }

    // A quest's thing to fetch, not someone to speak to: the journal's +0x14 can name an item (the quests' session,
    // 2026-11-16: the Pay Book DQ_15004, «who» the book in Azrott's house; on 13-11 A1 went in, collected it and took
    // it to Azrott; since the 14-11 swap of a «no creature» for the nearest villager no copy has done it). An item
    // lying in the world with the quest item flag (0x800, Gear's kQuestItem).
    bool questThing(const cObject* object)
    {
        if (!object || const_cast<cObject*>(object)->asCreature())
        {
            return false;
        }
        const uint32_t flags = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) + kObjectFlags);
        return (flags & 0x800) != 0;
    }

    // Equipment by its class (RTTI): weapons, armour, rings, amulets. Only these get the grade filter: gold, potions,
    // scrolls, runes and upgrades are always taken (the player, 2026-11-09: «se salta hasta el oro»).
    bool isEquipment(const cObject* object)
    {
        const auto* locator = reinterpret_cast<const CompleteObjectLocator* const*>(object->vtable)[-1];
        const char* name = locator && locator->type ? locator->type->name : "";
        return std::strcmp(name, ".?AVcWeapon3D@@") == 0 || std::strcmp(name, ".?AVcArmor3D@@") == 0 ||
               std::strcmp(name, ".?AVcRing3D@@") == 0 || std::strcmp(name, ".?AVcShield3D@@") == 0 ||
               std::strstr(name, "Amulet") != nullptr;
    }

    // Loot the hero failed at: opened containers, items it stood at without picking them up (a full inventory) or
    // could not reach. Tried again later, a few times, as the hero may have been busy or the way blocked.
    struct LootFailure
    {
        DWORD retryAt = 0;
        int count = 0;
    };
    std::unordered_map<uint32_t, LootFailure> g_lootFailures;
    // Not reached (behind a fence, across a river): tried again a minute later (then two), up to kLootTries in all.
    // Still there with the hero at it (a pick up cut short by a blow, a nudge lost): again after kLootSoonMs. Seen
    // live (2026-11-09): a weapon left for good after one such try, the backpack with room.
    constexpr int kLootTries = 4;
    constexpr DWORD kLootRetryMs = 60000;
    constexpr DWORD kLootSoonMs = 4000;

    bool lootBlocked(uint32_t id, DWORD now)
    {
        id = lootKey(id);
        const auto it = g_lootFailures.find(id);
        return it != g_lootFailures.end() &&
               (it->second.count >= kLootTries || static_cast<int>(now - it->second.retryAt) < 0);
    }

    // Loot the hero stood at and that stayed: an opened container, an item that did not fit. Never gone for again; nor loot
    // not reached four times.
    std::unordered_set<uint32_t> g_lootDone;

    void lootFailed(uint32_t id, DWORD now, bool soon = false)
    {
        id = lootKey(id);
        if (g_lootFailures.size() > 1024)
        {
            g_lootFailures.clear();
        }
        LootFailure& f = g_lootFailures[id];
        ++f.count;
        // Three times as long each time, left for good at the fourth (the analyst, 2026-11-10: the same loot «not
        // reached» again and again in a few minutes).
        DWORD wait = kLootRetryMs;
        for (int i = 1; i < f.count && wait < 1800000; ++i)
        {
            wait *= 3;
        }
        f.retryAt = now + (soon ? kLootSoonMs : wait);
        if (!soon && f.count >= 4)
        {
            g_lootDone.insert(id);
        }
    }

    // The hero gets no nearer to the loot for this long: it cannot reach it (behind a fence, in a house).
    constexpr DWORD kLootStuckMs = 6000;
    // How long it may stand at the loot before we leave it.
    constexpr DWORD kLootAtMs = 3000;
    // A loot order is given once (giving it again restarts the pick up, so gold farther than a second away was
    // never taken); again only after this long without the hero getting nearer.
    constexpr DWORD kLootNudgeMs = 1200;
    // Loot gone from the ground is being picked up: no new order for this long, which would cut the hero's
    // stooping short and cancel the pick up.
    constexpr DWORD kPickupMs = 1300;
    constexpr float kLootAtDistance = 2.5f * 53.66563f;   // world units, 2.5 tiles

    bool g_on = false;
    bool g_keyWasDown = false;
    uint32_t g_target = 0;          // the enemy we attack or the loot we go for, 0 for none
    bool g_looting = false;         // g_target is loot
    // Loot and fights weigh alike (the user, 2026-11-09): on each look, loot nearer to the hero than the chosen enemy
    // is taken first, enemies about or not. Loot taken that way is one piece, then
    // the fight again (g_collectOne), a hit meanwhile not ending it.
    bool g_lootInstead = false;
    bool g_lootInsteadAll = false;  // ... all of it (nobody attacks), not one piece and back to the fight
    bool g_collectOne = false;
    DWORD g_lootAtSince = 0;        // since when the hero stands at it, 0 while it does not
    bool g_lootStill = false;       // lootDone gave up on it with the hero at it and the thing still there
    bool g_lootStale = false;       // ... or its id now names another fixed thing (the table shifted): nothing marked
    float g_lootBest = 0.0f;        // the nearest the hero got to it, world units
    DWORD g_lootBestAt = 0;         // when it got that near
    DWORD g_sentAt = 0;             // when the last order went out
    DWORD g_quietUntil = 0;         // the player's own clicks: no auto attack before this tick
    DWORD g_pickupUntil = 0;        // a pick up under way: no new order before this tick

    // The physical state: SacredBild's GetAsyncKeyState is not the game's patched import, so injected input and
    // the controller never show here.
    bool physicallyDown(int vk)
    {
        return (GetAsyncKeyState(vk) & 0x8000) != 0;
    }

    // A mouse button held: the player gives their own orders. Moving the mouse does not count, so the cursor stays
    // free for the inventory and other windows while the hero fights.
    bool playerClicks()
    {
        return physicallyDown(VK_LBUTTON) || physicallyDown(VK_RBUTTON) || physicallyDown(VK_MBUTTON);
    }

    bool heroAlive()
    {
        int health = 0, maximum = 0;
        return AimAssist::heroHealth(health, maximum) && health > 0;
    }

    // The hero casts a combat art or a spell (the player's own, when Tactics is not busy): any order now, an attack,
    // a walk or a pick up, cuts it short.
    bool heroCasting()
    {
        cObjectManager* objects = cObjectManager::instance();
        return objects && CombatState::casting(objects->hero());
    }

    // All the loot seen is taken before the hero goes on, on a trip too (the player's wish, 2026-11-09: none left
    // behind but when it does not fit). Never further than kLootMaxTiles (a fixed thing's place read wrong put one
    // 3000 tiles off). g_questTravel: the hero is on a trip.
    // A creature's level as it will be fought (Manolito, block AP, 2026-11-13: cCreature::scaleLevelToHero 0x550E50):
    // one not yet scaled (no flag 0x200 at +0x1F4, its level 1 or 1000) becomes the hero's level + 2 once it is, so
    // its «level 1» is no weakling's. The hero's own is read as it is.
    int scaledLevel(const void* creature)
    {
        const auto* c = reinterpret_cast<const uint8_t*>(creature);
        const int level = *reinterpret_cast<const uint16_t*>(c + 0x3FE);
        cObjectManager* objects = cObjectManager::instance();
        const void* hero = objects ? objects->hero() : nullptr;
        if (!hero || creature == hero || (*reinterpret_cast<const uint32_t*>(c + 0x1F4) & 0x200) || (level != 1 && level != 1000))
        {
            return level;
        }
        return *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x3FE) + 2;
    }

    bool g_questTravel = false;
    // At the goal of a quest that asks for a kill: the fights around it are sought until then (the bear of DQ_15003,
    // the wolves' leader of R01NQ01, Gnarf of DQ_15011: the hero stood 2 tiles from the goal and fought only what
    // struck first; 1 of 8, 2 of 6 and 2 of 6 copies had them done, 2026-11-13).
    DWORD g_questSeekUntil = 0;
    constexpr double kLootMaxTiles = 60.0;
    // On a trip (a quest's goal, a merchant) the focus is the trip (the player, 2026-11-10: «si pretende hacer quest el
    // foco no es batallar necesariamente»): only loot at hand is taken on the way.
    constexpr double kTripLootTiles = 8.0;

    // What the agent is about and why (the player, 2026-11-10: «en cada cosa que hace tiene que saber el motivo de por
    // qué lo hace; si pretende farmear, el foco no es ir a la quest»). Set by the branch that drives the hero, logged on
    // each change with its reason; the branches that would pull the hero elsewhere (loot, seeking enemies, quests while
    // farming) read it.
    enum class Intent
    {
        Explore,
        Farm,
        Quest,
        Shop,
        Recover,
        Escape,
    };
    Intent g_intent = Intent::Explore;
    std::string g_intentWhy;
    DWORD g_intentSince = 0;

    const char* intentName(Intent i)
    {
        switch (i)
        {
        case Intent::Farm: return "farm";
        case Intent::Quest: return "quest";
        case Intent::Shop: return "shop";
        case Intent::Recover: return "recover";
        case Intent::Escape: return "escape";
        default: return "explore";
        }
    }

    // The agent's last decisions, for its mind map (the player, 2026-11-10: «cómo el agente está pensando»).
    std::vector<std::string> g_decisions;

    void remember(const std::string& what)
    {
        SYSTEMTIME t;
        GetLocalTime(&t);
        char at[16];
        std::snprintf(at, sizeof at, "%02d:%02d:%02d ", t.wHour, t.wMinute, t.wSecond);
        g_decisions.push_back(at + what);
        if (g_decisions.size() > 8)
        {
            g_decisions.erase(g_decisions.begin());
        }
    }

    void setIntent(Intent i, const std::string& why)
    {
        if (i == g_intent && why == g_intentWhy)
        {
            return;
        }
        // Logged on each change of intent; a new reason for the same one at most every 30 s (the log stays readable).
        static DWORD s_toldAt = 0;
        const DWORD tick = GetTickCount();
        if (i != g_intent)
        {
            g_intentSince = tick;
        }
        if (i != g_intent || tick - s_toldAt > 30000)
        {
            s_toldAt = tick;
            LOG("Intent: {} ({})", intentName(i), why);
            remember(std::string("intención ") + intentName(i) + ": " + why);
        }
        g_intent = i;
        g_intentWhy = why;
    }

    bool lootNear(int32_t x, int32_t y)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!hero)
        {
            return false;
        }
        const double tiles = std::max(std::abs(static_cast<double>(x - hero->x)), std::abs(static_cast<double>(y - hero->y))) /
                             kFixedTile;
        // All of it before going on; on a trip only what lies at hand (the player's newer wish: the focus is the trip).
        return tiles <= (g_questTravel ? kTripLootTiles : kLootMaxTiles);
    }

    // Doors (AGENT_ADDRESSES «Puertas y entradas»: TYPE_OBJECT_DOOR_* 0x1612..0x1697 and TYPE_OBJECT_S_DOOR 0x1465,
    // cObject3D; the village's open with a click). Only shut ones a key or a click opens (their trigger, below): a door is
    // used, as the player's click on it does, when the hero is stuck, the nearest one not tried for 2 minutes.
    std::unordered_map<uint32_t, DWORD> g_doorTried;
    // After a click on a door, the hero is let walk to it and use it (a diagnosis of the logs, 2026-11-10: the Daemon
    // 14 min in a merchant's house, a Seraphim 10 min in a cave: each door click overridden 0.13-3.6 s later by the
    // roam's, the quest's or the shop's own walk, the door never reached).
    DWORD g_doorHoldUntil = 0;
    DWORD g_entranceHoldUntil = 0;  // on the way to a house's way in: no chest takes the walk over meanwhile
    DWORD g_craftHoldUntil = 0;     // by a craftsman until then: the roam and the stray dialog's Enter wait
    // Far quest goals (over 300 tiles) the position watch found the hero not getting anywhere towards, in the last 10 min.
    int g_farFails = 0;
    DWORD g_farFailAt = 0;
    // The walk to the way out of where the hero is shut in, ordered by the stuck guard: kept by the roam (and the arrow
    // dodge) until the hero is there or the time is up (the stuck solver, 2026-11-16, A5 in the cave 5.2: nine of nine
    // such orders taken over by the roam's own goals within 3-11 s).
    int32_t g_wayOutX = 0, g_wayOutY = 0;
    DWORD g_wayOutUntil = 0;
    float g_doorRange = 12.0f * 53.66563f;

    bool acceptDoor(uint32_t id, void*)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        cObject* o = objects && !isFixed(id) ? objects->object(id) : nullptr;
        if (!o || !hero || o->asCreature())
        {
            return false;
        }
        const uint16_t type = *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(o) + 0x10);
        // A lever (LEVER01 0x17CD) too: used as a door is, it opens its own trigger, and the script then frees the
        // door it holds (Manolito, block K); one already pulled (its trigger open) is passed by.
        const bool lever = type == 0x17CD;
        if (!((type >= 0x1612 && type <= 0x1697) || type == 0x1465 || lever))
        {
            return false;
        }
        // Noted for the routes (MapMemory::noteDoor): opens or not, by its trigger's state below.
        const int doorLayer = *(reinterpret_cast<const uint8_t*>(hero) + 0x24);
        const int doorX = static_cast<int>(o->x / 53.66563), doorY = static_cast<int>(o->y / 53.66563);  // kTileSize, defined further on
        bool shutForGood = false;
        // Its state, in its trigger record (Manolito, block K, AGENT_ADDRESSES «Puertas y palancas»): door+0x34 the
        // trigger's index, the records [world+0x268] (end [world+0x26C]) 0x10 each, world = [[0xAD5C40]]; +0xA u16
        // bit 0 open, 0x8000 locked by a script or lever; +0xC u32 the key it asks (the game looks in the backpack).
        // Open ones and those a script holds shut are passed by.
        if (const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40))
        {
            if (const uintptr_t world = *reinterpret_cast<const uintptr_t*>(holder))
            {
                const uintptr_t begin = *reinterpret_cast<const uintptr_t*>(world + 0x268);
                const uintptr_t end = *reinterpret_cast<const uintptr_t*>(world + 0x26C);
                const uint32_t index = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(o) + 0x34);
                const uintptr_t trig = begin + static_cast<uintptr_t>(index) * 0x10;
                if (begin && end > begin && index < 0x100000 && trig + 0x10 <= end)
                {
                    const uint16_t state = *reinterpret_cast<const uint16_t*>(trig + 0xA);
                    const uint32_t key = *reinterpret_cast<const uint32_t*>(trig + 0xC);
                    // 0x4000 is no lock: «just switched», gone in a second (Manolito).
                    // A key asked counts as shut for the routes: the backpack may not hold it.
                    shutForGood = !(state & 1) && ((state & 0x8000) || key);
                    if (!lever)
                    {
                        MapMemory::noteDoor(doorLayer, doorX, doorY, !shutForGood);
                        MapMemory::doorState(doorLayer, doorX, doorY, (state & 1) != 0);
                    }
                    if ((state & 1) || (!lever && (state & 0x8000) && !key))
                    {
                        return false;
                    }
                }
            }
        }
        const auto it = g_doorTried.find(id);
        if (it != g_doorTried.end() && GetTickCount() - it->second < 120000)
        {
            // Tried and still shut a few seconds on: no way through for the routes either.
            if (!lever && GetTickCount() - it->second > 5000)
            {
                MapMemory::noteDoor(doorLayer, doorX, doorY, false);
            }
            return false;
        }
        const float dx = static_cast<float>(o->x - hero->x), dy = static_cast<float>(o->y - hero->y);
        return dx * dx + dy * dy <= g_doorRange * g_doorRange;
    }

    bool acceptLoot(uint32_t id, void*)
    {
        if (lootBlocked(id, GetTickCount()) || g_lootDone.count(lootKey(id)) || Gear::wasDropped(id))
        {
            return false;
        }
        if (isFixed(id))
        {
            int32_t x = 0, y = 0;
            return fixedPosition(id, x, y) && lootNear(x, y) && fixedUsable(id);
        }
        cObjectManager* objects = cObjectManager::instance();
        cObject* object = objects ? objects->object(id) : nullptr;
        if (object && !lootNear(object->x, object->y))
        {
            return false;
        }
        const Loot loot = object ? lootOf(object) : Loot::None;
        // A container already opened (object flags +0x14 & 0x4000, seen live 2026-11-09: 0x94000001 shut, 0x9400C001
        // open; also after a load): nothing in it any more.
        if (loot == Loot::Container && (*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) + 0x14) & 0x4000))
        {
            return false;
        }
        // Equipment below the grade asked for is left lying (the player's wish, 2026-11-09: no junk in the backpack);
        // set pieces as asked; potions, runes, gold and the rest always.
        // The grade filter only with gold enough (the player's wish, 2026-11-09): low grades are worth gold at a
        // merchant, and early on the basic gear is what the hero puts on. Enough: so much per hero level. The hero's
        // level: u16 at +0x3A8 + 0x56; the purse: u32 at +0x3A8 + 0x46 (Gear's kGold).
        const cCreature* hero = objects ? objects->hero() : nullptr;
        const uint8_t* heroBytes = reinterpret_cast<const uint8_t*>(hero);
        const int heroLevel = hero ? *reinterpret_cast<const uint16_t*>(heroBytes + 0x3A8 + 0x56) : 0;
        const uint32_t heroGold = hero ? *reinterpret_cast<const uint32_t*>(heroBytes + 0x3A8 + 0x46) : 0;
        const bool goldEnough = hero && static_cast<uint64_t>(heroGold) >=
                                            static_cast<uint64_t>(Config::autoAttack.rarityGoldPerLevel) * std::max(heroLevel, 1);
        const bool droppedGold = object && (*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) + 0x14) & 0x00100000);
        if (loot == Loot::Item && goldEnough && !droppedGold && isEquipment(object) && !Gear::heroWeapon(id) &&
            (Config::autoAttack.minRarity > 0 || !Config::autoAttack.keepSets))
        {
            const int grade = Gear::grade(id, true);
            const bool keep = grade < 0 || (grade == 4 ? Config::autoAttack.keepSets || Config::autoAttack.minRarity == 0
                                                       : grade >= Config::autoAttack.minRarity);
            if (!keep)
            {
                static std::unordered_set<uint32_t> s_told;
                if (s_told.size() > 512)
                {
                    s_told.clear();
                }
                if (s_told.insert(id).second)
                {
                    static const char* kNames[] = {"white", "blue", "yellow", "gold", "set"};
                    LOG("AutoAttack: item {:x} ({}) below the grade asked for, left lying ({} gold, level {})", id,
                        kNames[grade], heroGold, heroLevel);
                }
                return false;
            }
        }
        // The backpack full: items are left lying (none fits; seen live, 2026-11-09: each tried again and again on the
        // way to the merchant), but dropped gold (flags +0x14 & 0x00100000), which goes to the purse.
        if (loot == Loot::Item && Gear::packFull() &&
            !(*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) + 0x14) & 0x00100000))
        {
            // A piece worth the trouble lying about: Gear drops the worst it would sell anyway to take it (the player,
            // 2026-11-16: «se están dejando en el suelo muchos objetos útiles»).
            if (isEquipment(object))
            {
                Gear::wantRoomFor(id);
            }
            return false;
        }
        return loot == Loot::Item || loot == Loot::Container;
    }

    bool isCurrent(uint32_t id, void*)
    {
        return id == g_target;
    }

    bool questGoalNear(int32_t x, int32_t y, double tiles);     // a goal of the journal within that many tiles

    // Magic hiding places (VERSTECK) have no picture and are not in the pick list: the cursor finds them by the tile
    // under it, shows the hand and their name. Gone for by their record's tile, within LootRange / 40 tiles (about
    // the screen pixels LootRange stands for) on either axis.
    bool findHidingPlace(uint32_t& out)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        const size_t count = fixedCount();
        if (!hero || !count)
        {
            return false;
        }
        const double reach = Config::autoAttack.lootRange / 40.0 * kFixedTile;
        double best = 1e30;
        for (size_t i = 0; i < count; ++i)
        {
            const uint32_t id = kFixedId | static_cast<uint32_t>(i);
            const uint8_t* record = fixedRecord(id);
            // And a quest's spot to click (the quests study, 2026-11-23: the quest scripts put usable records in this
            // table, clicked like a hiding place: take402 at 2142,2928, take1002 and ding1002, take1202's healing herb,
            // take2301, postchange2201, ot_saeure5003, ot_wurzkraut (7615), ot_nimmt_flamme (53), We_ek_* (55); the hero
            // stood 6 min on 2142,2928 «with the journal not moving»). Only with a goal of the journal within 15 tiles:
            // clicked before the quest is taken it would do nothing and be marked done for good.
            const char* name = reinterpret_cast<const char*>(record + kFixedName);
            const bool questName = std::memcmp(name, "take", 4) == 0 || std::memcmp(name, "ding", 4) == 0 ||
                                   std::memcmp(name, "ot_", 3) == 0 || std::memcmp(name, "postchange", 10) == 0 ||
                                   std::memcmp(name, "We_ek_", 6) == 0;
            const bool questSpot = questName && *reinterpret_cast<const uint32_t*>(record + kFixedKind) == kFixedUsable;
            if (std::memcmp(record + kFixedName, "VERSTECK", 9) != 0 && !questSpot)
            {
                continue;
            }
            int32_t x = 0, y = 0;
            fixedPosition(id, x, y);
            if (questSpot && !questGoalNear(x, y, 15.0))
            {
                continue;
            }
            if (questSpot)
            {
                static uint32_t s_told = 0;
                if (s_told != id)
                {
                    s_told = id;
                    LOG("AutoAttack: quest spot {} at tile {},{}: to be clicked", name, static_cast<int>(x / kFixedTile),
                        static_cast<int>(y / kFixedTile));
                }
            }
            const double dx = x - hero->x, dy = y - hero->y;
            if (std::abs(dx) > reach || std::abs(dy) > reach || dx * dx + dy * dy >= best || !lootNear(x, y) ||
                lootBlocked(id, GetTickCount()) || g_lootDone.count(lootKey(id)))
            {
                continue;
            }
            best = dx * dx + dy * dy;
            out = id;
        }
        return best < 1e30;
    }

    // The loot on the agent's radar (what the collect goes for, done ones left out): items and containers in the
    // world pick (the screen and a margin around), the usable fixed things (hiding places, wells, gold) within 60
    // tiles. Between beginRadar and endRadar.
    bool radarPick(uint32_t id, void*)
    {
        if (g_lootDone.count(lootKey(id)) || isFixed(id))
        {
            return false;
        }
        cObjectManager* objects = cObjectManager::instance();
        cObject* object = objects ? objects->object(id) : nullptr;
        const Loot loot = object ? lootOf(object) : Loot::None;
        if (loot == Loot::Item || loot == Loot::Container)
        {
            MapMemory::addBlip(loot == Loot::Item ? MapMemory::Blip::Item : MapMemory::Blip::Chest, object->x, object->y);
        }
        return false;   // never chosen: only seen
    }

    void radarLoot()
    {
        AimAssist::Target unused;
        AimAssist::findObject(4000.0f, &radarPick, nullptr, unused);
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        const size_t count = fixedCount();
        const double reach = 60 * kFixedTile;
        for (size_t i = 0; hero && i < count; ++i)
        {
            const uint32_t id = kFixedId | static_cast<uint32_t>(i);
            const uint8_t* record = fixedRecord(id);
            int32_t x = 0, y = 0;
            if (!record || *reinterpret_cast<const uint32_t*>(record + kFixedKind) != kFixedUsable ||
                !fixedPosition(id, x, y) || std::abs(x - hero->x) > reach || std::abs(y - hero->y) > reach ||
                g_lootDone.count(lootKey(id)))
            {
                continue;
            }
            MapMemory::addBlip(MapMemory::Blip::Hiding, x, y);
        }
    }

    // The nearest loot: on the screen (items, containers, wells) or a hiding place.
    bool findLoot(uint32_t& out)
    {
        AimAssist::Target t;
        if (AimAssist::findObject(static_cast<float>(Config::autoAttack.lootRange), &acceptLoot, nullptr, t))
        {
            out = t.id;
            return true;
        }
        return findHidingPlace(out);
    }

    // Whether the hero is done with the loot it goes for: it gives up after a while, or after standing at it (an
    // opened container stays, and so does an item when the inventory is full).
    int32_t g_fixedX = 0, g_fixedY = 0;  // where the fixed thing gone for stands (world), see attack

    bool lootDone(uint32_t id, DWORD now)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        cObject* loot = objects && !isFixed(id) ? objects->object(id) : nullptr;
        if (!hero || (!loot && !isFixed(id)))
        {
            return true;
        }
        // A fixed thing's table shifts when the game removes one of its entries (a used stone): the id then names
        // another record (the review of the findings, 2026-11-09: «not reached» at 111 to 4366 tiles, F_Stein_0011
        // e8 -> e7 in 22 s). Its place read again: moved off, it is left at once, and nothing is marked for it.
        if (!loot)
        {
            int32_t fx = 0, fy = 0;
            if (!fixedPosition(id, fx, fy) || std::abs(fx - g_fixedX) > 3 * 53.66563f || std::abs(fy - g_fixedY) > 3 * 53.66563f)
            {
                LOG("AutoAttack: fixed thing {:x} is another one now (its table shifted), left", id);
                g_lootStale = true;
                return true;
            }
        }
        // Any dialog open (a quest talk on the way, a stone's text): the loot's clocks stand still (the review of the
        // findings: «not reached» after 12 s of a quest talk, the hero standing).
        if (UiNav::npcDialogOpen())
        {
            g_lootBestAt = now;
            if (g_lootAtSince)
            {
                g_lootAtSince = now;
            }
            return false;
        }
                const int32_t lx = loot ? loot->x : g_fixedX, ly = loot ? loot->y : g_fixedY;
        const float dx = static_cast<float>(lx - hero->x), dy = static_cast<float>(ly - hero->y);
        const float distance = std::sqrt(dx * dx + dy * dy);
        // Progress: half a tile nearer than ever before.
        if (!g_lootBestAt || distance < g_lootBest - 0.5f * 53.66563f)
        {
            g_lootBest = distance;
            g_lootBestAt = now;
        }
        if (distance > kLootAtDistance)
        {
            g_lootAtSince = 0;
            if (static_cast<int>(now - g_lootBestAt) > static_cast<int>(kLootStuckMs))
            {
                LOG("AutoAttack: loot {:x} not reached, left", id);
            Findings::note("loot", hero->x, hero->y, "loot {:x} not reached ({:.1f} tiles left)", id, distance / 53.66563f);
                return true;
            }
            return false;
        }
        if (!g_lootAtSince)
        {
            g_lootAtSince = now;
        }
        // A container the hero opened (flags +0x14 & 0x4000): done once its lid is up (a moment for the spill), its
        // contents on the ground for the next collect.
        if (loot && lootOf(loot) == Loot::Container &&
            (*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(loot) + 0x14) & 0x4000) &&
            now - g_lootAtSince > 800)
        {
            LOG("AutoAttack: container {:x} opened", id);
            return true;
        }
        // A well stays where it is once used (it heals, or nothing with full health): done once the hero stood at it
        // after the use order (seen live, 2026-11-09: the abbey's well «still there» again and again).
        if (!loot && static_cast<int>(now - g_lootAtSince) > 1500 && static_cast<int>(g_sentAt - g_lootAtSince) >= 0)
        {
            const uint8_t* record = fixedRecord(id);
            if (record && std::memcmp(record + kFixedName, "BRUNNEN", 7) == 0)
            {
                LOG("AutoAttack: well {:x} used", id);
                return true;
            }
            // Any other fixed object (ids 8000xxxx: levers, shrines, usable things) stays too once used; not loot left
            // behind (the findings verifier, 2026-11-12: 3191,2773, 3279,2786 and 3504,2478 counted as «still there»).
            if (id & kFixedId)
            {
                LOG("AutoAttack: fixed object {:x} used", id);
                return true;
            }
        }
        if (static_cast<int>(now - g_lootAtSince) > static_cast<int>(kLootAtMs))
        {
            LOG("AutoAttack: loot {:x} still there with the hero at it, again in {} s", id, kLootSoonMs / 1000);
            Findings::note("loot", hero->x, hero->y, "loot {:x} still there with the hero at it ({:.1f} tiles)", id,
                           distance / 53.66563f);
            g_lootStill = true;
            return true;
        }
        return false;
    }

    // The game's path finders search 64x64 tiles around the walker (ClickWalk): loot further out on a tile axis
    // (a well across a river, 40 tiles up a 32:9 screen) is walked to first, with a walk order, which ClickWalk
    // routes in legs; once within reach, the next order (lootDone's nudge when the hero stops) uses it.
    constexpr double kTileSize = 53.66563;
    constexpr int32_t kUseReach = static_cast<int32_t>(24 * kTileSize);

    // How far the hero walks from one point to another, in world units (the player, 2026-11-11: «que paren de medir
    // cercanía con la distancia en línea recta, … la distancia de la ruta entera»): the route's length over what the
    // map knows (roads, doors that open, walls and doors held shut), once worked out on its own thread; until then, or
    // with no route (too far apart for one search), the straight line.
    double wayLength(int32_t fromX, int32_t fromY, int32_t toX, int32_t toY)
    {
        const double straight = std::hypot(static_cast<double>(toX - fromX), static_cast<double>(toY - fromY));
        cObjectManager* objects = cObjectManager::instance();
        const cCreature* hero = objects ? objects->hero() : nullptr;
        const int layer = hero ? *(reinterpret_cast<const uint8_t*>(hero) + 0x24) : 0;
        const float tiles = MapMemory::routeTiles(layer, static_cast<int>(fromX / kTileSize),
                                                  static_cast<int>(fromY / kTileSize), static_cast<int>(toX / kTileSize),
                                                  static_cast<int>(toY / kTileSize));
        return tiles >= 0.0f ? std::max(straight, tiles * kTileSize) : straight;
    }

    int32_t g_walkX = 0, g_walkY = 0;
    DWORD g_roamAt = 0;     // the last roaming step (0: not roaming)

    // On the window's thread, as the player's clicks (HeroMove).
    void walkThere(void*)
    {
        cEngine* engine = FrameHooks::engine();
        cObjectManager* objects = cObjectManager::instance();
        cCreature* self = engine && objects ? objects->creature(engine->controlled) : nullptr;
        // Riding, to the hero all the same: his handler passes a move on to the horse, which swallows direct orders
        // (Manolito, phase 2, 2026-11-12: 0x52E590; the horse with a rider, +0x200 & 4, takes none).
        if (cCreature* hero = objects ? objects->hero() : nullptr;
            hero && *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x1EC))
        {
            self = hero;
        }
        if (!self)
        {
            return;
        }
        cOrder order;
        order.type = cOrder::move;
        order.mode = cOrder::walk;
        order.x = g_walkX;
        order.y = g_walkY;
        order.layer = reinterpret_cast<const uint8_t*>(self)[0x24];     // the walker's layer (Manolito, block AF)
        // The path-finding walk to the spot a click gives (follow 0). follow 1 is hold-to-walk: it heads for the
        // cursor and ends within a tenth of a second unless the left button is held (seen live: walking, then 2,
        // then standing, not a pixel moved).
        order.follow = 0;
        engine->sendOrder(self, order);
    }

    // The agent's walk order, once the game's cursor is on the spot (AgentCursor; at once with the option off).
    void fireWalk(void*)
    {
        Inject::engineCallOrdered(&walkThere, nullptr);
    }
    void sendWalk()
    {
        AgentCursor::act({0, g_walkX, g_walkY}, &fireWalk, nullptr);
    }

    // True if `self` is too far from (x, y) for the use order: a walk order went out instead.
    bool walkFirst(cCreature* self, int32_t x, int32_t y, int32_t reach = kUseReach)
    {
        if (std::abs(x - self->x) <= reach && std::abs(y - self->y) <= reach)
        {
            return false;
        }
        // A spot far off the loot range is a stale position (a fixed thing's table shifts when the game removes one
        // of its entries): no walk across the world for it; the stalled pick up leaves it.
        if (std::abs(x - self->x) > 60 * kTileSize || std::abs(y - self->y) > 60 * kTileSize)
        {
            return true;
        }
        // Once per destination: the walk order goes out again at each nudge (about every 1.2 s) of a long walk.
        static int32_t loggedX = 0, loggedY = 0;
        if (x != loggedX || y != loggedY)
        {
            loggedX = x;
            loggedY = y;
            LOG("AutoAttack: loot at {},{} is far ({:.0f},{:.0f} tiles), walking there first", x, y,
                (x - self->x) / kTileSize, (y - self->y) / kTileSize);
        }
        g_walkX = x;
        g_walkY = y;
        sendWalk();
        return true;
    }

    // The A key's «collect» (Manolito's block U3, 2026-11-10; the player: «al apretar A el personaje recogía sin salir
    // del caballo»): a cEvent 0x113 with the player's id at +0xC to the hero's receiveEvent puts it in its pick up mode
    // (+0xFC = 0xC), which walks to the nearest loot and takes it, mounted or not.
    void sendCollect(void*)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        const uint8_t* player = *reinterpret_cast<const uint8_t* const*>(0x182EBE8);
        if (!hero || !player)
        {
            return;
        }
        alignas(8) uint8_t ev[0x44] = {};
        *reinterpret_cast<uintptr_t*>(ev) = 0x89095C;
        *reinterpret_cast<uint32_t*>(ev + 4) = 0x113;
        *reinterpret_cast<uint32_t*>(ev + 0xC) = *reinterpret_cast<const uint32_t*>(player + 0x14);
        using Handle = void(__fastcall*)(void* self, void*, void* ev);
        const auto* vt = *reinterpret_cast<const uintptr_t* const*>(hero);
        reinterpret_cast<Handle>(vt[6])(hero, nullptr, ev);
    }

    // A door (DOOR_* 0x1612..0x1697, S_DOOR 0x1465) or a lever (0x17CD): the objects a click uses through a trigger.
    bool isDoorObject(const cObject* o)
    {
        if (!o)
        {
            return false;
        }
        const uint16_t type = *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(o) + 0x10);
        return (type >= 0x1612 && type <= 0x1697) || type == 0x1465 || type == 0x17CD;
    }
    // The door last clicked: 4 s before it may be clicked again, its state told once 2.5 s after the click.
    struct DoorUse
    {
        uint32_t id = 0;
        DWORD at = 0;
        bool told = true;
        double tiles = -1.0;    // the hero's distance to the door (Chebyshev, tiles) when the click went out
    } g_doorUse;
    // The door the hero is walking up to for a click: attack() is called again from doorPendingTick every second, 25 s at most.
    struct DoorPending
    {
        uint32_t id = 0;
        DWORD since = 0, askedAt = 0;
    } g_doorPending;
    // The door's trigger record (AGENT_ADDRESSES «Puertas y palancas»): +0xA bit 0 open, 0x8000 locked by a script or lever,
    // +0xC the key it asks. False when the record cannot be read.
    bool doorTrigger(const cObject* o, uint16_t& state, uint32_t& key)
    {
        if (const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40))
        {
            if (const uintptr_t world = *reinterpret_cast<const uintptr_t*>(holder))
            {
                const uintptr_t begin = *reinterpret_cast<const uintptr_t*>(world + 0x268);
                const uintptr_t end = *reinterpret_cast<const uintptr_t*>(world + 0x26C);
                const uint32_t index = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(o) + 0x34);
                const uintptr_t trig = begin + static_cast<uintptr_t>(index) * 0x10;
                if (begin && end > begin && index < 0x100000 && trig + 0x10 <= end)
                {
                    state = *reinterpret_cast<const uint16_t*>(trig + 0xA);
                    key = *reinterpret_cast<const uint32_t*>(trig + 0xC);
                    return true;
                }
            }
        }
        return false;
    }
    void doorUseCheck(DWORD now)
    {
        if (!g_doorUse.id || g_doorUse.told || now - g_doorUse.at < 2500)
        {
            return;
        }
        g_doorUse.told = true;
        cObjectManager* objects = cObjectManager::instance();
        const cObject* o = objects ? objects->object(g_doorUse.id) : nullptr;
        uint16_t state = 0;
        uint32_t key = 0;
        if (o && !o->x && !o->y)
        {
            LOG("AutoAttack: door {:x} clicked {:.1f} s ago from {:.1f} tiles: no longer loaded (its position reads 0,0): no state",
                g_doorUse.id, (now - g_doorUse.at) / 1000.0, g_doorUse.tiles);
        }
        else if (o && doorTrigger(o, state, key))
        {
            const cCreature* hero = objects ? objects->hero() : nullptr;
            const double nowTiles = hero ? std::max(std::abs(static_cast<double>(o->x - hero->x)),
                                                    std::abs(static_cast<double>(o->y - hero->y))) / 53.66563
                                         : -1.0;
            LOG("AutoAttack: door {:x} clicked {:.1f} s ago from {:.1f} tiles (hero now {:.1f}): now {} (trigger state {:x}, key {:x}, "
                "at {},{})", g_doorUse.id, (now - g_doorUse.at) / 1000.0, g_doorUse.tiles, nowTiles,
                (state & 1) ? "OPEN" : "still shut", state, key, o->x / 53, o->y / 53);
        }
    }

    // Orders the creature the mouse commands (the hero, or its mount) to attack, pick up or open `id`, as a click
    // on it does.
    bool attack(uint32_t id);
    bool g_cursorFiring = false;    // attack() called back by AgentCursor, the cursor on the target
    void fireAttack(void* id)
    {
        g_cursorFiring = true;
        attack(static_cast<uint32_t>(reinterpret_cast<uintptr_t>(id)));
        g_cursorFiring = false;
    }
    // The use order (a left click on `id`), once the game's cursor is on it; at once with the option off.
    bool clickOn(cCreature* self, UseOrder& order)
    {
        if (!g_cursorFiring && AgentCursor::active())
        {
            AgentCursor::act({order.target, order.x, order.y}, &fireAttack,
                             reinterpret_cast<void*>(static_cast<uintptr_t>(order.target)));
            return true;
        }
        const auto handler = reinterpret_cast<const OrderHandler*>(self->vtable)[6];
        handler(self, nullptr, &order);
        return true;
    }

    bool attack(uint32_t id)
    {
        cEngine* engine = FrameHooks::engine();
        cObjectManager* objects = cObjectManager::instance();
        if (!engine || !objects)
        {
            return false;
        }
        cCreature* self = objects->creature(engine->controlled);
        cCreature* rider = objects->hero();
        // Riding: the hero's own mount field (Manolito AD/AG), not «controlled is not the hero» (half off counts so too).
        const bool riding = rider && *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(rider) + 0x1EC) != 0;
        if (self && isFixed(id))
        {
            // As a click on it: the order 7 with its id and where it stands. Read first: lootDone checks the id
            // against this place, also while the hero gets off the horse (else it reads as a shifted table, the
            // thing is left and found again at once: 1800 times in 90 s, A5 2026-11-12).
            int32_t x = 0, y = 0;
            if (!fixedPosition(id, x, y))
            {
                return false;
            }
            // A well, a hiding place: used on foot (the horse uses nothing; the reviewer, 2026-11-12).
            if (riding)
            {
                g_fixedX = x;
                g_fixedY = y;
                AutoAttack::footFor(15000);
                return true;
            }
            if (rider)
            {
                self = rider;
            }
            // Beyond the loot range: a stale id (its table shifted), not a thing to walk to.
            if (std::abs(x - self->x) > 60 * kTileSize || std::abs(y - self->y) > 60 * kTileSize)
            {
                LOG("AutoAttack: fixed thing {:x} reads {:.0f} tiles off: a stale id, not gone for", id,
                    std::max(std::abs(x - self->x), std::abs(y - self->y)) / kTileSize);
                return false;
            }
            g_fixedX = x;
            g_fixedY = y;
            if (walkFirst(self, x, y))
            {
                return true;
            }
            UseOrder order;
            order.target = id;
            order.x = x;
            order.y = y;
            return clickOn(self, order);
        }
        cObject* target = objects->object(id);
        if (!self || !target)
        {
            return false;
        }
        // Mounted, a click on a creature goes to the rider, not the mount (seen in the orders the world mouse
        // handler gives): the horse would only walk up to it.
        if (rider && rider != self && target->asCreature())
        {
            self = rider;
        }
        // Mounted, loot on the ground is taken as the A key takes it, without getting off (once a second at most);
        // a door, a chest or anything else is used on foot (the reviewer: the A key opens none of them).
        else if (riding && !target->asCreature() && lootOf(target) != Loot::Item)
        {
            AutoAttack::footFor(15000);
            return true;
        }
        else if (riding && !target->asCreature())
        {
            static DWORD s_collectAt = 0;
            const DWORD now = GetTickCount();
            if (now - s_collectAt > 1000)
            {
                s_collectAt = now;
                LOG("AutoAttack: mounted: collecting {:x} as the A key does", id);
                Inject::engineCallOrdered(&sendCollect, nullptr);
            }
            return true;
        }
        // A door is clicked only from beside it, the hero walked up first (3 tiles: the use point lies a step before or behind
        // it; the stuck solver, 2026-11-17: 6 clicks in 20 min from 10-38 tiles off, one door opened): the walk goes on
        // from doorPendingTick until the click can go out.
        if (!target->asCreature() && isDoorObject(target))
        {
            if (walkFirst(self, target->x, target->y, static_cast<int32_t>(3.0 * kTileSize)))
            {
                if (g_doorPending.id != id)
                {
                    g_doorPending = {id, GetTickCount(), 0};
                }
                return true;
            }
        }
        else if (!target->asCreature() && walkFirst(self, target->x, target->y))
        {
            return true;
        }
        // A door is used once, from the use point the game walks the hero to (Manolito, block BU, 2026-11-17: the use
        // alternates, and 1 s after a change the trigger holds 0x4000 and refuses another, so a second click inside that
        // second or just after it shuts the door again; A4's ed1, 1950,3270, was «used» again and again and never read open):
        // the same door is not clicked again for 4 s, and its state is told 2.5 s after the click.
        if (!target->asCreature() && isDoorObject(target))
        {
            const DWORD now = GetTickCount();
            if (g_doorUse.id == id && now - g_doorUse.at < 4000)
            {
                return true;
            }
            // Noted only when the order goes out: through the game's cursor (AgentCursor) this first call only moves the cursor
            // onto the door and the click comes in a second call (g_cursorFiring); noted here at the first, the second was taken
            // for a repeat and no order was ever sent (the stuck solver, 2026-11-17, A7: «clicked 2.5 s ago: still shut» on
            // every door after the 17:55 install, the hero's order never in mode 1 in a 0.1 s watch of its order fields).
            if (g_cursorFiring || !AgentCursor::active())
            {
                g_doorUse = {id, now, false,
                             std::max(std::abs(static_cast<double>(target->x - self->x)),
                                      std::abs(static_cast<double>(target->y - self->y))) / kTileSize};
            }
        }
        UseOrder order;
        order.target = id;
        order.x = target->x;
        order.y = target->y;
        return clickOn(self, order);
    }

    // The walk up to a door goes on (attack() sent it as a walk order, once): asked again every second until the click goes out
    // or 25 s pass.
    void doorPendingTick(DWORD now)
    {
        DoorPending& p = g_doorPending;
        if (!p.id)
        {
            return;
        }
        if (now - p.since > 25000 || (g_doorUse.id == p.id && g_doorUse.at >= p.since))
        {
            p = DoorPending{};
            return;
        }
        if (now - p.askedAt < 1000)
        {
            return;
        }
        p.askedAt = now;
        g_doorHoldUntil = now + 1500;
        if (!attack(p.id))
        {
            p = DoorPending{};
        }
    }

    // Natural pace: a look at the situation every so often, a moment before acting on a new aim, orders repeated at
    // slightly uneven intervals.
    constexpr DWORD kThinkMinMs = 180, kThinkMaxMs = 340;
    constexpr DWORD kIdleThinkMinMs = 100, kIdleThinkMaxMs = 180;   // no enemy aimed at: a new one is seen sooner
    constexpr DWORD kReactMinMs = 220, kReactMaxMs = 480;
    constexpr DWORD kReactUrgentMinMs = 90, kReactUrgentMaxMs = 220;
    // Hurt this recently: the hero is under attack.
    constexpr DWORD kHurtMs = 4000;
    constexpr int kMaxFoes = 64;
    // Enemies attacking the hero are fought this far away (times Range): archers and casters shoot from afar.
    constexpr float kEngagedReach = 4.0f;

    DWORD g_thinkAt = 0;            // the next look at the situation
    uint32_t g_pending = 0;         // the new aim not acted on yet, 0 for none
    DWORD g_actAt = 0;              // ... acted on from this tick
    int g_repeatMs = 1000;          // this target's repeat interval: Repeat with some spread
    int g_lastHealth = 0;
    DWORD g_hurtAt = 0;             // when the hero last lost health, 0 for never
    std::unordered_map<uint32_t, float> g_lastDistance;   // each enemy's distance at the last look, pixels

    DWORD jitter(DWORD lo, DWORD hi)
    {
        static uint32_t state = GetTickCount() | 1;
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        return lo + state % (hi - lo + 1);
    }

    // A creature's aim (seen live, 2026-11-07): attacking, +0x104 holds its target's id and +0x108/+0x10C where the
    // target stands; walking or idle, +0x104/+0x108 hold the point it goes to (world coordinates, far above any id).
    // The id counts only when the position after it is its object's, give or take its last steps.
    constexpr size_t kAimId = 0x104, kAimX = 0x108, kAimY = 0x10C;
    constexpr int32_t kAimSlack = 400;     // world units, about 7 tiles

    // Hostile creatures near the hero on the surface (40 tiles), from the world pass each second: the explorer keeps
    // clear of those not after it yet (Manolito, block N: a creature fixes on the hero within 600 u, 11.2 tiles, and
    // a pack (+0x24D its leader) comes as one; gives up beyond 1500 u, 27.9 tiles).
    struct AggroFoe
    {
        uint32_t id;
        int32_t x, y;
        bool onHero;    // +0x251 the hero, +0x1F4 bit 4 (an enemy fixed), not a summon's master (bit 0x100)
    };
    std::vector<AggroFoe> g_aggroFoes;
    std::atomic<DWORD> g_attackAt{0};    // the last attack order (read by Gear on its own thread)
    int32_t g_aggroHeroX = 0, g_aggroHeroY = 0;    // where the hero stood when g_aggroFoes was read
    constexpr double kAggroTiles = 13.0;

    // A creature with aggro on the hero (Manolito, block N): its AI target +0x251 the hero (or what it rides), an enemy
    // fixed (+0x1F4 bit 4), and no master (bit 0x100: then +0x251 is the master). Set from 11.2 tiles on, before the
    // first blow; dropped beyond 28 tiles (the pursuit's end). The player, 2026-11-10: «saber cuando un enemigo le
    // tiene aggro, para saber a quién atacar o de quién huir».
    bool aggroOnHero(const cObject* creature, uint32_t heroId, uint32_t selfId)
    {
        if (!creature)
        {
            return false;
        }
        const auto* base = reinterpret_cast<const uint8_t*>(creature);
        const int32_t target = *reinterpret_cast<const int32_t*>(base + 0x251);
        const uint32_t ai = *reinterpret_cast<const uint32_t*>(base + 0x1F4);
        return target > 0 && (ai & 4) && !(ai & 0x100) &&
               (static_cast<uint32_t>(target) == heroId || static_cast<uint32_t>(target) == selfId);
    }

    uint32_t aimOf(cObjectManager* objects, cObject* creature)
    {
        const auto* base = reinterpret_cast<const uint8_t*>(creature);
        const uint32_t id = *reinterpret_cast<const uint32_t*>(base + kAimId);
        cObject* target = id && id != creature->id ? objects->object(id) : nullptr;
        if (!target)
        {
            return 0;
        }
        const int32_t x = *reinterpret_cast<const int32_t*>(base + kAimX);
        const int32_t y = *reinterpret_cast<const int32_t*>(base + kAimY);
        return std::abs(x - target->x) <= kAimSlack && std::abs(y - target->y) <= kAimSlack ? id : 0;
    }

    // Enemies the player attacked themself (the hero's aim after a click of theirs): fought to the end.
    std::unordered_set<uint32_t> g_playerTargets;

    // After a click of the player's: the enemy they set the hero on is theirs to the end. Dead or gone ones are
    // dropped.
    void notePlayerTarget()
    {
        cObjectManager* objects = cObjectManager::instance();
        cEngine* engine = FrameHooks::engine();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!objects || !engine || !hero)
        {
            return;
        }
        cObject* controlled = objects->object(engine->controlled);
        const uint32_t aim = controlled ? aimOf(objects, controlled) : 0;
        cCreature* foe = aim ? objects->creature(aim) : nullptr;
        if (foe && foe->health > 0 && hero->isEnemy(foe) && g_playerTargets.insert(aim).second)
        {
            LOG("AutoAttack: the player attacks {:x}", aim);
        }
        for (auto it = g_playerTargets.begin(); it != g_playerTargets.end();)
        {
            cCreature* c = objects->creature(*it);
            it = c && c->health > 0 ? std::next(it) : g_playerTargets.erase(it);
        }
    }

    struct Choice
    {
        uint32_t id = 0;
        bool urgent = false;    // under threat: acted on sooner
    };

    // --- Who follows the hero: hirelings ---------------------------------------------------------------------------

    // A creature that is no enemy, stays about the hero for a while and kept up while the hero went some way: a
    // hireling (people in town and animals stay where they are; the horse waits where the hero got off).
    struct Follower
    {
        DWORD since = 0, seenAt = 0;
        int32_t heroX = 0, heroY = 0;   // where the hero stood when it was first seen
        int32_t ownX = 0, ownY = 0;     // ... and where it stood itself (townsfolk stay, hirelings go along)
        bool follows = false;
    };
    std::unordered_map<uint32_t, Follower> g_followers;
    std::vector<uint32_t> g_hirelings;
    constexpr DWORD kFollowMs = 15000;
    constexpr int32_t kFollowWay = static_cast<int32_t>(6 * kTileSize);

    void noteHirelings(DWORD now, const cCreature* hero, float range)
    {
        AimAssist::Foe friends[32];
        const int n = AimAssist::friends(range, friends, 32);
        cObjectManager* objects = cObjectManager::instance();
        for (int i = 0; i < n; ++i)
        {
            const cObject* o = objects ? objects->object(friends[i].id) : nullptr;
            if (!o)
            {
                continue;
            }
            Follower& f = g_followers[friends[i].id];
            if (!f.since || now - f.seenAt > 10000)
            {
                const bool follows = f.follows;
                f = Follower{now, now, hero->x, hero->y, o->x, o->y, follows};
            }
            f.seenAt = now;
            // The hero went a way, and it went the same way along (townsfolk and guards walk their own ways).
            const int64_t hdx = static_cast<int64_t>(hero->x) - f.heroX, hdy = static_cast<int64_t>(hero->y) - f.heroY;
            const int64_t odx = static_cast<int64_t>(o->x) - f.ownX, ody = static_cast<int64_t>(o->y) - f.ownY;
            const bool heroWent = std::abs(hdx) > kFollowWay || std::abs(hdy) > kFollowWay;
            const bool alongWith = std::abs(odx - hdx) < kFollowWay * 2 / 3 && std::abs(ody - hdy) < kFollowWay * 2 / 3;
            if (!f.follows && now - f.since > kFollowMs && heroWent && alongWith)
            {
                f.follows = true;
                LOG("AutoAttack: {:x} follows the hero: a hireling", friends[i].id);
            }
        }
        // The game's own list of companions (Manolito, AGENT_ADDRESSES «Mercenarios y acompañantes»): a std::vector
        // of 9-byte records at hero+0x39C..+0x3A0, +0 the creature's id, +8 non-zero for a hired mercenary (0: one
        // the script makes follow, e.g. an escorted man). Known at once, without waiting to see it follow.
        // When the list reads well (an empty one too), it alone says who the companions are: the guess from who walks
        // along took Julius, the arena master, for one (seen live, 2026-11-09).
        {
            const auto* heroBytes = reinterpret_cast<const uint8_t*>(hero);
            const auto begin = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x39C);
            const auto end = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x3A0);
            const bool listKnown = (!begin && !end) ||
                                   (begin && end >= begin && !((end - begin) % 9) && (end - begin) / 9 <= 8);
            if (listKnown)
            {
                std::vector<uint32_t> listed;
                for (const uint8_t* r = begin; r && r < end; r += 9)
                {
                    const uint32_t id = *reinterpret_cast<const uint32_t*>(r);
                    const cCreature* c = objects ? objects->creature(id) : nullptr;
                    if (!c || c->health <= 0)
                    {
                        // A companion lost (the player, 2026-11-11: A4 let a mercenary die): told once.
                        static std::unordered_set<uint32_t> s_lost;
                        if (c && std::find(g_hirelings.begin(), g_hirelings.end(), id) != g_hirelings.end() && s_lost.insert(id).second)
                        {
                            LOG("AutoAttack: companion {:x} died ({} of {} health)", id, c->health, c->maxHealth);
                        }
                        continue;
                    }
                    listed.push_back(id);
                    static std::unordered_set<uint32_t> s_told;
                    if (s_told.insert(id).second)
                    {
                        LOG("AutoAttack: {:x} is in the hero's companions ({}): looked after", id,
                            r[8] ? "a hired mercenary" : "following by script");
                    }
                }
                g_hirelings = std::move(listed);
                return;
            }
        }
        g_hirelings.clear();
        for (auto it = g_followers.begin(); it != g_followers.end();)
        {
            if (now - it->second.seenAt > 30000)
            {
                it = g_followers.erase(it);
                continue;
            }
            if (it->second.follows)
            {
                g_hirelings.push_back(it->first);
            }
            ++it;
        }
    }

    bool isHireling(uint32_t id)
    {
        return std::find(g_hirelings.begin(), g_hirelings.end(), id) != g_hirelings.end();
    }

    // A creature under a quest sign of the dialog table (the icon's last digit 0, «!» to take a quest, or 1, «?» to report;
    // the same test scanQuestMarks makes).
    bool questSigned(const cObject* o)
    {
        if (!o)
        {
            return false;
        }
        const auto dialogs = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x755C);
        const auto dialogsEnd = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7560);
        const uint32_t dialog = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(o) + 0x245);
        if (!dialogs || dialogsEnd <= dialogs || !dialog || dialog >= static_cast<size_t>(dialogsEnd - dialogs) / 0x50)
        {
            return false;
        }
        const uint32_t icon = *reinterpret_cast<const uint32_t*>(dialogs + dialog * 0x50 + 0x48);
        return icon < 20 && (icon % 10 == 0 || icon % 10 == 1);
    }

    // A follower that is no plain hireling: with a quest sign it is spoken to, whatever the hero's companions list or the guess
    // from its steps say (the stuck solver, 2026-11-17, A8: f3d, the farmer's daughter of «Hábitos negros» (quest 1101, type
    // 0x291), rescued and following, a «?» over her and the journal's creature to report to, was in the list with +8 = 1
    // and «a hireling» for the talk: «not spoken to … hireling true», the quest never done).
    bool isPlainHireling(uint32_t id)
    {
        if (!isHireling(id))
        {
            return false;
        }
        cObjectManager* om = cObjectManager::instance();
        return !questSigned(om ? om->object(id) : nullptr);
    }

    // --- The target: kept, given up when out of reach ---------------------------------------------------------------

    DWORD g_targetSince = 0;        // when the current target was taken
    float g_targetBest = 0.0f;      // its nearest distance since, pixels (0: none yet)
    DWORD g_targetBestAt = 0;       // ... reached then
    DWORD g_lastLookAt = 0;         // the last look at the situation
    DWORD g_retreatStartAt = 0;     // when the retreat began
    bool g_retreatDoomed = false;   // the retreat is from a hopeless fight (not for health or potions)
    int g_retreatExtended = 0;      // times the retreat went on with little health and no potion
    std::unordered_map<uint32_t, DWORD> g_unreachable;      // enemies given up on, until then
    std::unordered_map<uint32_t, float> g_unreachableAt;    // ... and how far they were then (pixels)
    std::unordered_map<uint32_t, int> g_unreachableTimes;   // ... how many times so far (the wait grows each time)
    std::unordered_map<uint32_t, int> g_farAimLooks;        // looks in a row an enemy aimed at the hero from afar
    uint32_t g_lastShooter = 0;                             // the last one taken for the shooter (logged once)
    int g_unseenHits = 0;                                   // hits in a row with no enemy to answer
    DWORD g_meleeAt = 0;                                    // the last look with an enemy in the melee
    DWORD g_unseenHitAt = 0;
    int32_t g_unseenSpotX = 0, g_unseenSpotY = 0;   // where the hero last walked off such hits ...
    DWORD g_unseenSpotAt = 0;                       // ... and when
    std::unordered_map<uint32_t, std::pair<int32_t, int32_t>> g_lastWorld;   // each enemy's world position, last look
    constexpr DWORD kStuckMs = 4000;        // no nearer to the target in this long, not fighting: out of reach
    constexpr DWORD kUnreachableMs = 20000;

    DWORD g_lastTargetAt = 0;       // the last enemy taken for target
    DWORD g_keptDistanceAt = 0;     // the last step back from an enemy (a ranged weapon's): no «out of reach» then
    DWORD g_lastHurtAt = 0;         // the target's health last went down (a blow that told)
    DWORD g_lootCount = 0;          // loot taken for good, counted (AgentStuck: progress)
    void targetTaken(DWORD now, uint32_t id)
    {
        // The same one taken again moments after a dodge or a look away (the player, 2026-11-11: the Vampiress after
        // archers across a river, «target 5d4» every 2 s between the dodges): the time without getting nearer goes on.
        static uint32_t s_lastId = 0;
        const bool again = id == s_lastId && g_lastTargetAt && now - g_lastTargetAt < 6000;
        s_lastId = id;
        g_lastTargetAt = now;
        if (again)
        {
            return;
        }
        g_targetSince = now;
        g_targetBest = 0.0f;
        g_targetBestAt = now;
    }

    // --- Stepping back -------------------------------------------------------------------------------------------

    DWORD g_retreatUntil = 0;       // stepping back until then at the latest (0: not stepping back)
    // No fights lost (docs/No-entrar-en-peleas-perdidas.md, [AutoAttack] NoLostFights): no fight of its choosing that
    // the class's own record says goes bad (5 %, 3 % with no healing potion: about 70 % / 82 % to win by the prior);
    // after leaving one as going bad, none sought for 20 s.
    DWORD g_noSeekUntil = 0;        // no fight sought until then (0: none barred)
    DWORD g_entryShutAt = 0;        // since when the forecast bars a fight of its choosing (0: open)
    bool entryOpen(DWORD now)
    {
        if (!Config::autoAttack.noLostFights)
        {
            return true;
        }
        static DWORD s_at = 0;
        static bool s_open = true;
        if (s_at == now)
        {
            return s_open;     // asked once per enemy of the look: the same answer
        }
        s_at = now;
        const CombatLearn::Forecast& pre = CombatLearn::forecast();
        const float bad = CombatLearn::badChance(pre);
        const bool barred = g_noSeekUntil && static_cast<int>(now - g_noSeekUntil) < 0;
        s_open = !barred && bad <= (Gear::healingLeft() == 0 ? 0.03f : 0.05f);
        if (s_open)
        {
            g_entryShutAt = 0;
            return true;
        }
        if (!g_entryShutAt)
        {
            g_entryShutAt = now;
        }
        static DWORD s_toldAt = 0;
        if (!s_toldAt || now - s_toldAt > 10000)
        {
            s_toldAt = now;
            LOG("AutoAttack: no fight sought: {} enemies, {:.0f}% to win, {:.0f}% to go bad for this class, {} healing "
                "potions{}",
                pre.foes, pre.win * 100.0f, bad * 100.0f, Gear::healingLeft(), barred ? ", just left one going bad" : "");
        }
        return false;
    }
    // Hopeless fights stepped back from (A3, the Battle Mage at level 4, 2026-11-12: away from groups of 5 at 418 %
    // of his health again and again, a level 4-7 region his farm and quest ground for hours, never a level up).
    std::deque<DWORD> g_hopelessAt;
    bool g_collecting = false;      // collecting a quest item or loot (declared early: the position watch reads it)
    DWORD g_questNoWayUntil = 0;    // a quest with no way there: the quests left alone until then
    // Where those hopeless fights were (tiles): a quest whose goal lies within 30 tiles of one waits 30 min (the
    // analyst, 2026-11-12: A3 stepped back from 7 enemies at 27 % to win, then walked on to its quest 24 tiles from
    // the archers' camp and died 16 s later).
    struct HopelessSpot { int tx, ty; DWORD at; };
    std::vector<HopelessSpot> g_hopelessSpots;
    bool nearHopelessSpot(int tx, int ty, DWORD now)
    {
        std::erase_if(g_hopelessSpots, [now](const HopelessSpot& h) { return now - h.at > 1800000; });
        for (const HopelessSpot& h : g_hopelessSpots)
        {
            if ((tx - h.tx) * (tx - h.tx) + (ty - h.ty) * (ty - h.ty) < 900)
            {
                return true;
            }
        }
        return false;
    }

    // Enemies given up as out of reach, by where THEY stand (tiles; the stuck solver, 2026-11-14: A8 gave up 25
    // different enemies in one rock pocket at 2775,3270, each new id starting the per-id wait again). Three different
    // ids within 15 tiles in 10 min veto the circle: no farming zone there for 15 min, and no enemy inside it
    // sought from beyond the melee for 5.
    struct UnreachableSpot { int tx, ty; uint32_t id; DWORD at; };
    std::vector<UnreachableSpot> g_unreachableSpots;
    struct VetoedCircle { int tx, ty; DWORD at; };
    std::vector<VetoedCircle> g_vetoedCircles;
    // span: 900000 for the farming zone's choice, 300000 for the choice of an enemy.
    bool inVetoedCircle(int tx, int ty, DWORD now, DWORD span)
    {
        std::erase_if(g_vetoedCircles, [now](const VetoedCircle& c) { return now - c.at > 900000; });
        for (const VetoedCircle& c : g_vetoedCircles)
        {
            if (now - c.at <= span && (tx - c.tx) * (tx - c.tx) + (ty - c.ty) * (ty - c.ty) < 225)
            {
                return true;
            }
        }
        return false;
    }
    void noteUnreachableSpot(uint32_t id, int tx, int ty, DWORD now)
    {
        std::erase_if(g_unreachableSpots, [now](const UnreachableSpot& s) { return now - s.at > 600000; });
        g_unreachableSpots.push_back({tx, ty, id, now});
        std::vector<uint32_t> ids;
        for (const UnreachableSpot& s : g_unreachableSpots)
        {
            if ((tx - s.tx) * (tx - s.tx) + (ty - s.ty) * (ty - s.ty) < 225 &&
                std::find(ids.begin(), ids.end(), s.id) == ids.end())
            {
                ids.push_back(s.id);
            }
        }
        if (ids.size() >= 3 && !inVetoedCircle(tx, ty, now, 900000))
        {
            g_vetoedCircles.push_back({tx, ty, now});
            LOG("AutoAttack: {} different enemies out of reach within 15 tiles of {},{} in 10 min: the place left for "
                "farming 15 min, its enemies 5",
                ids.size(), tx, ty);
            Findings::note("unreachable-place", static_cast<int32_t>(tx * kTileSize), static_cast<int32_t>(ty * kTileSize),
                           "{} enemies out of reach here", static_cast<int>(ids.size()));
        }
    }

    // Two hopeless fights in 10 min: outmatched where it is; farmed and quested only where the enemies are no
    // higher than the hero, for as long as two stay within the 10 min.
    bool outmatched(DWORD now)
    {
        while (!g_hopelessAt.empty() && now - g_hopelessAt.front() > 600000)
        {
            g_hopelessAt.pop_front();
        }
        return g_hopelessAt.size() >= 2;
    }
    DWORD g_retreatWalkAt = 0;      // the last walk order away
    DWORD g_noRetreatUntil = 0;     // after a long retreat, fight again for a while first
    constexpr DWORD kRetreatMaxMs = 12000, kRetreatPauseMs = 8000;
    constexpr double kRetreatWay = 8 * kTileSize;
    // The hero's last positions (one every 2 s while it moves, the last 2 minutes): the way back for a retreat.
    std::deque<std::pair<int32_t, int32_t>> g_fleeTrail;

    // The game's tutorial (the player, 2026-11-10: «tienen que saber hacer todo el tutorial perfectamente»; «beneficia
    // a los agentes que llevan buena conducta con el tutorial»). Manolito, block T/V3: the script variable «Tutorial»
    // (the save's script variables, a vector [0xAACF80+0x7550..+0x7554] of 0x24-byte records, name char[0x20], u32
    // value at +0x20) holds the step; 0x0D is over (or skipped). Each step taken is logged and remembered with how
    // long it took; one standing over 3 minutes is logged once with what it asks for, to be seen and taught.
    void watchTutorial(DWORD now)
    {
        static DWORD s_at = 0, s_stepAt = 0;
        static const uint8_t* s_var = nullptr;
        static uint32_t s_step = 0xFFFFFFFFu;
        static bool s_stuckLogged = false;
        static int s_taken = 0;
        if (now - s_at < 2000)
        {
            return;
        }
        s_at = now;
        const auto begin = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7550);
        const auto end = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7554);
        if (!begin || end <= begin || (end - begin) / 0x24 > 20000)
        {
            s_var = nullptr;
            return;
        }
        if (!s_var || s_var < begin || s_var >= end || std::strncmp(reinterpret_cast<const char*>(s_var), "Tutorial", 0x20) != 0)
        {
            s_var = nullptr;
            for (const uint8_t* r = begin; r + 0x24 <= end; r += 0x24)
            {
                if (std::strncmp(reinterpret_cast<const char*>(r), "Tutorial", 0x20) == 0)
                {
                    s_var = r;
                    break;
                }
            }
            if (!s_var)
            {
                return;
            }
        }
        static const char* const kAsks[] = {
            "no empezado", "bienvenida: abrir el cofre y hablar con el PNJ", "recoger objetos: abrir el cofre",
            "equipo: equipar un objeto de la mochila", "combate: atacar", "experiencia: repartir los puntos",
            "compañeros: aceptar al compañero", "brújula: seguirla", "misiones: hablar con el PNJ de «?!»",
            "mercaderes: comprar o vender", "caballo: comprar o montar un caballo", "historia: seguir la misión principal",
            "primeros pasos: abrir el cofre y hablar con el PNJ", "terminado", "recompensas: cobrar en el «!»",
            "maestro de combos: crear un combo", "herrero: engarzar", "escaleras: subirlas", "paso 18"};
        // Seen live 2026-11-10 (8 heroes): the value is the tutorial on screen, back to 0 once it is closed (2 at
        // the first chest, 16 by the smith), not a running count: each one shown is a lesson, counted once.
        static uint32_t s_seen = 0;     // bit per tutorial shown this session
        const uint32_t step = *reinterpret_cast<const uint32_t*>(s_var + 0x20);
        const char* ask = step < std::size(kAsks) ? kAsks[step] : "paso desconocido";
        if (step != s_step)
        {
            if (step && step < 32 && !(s_seen & (1u << step)))
            {
                s_seen |= 1u << step;
                ++s_taken;
                LOG("AutoAttack: tutorial {} shown ({}), {} of 17 seen this session", step, ask, s_taken);
                remember(std::format("tutorial {}: {}", step, ask));
            }
            else if (!step && s_step && s_step != 0xFFFFFFFFu)
            {
                LOG("AutoAttack: tutorial {} closed after {} s", s_step, (now - s_stepAt) / 1000);
            }
            s_step = step;
            s_stepAt = now;
            s_stuckLogged = false;
        }
        else if (!s_stuckLogged && step != 0 && now - s_stepAt > 20000)
        {
            s_stuckLogged = true;
            LOG("AutoAttack: tutorial {} ({}) open for {} s", step, ask, (now - s_stepAt) / 1000);
        }
    }

    // Riding (the tutorial's step 10). Manolito, block V3/V3b: mounting is an event to the rider, hero->vt[6](&ev),
    // a 0x44-byte cEvent (vtable 0x89095C) with +4 0x209 to mount, 0x20A to get off, +0x14 the horse's id (hero
    // +0x570); destroyed by 0x416B30 thiscall(&ev). Mounted: creature +0x200 & 0x10. Mounted blows are split by the
    // riding skill (down to a third): on for the long walks with no enemy within 20 tiles, off once one comes within
    // 12; at most a change every 8 s.
    // Free horses about (side 4, no owner at +0x570; Manolito, block H2: wild horses, taken by walking up and the ride
    // event), within 25 tiles on the surface, with their worth (Gear::horseWorth).
    struct WildHorse
    {
        uint32_t id;
        int32_t x, y;
        int worth;
    };
    std::vector<WildHorse> g_wildHorses;
    uint32_t g_rideCode = 0, g_rideHorse = 0;
    // A walk stuck on horseback (the analyst, 2026-11-11: A5, mounted all the time, the most «no nearer» of the eight,
    // in a wood; a horse does not pass where a man on foot does): off for a minute, on foot, before the tile is left.
    DWORD g_onFootUntil = 0;

    void sendRide(void*)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!hero || !g_rideHorse || !objects->creature(g_rideHorse))
        {
            return;
        }
        alignas(8) uint8_t ev[0x44] = {};
        *reinterpret_cast<uintptr_t*>(ev) = 0x89095C;
        *reinterpret_cast<uint32_t*>(ev + 4) = g_rideCode;
        *reinterpret_cast<uint32_t*>(ev + 0x14) = g_rideHorse;
        using Handle = void(__fastcall*)(void* self, void*, void* ev);
        const auto* vt = *reinterpret_cast<const uintptr_t* const*>(hero);
        reinterpret_cast<Handle>(vt[6])(hero, nullptr, ev);
        // The off event leaves the control on the horse (Manolito, block AG): given back in the same call, as the game's
        // input handler does on the next mouse event, so no frame sees the hero half off.
        if (g_rideCode == 0x20A)
        {
            if (cEngine* engine = FrameHooks::engine())
            {
                engine->controlled = hero->id;
            }
        }
        // Not destroyed with 0x416B30: its return is not documented (the code reviewer), and the zeroed event on the
        // stack holds nothing to free.
    }

    // The horseshoe's call (Manolito, block Y, 2026-11-11; the player: «el caballo se puede llamar siempre que él
    // quiera que automáticamente él se acerca a ti»): a cEvent 0x116 to the hero's vt[6], +0x10 the horse's id, as the
    // horseshoe's left click sends with the horse far. The hero's handler (0x530D68) uses hero +0x570 and does nothing
    // underground, in an interior or with the horse dead; the horse walks up (or is set beside its owner).
    void sendCall(void*)
    {
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!hero || !g_rideHorse)     // the horse may lie beyond the loaded ground: the handler goes by hero +0x570
        {
            return;
        }
        alignas(8) uint8_t ev[0x44] = {};
        *reinterpret_cast<uintptr_t*>(ev) = 0x89095C;
        *reinterpret_cast<uint32_t*>(ev + 4) = 0x116;
        *reinterpret_cast<uint32_t*>(ev + 0x10) = g_rideHorse;
        using Handle = void(__fastcall*)(void* self, void*, void* ev);
        const auto* vt = *reinterpret_cast<const uintptr_t* const*>(hero);
        reinterpret_cast<Handle>(vt[6])(hero, nullptr, ev);
    }

    // The call, at most every 30 s, only where the game's handler is where block Y has it.
    void callHorse(DWORD now, uint32_t horse, double tiles)
    {
        static DWORD s_calledAt = 0;
        static const bool s_known = [] {
            static constexpr uint8_t kSig[] = {0x83, 0xBD, 0x70, 0x05, 0x00, 0x00, 0x10, 0x0F};
            return std::memcmp(reinterpret_cast<const void*>(0x530D68), kSig, sizeof(kSig)) == 0;
        }();
        // Not again while it is on its way: both crashes after a call (A8 2026-11-13 09:01, Sacred.exe+fa47d; A2
        // 2026-11-14 09:39, +fa524, c0000005 0.8 s after) were a second call 30 s after the first, the horse by then
        // 9 and 15 tiles off and coming. Two minutes between calls.
        if (!s_known || (s_calledAt && now - s_calledAt < 120000))
        {
            return;
        }
        // Never with the horse within 1200 units (Manolito, block AX, from A2's dump): there the game's handler runs
        // its path finder at once, on the thread the event is sent from, over the finder's global grid (0xABA8F8) the
        // game's own logic may be using: the way points come out as rubbish and 0x4F9F20 reads through one. Farther
        // off it only starts a plain approach. Within that distance the horse is walked to or left.
        if (tiles > 0 && tiles * kTileSize <= 1300.0)
        {
            return;
        }
        if (!Act::allowed(Act::Kind::CallHorse, "call the horse (the horseshoe)"))
        {
            return;
        }
        s_calledAt = now;
        if (tiles > 0)
        {
            LOG("AutoAttack: horse {:x} {:.0f} tiles off: called (the horseshoe)", horse, tiles);
        }
        else
        {
            LOG("AutoAttack: horse {:x} beyond the loaded ground: called (the horseshoe)", horse);
        }
        remember("llama al caballo");
        g_rideHorse = horse;
        Inject::engineCall(&sendCall, nullptr);
    }

    // Half off the horse (Manolito, block AG, 2026-11-12, read live in A6): the hero on foot (+0x1EC 0) but its
    // riding bits (+0x200 & 0x14) still set and cEngine::controlled still the horse, so the camera and the mouse
    // follow the horse. The game itself mends it only on a mouse event (0x6173E7 in the input handler 0x6172C0); the
    // agent makes none. Mended as that does, on the game's thread: the off event with the horse's id (hero +0x570, the
    // handler 0x53677C does nothing with id 0), then controlled back to the hero.
    void mendHalfOff(void*)
    {
        cEngine* engine = FrameHooks::engine();
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!engine || !hero)
        {
            return;
        }
        const auto* h = reinterpret_cast<const uint8_t*>(hero);
        const uint32_t horse = *reinterpret_cast<const uint32_t*>(h + 0x570);
        if (horse && (*reinterpret_cast<const uint32_t*>(h + 0x200) & 0x14) && objects->creature(horse))
        {
            alignas(8) uint8_t ev[0x44] = {};
            *reinterpret_cast<uintptr_t*>(ev) = 0x89095C;
            *reinterpret_cast<uint32_t*>(ev + 4) = 0x20A;
            *reinterpret_cast<uint32_t*>(ev + 0x14) = horse;
            using Handle = void(__fastcall*)(void* self, void*, void* ev);
            const auto* vt = *reinterpret_cast<const uintptr_t* const*>(hero);
            reinterpret_cast<Handle>(vt[6])(hero, nullptr, ev);
        }
        engine->controlled = hero->id;
    }

    void ride(DWORD now, const cCreature* self)
    {
        // The hero, not the controlled creature (Manolito, block AD, 2026-11-11: mounted, engine->controlled is the
        // horse, whose +0x570 is its rider, so «horse 1» was the hero's own id and A3 stood still for hours).
        if (cObjectManager* om = cObjectManager::instance())
        {
            if (const cCreature* hero = om->hero())
            {
                self = hero;
            }
        }
        static DWORD s_at = 0;
        // Walking up to the horse: since when (0: not), and when last told to walk.
        static DWORD s_approachSince = 0, s_approachStep = 0, s_restUntil = 0;
        uint32_t horse = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x570);
        // A wild horse ridden unbound (+0x570 0): the one under the hero (+0x1EC), so it can be got off (the reviewer).
        if (!horse)
        {
            horse = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x1EC);
        }
        // Half off (the camera on the horse, the hero on foot beside it): mended, once in 5 s at most.
        if (const cEngine* engine = FrameHooks::engine();
            engine && engine->controlled != self->id &&
            !*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x1EC))
        {
            static DWORD s_mendAt = 0;
            static int s_mends = 0;
            if (now - s_mendAt > 5000)
            {
                s_mendAt = now;
                if (++s_mends <= 20)
                {
                    LOG("AutoAttack: half off the horse (controlled {:x}, the hero {:x} on foot): control back to the hero "
                        "(try {})", engine->controlled, self->id, s_mends);
                }
                Inject::engineCall(&mendHalfOff, nullptr);
            }
            return;
        }
        // A wild horse taken (the player, 2026-11-10: «existen caballos salvajes, son útiles cuando no tienes
        // caballo»; Manolito, H2: walk up to it and send the ride event): one within 25 tiles when the hero has none,
        // or one two levels better than his, on foot, no enemy within 15 tiles.
        static uint32_t s_wildId = 0;
        static DWORD s_wildSince = 0, s_wildStep = 0, s_wildSentAt = 0;
        static std::unordered_map<uint32_t, DWORD> s_wildFailed;
        if (Act::may(Act::Kind::Mount) && HeroProfile::current().cls != HeroProfile::Class::Dwarf &&
            !*(reinterpret_cast<const uint8_t*>(self) + 0x24) && !g_retreatUntil)
        {
            cObjectManager* om = cObjectManager::instance();
            const cCreature* own = horse && om ? om->creature(horse) : nullptr;
            if (s_wildSentAt)
            {
                // Taken: the hero's own now, or at least ridden (the hero where it stands; the code reviewer: the ride
                // event may mount a free horse without binding it, unconfirmed).
                const cCreature* wild = om ? om->creature(s_wildId) : nullptr;
                const bool riding = wild && std::abs(wild->x - self->x) <= 3 && std::abs(wild->y - self->y) <= 3;
                if (horse == s_wildId || riding)
                {
                    LOG("AutoAttack: wild horse {:x} taken ({})", s_wildId, horse == s_wildId ? "the hero's now" : "ridden, not bound");
                    s_wildId = 0;
                    s_wildSentAt = 0;
                }
                else if (now - s_wildSentAt > 3000)
                {
                    LOG("AutoAttack: wild horse {:x} not taken (riding skill?): left 10 min", s_wildId);
                    s_wildFailed[s_wildId] = now;
                    s_wildId = 0;
                    s_wildSentAt = 0;
                }
                return;
            }
            const bool onFoot = !own || std::abs(own->x - self->x) > 3 || std::abs(own->y - self->y) > 3;
            double nearestFoe = 1e9;
            for (const AggroFoe& f : g_aggroFoes)
            {
                nearestFoe = std::min(nearestFoe, std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y)));
            }
            const int bar = own ? Gear::horseWorth(own) + 2000 : 1;
            const WildHorse* best = nullptr;
            for (const WildHorse& w : g_wildHorses)
            {
                const auto failed = s_wildFailed.find(w.id);
                const cCreature* candidate = om ? om->creature(w.id) : nullptr;
                if (w.worth >= bar && (failed == s_wildFailed.end() || now - failed->second > 600000) &&
                    (!best || w.worth > best->worth) &&
                    (!candidate || AutoAttack::canRide(const_cast<cCreature*>(self), const_cast<cCreature*>(candidate))))
                {
                    best = &w;
                }
            }
            if (best && onFoot && nearestFoe > 15.0 * kTileSize)
            {
                const cCreature* wild = om ? om->creature(best->id) : nullptr;
                const double off = wild ? std::hypot(static_cast<double>(wild->x - self->x), static_cast<double>(wild->y - self->y)) : 1e9;
                if (best->id != s_wildId)
                {
                    s_wildId = best->id;
                    s_wildSince = now;
                    LOG("AutoAttack: wild horse {:x} (worth {}, the hero's {}) {:.1f} tiles off: going to take it", best->id,
                        best->worth, own ? Gear::horseWorth(own) : 0, off / kTileSize);
                }
                if (!wild || now - s_wildSince > 20000)
                {
                    LOG("AutoAttack: wild horse {:x} not reached in 20 s: left 10 min", s_wildId);
                    s_wildFailed[s_wildId] = now;
                    s_wildId = 0;
                    return;
                }
                if (off > 2.0 * kTileSize)
                {
                    g_doorHoldUntil = now + 1500;
                    if (now - s_wildStep > 1000)
                    {
                        s_wildStep = now;
                        g_walkX = wild->x;
                        g_walkY = wild->y;
                        sendWalk();
                    }
                    return;
                }
                if (!AutoAttack::canRide(const_cast<cCreature*>(self), const_cast<cCreature*>(wild)))
                {
                    LOG("AutoAttack: wild horse {:x}: riding skill too low for it (the game's test): left 10 min", s_wildId);
                    s_wildFailed[s_wildId] = now;   // else the next tick picks it again (A4, 18-11: 34 000 times, hero lost)
                    s_wildId = 0;
                    return;
                }
                if (!Act::allowed(Act::Kind::Mount, "mount a wild horse"))
                {
                    return;
                }
                LOG("AutoAttack: mounting wild horse {:x}", s_wildId);
                g_rideCode = 0x209;
                g_rideHorse = s_wildId;
                Inject::engineCall(&sendRide, nullptr);
                s_wildSentAt = now;
                return;
            }
            s_wildId = 0;
        }
        // The Dwarf does not ride (Builds.md; the player, 2026-11-10: «el enano no tiene animación montado»).
        if (!horse || *(reinterpret_cast<const uint8_t*>(self) + 0x24) ||
            HeroProfile::current().cls == HeroProfile::Class::Dwarf)
        {
            s_approachSince = 0;
            return;
        }
        // The 8 s between changes holds the mounting only: getting off for an enemy near is never put off (the live
        // verifier, 2026-11-10: off at 7 and 4 tiles, the gate had held it).
        const bool onFoot = g_onFootUntil && static_cast<int>(now - g_onFootUntil) < 0;
        const bool gated = now - s_at < 8000 || static_cast<int>(now - s_restUntil) < 0 || onFoot;
        // Mounted: the horse stands exactly where the rider does (seen live 2026-11-10, the player's Gladiator on its
        // horse: same position each second; +0x200 & 0x10, the guess, stayed clear and the agent kept mounting).
        cObjectManager* om = cObjectManager::instance();
        const cCreature* steed = om ? om->creature(horse) : nullptr;
        // Not while stepping back from a fight (the code reviewer: a walk to the horse must not undo a retreat).
        if (!steed && !g_retreatUntil && (ClickWalk::routing() || g_questTravel) && now - s_at > 8000)
        {
            // Left so far behind that it is not on the loaded ground: called all the same, on a long walk with no
            // enemy within 15 tiles.
            bool calm = true;
            for (const AggroFoe& f : g_aggroFoes)
            {
                calm = calm && std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y)) > 15.0 * kTileSize;
            }
            if (calm)
            {
                callHorse(now, horse, 0.0);
            }
        }
        // A dead horse is not mounted nor called (the code reviewer: 3 tries and 10 min of rest spent on it).
        if (!steed || g_retreatUntil || steed->health <= 0)
        {
            s_approachSince = 0;
            return;
        }
        // The hero's own mount field (+0x1EC, the horse's id while riding; HeroProfile and AgentSave read it), not the
        // horse standing where the hero does: just off, the horse stays on the hero's spot, and the off event sent
        // again each 1.5 s put the hero back up (A6 2026-11-12 00:08-00:27, 30 «getting off» in a row, standing still).
        const bool mounted = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x1EC) != 0;
        // Ride events sent with the hero still on foot after them (no riding skill?): after 3, a long rest.
        static int s_unmounted = 0;
        if (mounted)
        {
            s_unmounted = 0;
        }
        else if (s_unmounted >= 3)
        {
            LOG("AutoAttack: 3 mounts of horse {:x} left the hero on foot: on foot for 10 min", horse);
            s_unmounted = 0;
            s_restUntil = now + 600000;
            return;
        }
        double nearest = 1e9;
        for (const AggroFoe& f : g_aggroFoes)
        {
            nearest = std::min(nearest, std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y)));
        }
        const bool longWalk = ClickWalk::routing() || g_questTravel;
        int close = 0;
        for (const AggroFoe& f : g_aggroFoes)
        {
            close += std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y)) < 8.0 * kTileSize;
        }
        const bool hardOnFoot = close >= 3 && Config::tactics.arts && Tactics::artsBarredMounted() > 0 && Mind::now().hardOnFoot;
        // Off for a hard fight: not back up until 20 s without one (the code reviewer: off with three near, up again
        // as soon as fewer than three, back and forth). An ordinary fight is still fought from the saddle.
        static DWORD s_hardAt = 0;
        if (hardOnFoot)
        {
            s_hardAt = now;
        }
        const bool settled = !s_hardAt || now - s_hardAt > 20000;
        // The Vampiress rides only in her knight's form (the player, 2026-11-12).
        const bool vampire = Tactics::vampireForm(now);
        uint32_t code = 0;
        // Up again once the nearest enemy is 5 tiles off: the saddle is the better place to fight from (the player,
        // 2026-11-11), so only an enemy at hand puts the walk to the horse off.
        if (!mounted && longWalk && nearest > 5.0 * kTileSize && !hardOnFoot && !vampire && settled &&
            (s_approachSince || !gated))
        {
            code = 0x209;
        }
        else if (mounted && vampire && now - s_at > 1500)
        {
            static DWORD s_formToldAt = 0;
            if (now - s_formToldAt > 30000)
            {
                s_formToldAt = now;
                LOG("AutoAttack: the Vampiress in her vampire form: off the horse");
            }
            code = 0x20A;
        }
        // A fight and her turn due: off first (V1: the vampire form has no mounted variant; the turn may be barred up
        // there), the turn follows on foot (Tactics, chooseArt).
        else if (mounted && Tactics::vampireTurnWanted() && now - s_at > 1500)
        {
            // Told once per 30 s: in the off events' rest it came every frame (A6 2026-11-24, 39 lines in 2 s).
            static DWORD s_vampToldAt = 0;
            if (now - s_vampToldAt > 30000)
            {
                s_vampToldAt = now;
                LOG("AutoAttack: the Vampiress has a fight: off the horse for the vampire form");
            }
            code = 0x20A;
        }
        else if (mounted && onFoot && now - s_at > 1500)
        {
            code = 0x20A;
        }
        // Every class fights mounted (Mind: dismountTiles 0), the off branch kept for a class given a distance.
        else if (mounted && nearest < Mind::now().dismountTiles * kTileSize && now - s_at > 1500)
        {
            code = 0x20A;
        }
        // But a hard fight (three or more within 8 tiles) is fought on foot when arts in the slots cannot be cast up
        // there (the player, 2026-11-11: «no todas las habilidades pueden ser usadas a caballo»): an easy one the
        // saddle's quicker blows end anyway.
        else if (mounted && hardOnFoot && now - s_at > 1500)
        {
            static DWORD s_barredToldAt = 0;
            if (now - s_barredToldAt > 30000)
            {
                s_barredToldAt = now;
                LOG("AutoAttack: {} enemies near and arts barred on horseback: fighting on foot", close);
            }
            code = 0x20A;
        }
        // Off events the game does not act on (A6 2026-11-12 20:03-20:08: «getting off» each 1.5 s for 5 min, the mount
        // field still set, the hero stuck): after 4 in a row, none for a minute, the walk out going on from the saddle.
        // Nothing on the horse without the player's leave (2026-11-14: off his horse in a fight, the agent off).
        if (code == 0x209 && !Act::allowed(Act::Kind::Mount, "mount the horse for the long walk"))
        {
            code = 0;
        }
        else if (code == 0x20A &&
                 !Act::allowed(Act::Kind::Dismount, hardOnFoot ? "get off the horse: enemies near and arts barred on horseback"
                                                         : "get off the horse"))
        {
            code = 0;
        }
        static int s_offSent = 0;
        static DWORD s_offRestUntil = 0;
        if (!mounted)
        {
            s_offSent = 0;
        }
        if (code == 0x20A && s_offRestUntil && static_cast<int>(now - s_offRestUntil) < 0)
        {
            code = 0;
        }
        if (!code)
        {
            s_approachSince = 0;
            return;
        }
        // The game does not get off with a walk under way (the stuck solver, 2026-11-13: every ignored 0x20A came
        // each 1.5 s with ClickWalk's route on): the route cancelled and the hero stopped first, the event 0.4 s on.
        static DWORD s_stoppedAt = 0;
        if (code == 0x20A)
        {
            if (ClickWalk::routing())
            {
                ClickWalk::cancel();
                HeroMove::stop();
                s_stoppedAt = now;
                g_doorHoldUntil = now + 1500;   // the roam's travel holds its orders: the event goes out 0.4 s on
                return;
            }
            if (now - s_stoppedAt < 400)
            {
                return;
            }
        }
        // Counted here, where the event is about to go out (the stuck solver, 2026-11-16, A8: counted before the stop
        // and its 0.4 s wait, five frames made «4 off events» with none sent: 0 «getting off horse» in 600 lines, 10
        // rests of a minute, the hero never off and AgentSave waiting for it 25 min).
        if (code == 0x20A && ++s_offSent > 4)
        {
            LOG("AutoAttack: 4 off events and the hero still up (mount field {:x}, controlled {:x}, horse {:x}): none for "
                "a minute",
                *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x1EC),
                FrameHooks::engine() ? FrameHooks::engine()->controlled : 0u, horse);
            s_offSent = 0;
            s_offRestUntil = now + 60000;
            return;
        }
        if (code == 0x209 && !AutoAttack::canRide(const_cast<cCreature*>(self), const_cast<cCreature*>(steed)))
        {
            static DWORD s_toldAt = 0;
            if (!s_toldAt || now - s_toldAt > 300000)
            {
                s_toldAt = now;
                LOG("AutoAttack: horse {:x}: riding skill too low for it (the game's test): on foot", horse);
            }
            s_approachSince = 0;
            return;
        }
        if (code == 0x209)
        {
            // Up as a player gets up: the hero walks to the horse first and mounts beside it (the player, 2026-11-10:
            // the event put the hero onto the horse wherever it stood, «se teleporta encima del caballo»; Manolito's
            // block U2: a click on one's own horse is no order, the game's pick skips it, so a walk to it).
            const double off = std::hypot(static_cast<double>(steed->x - self->x), static_cast<double>(steed->y - self->y));
            if (off > 2.0 * kTileSize)
            {
                // More than 10 tiles back: left behind, on foot (the Daemon walked 24 tiles back to it after each
                // fight, the player: «no está teniendo mucha eficiencia»).
                if (off > 5.0 * kTileSize)
                {
                    // Far: called as the horseshoe calls it (on the surface, the hero's handler checks the rest), and
                    // mounted once it has come up; never walked back for.
                    callHorse(now, horse, off / kTileSize);
                    s_at = now;     // not walked back to: it comes
                    s_approachSince = 0;
                    return;
                }
                if (!s_approachSince)
                {
                    s_approachSince = now;
                    LOG("AutoAttack: walking to horse {:x} ({:.1f} tiles) to mount it", horse, off / kTileSize);
                }
                else if (now - s_approachSince > 20000)
                {
                    // Two walks in a row that did not reach it (A3: 49 tries, 10 never there): 10 min on foot.
                    static int s_notReached = 0;
                    static DWORD s_notReachedAt = 0;
                    s_notReached = now - s_notReachedAt < 180000 ? s_notReached + 1 : 1;
                    s_notReachedAt = now;
                    LOG("AutoAttack: horse {:x} not reached in 20 s ({:.1f} tiles): on foot{}", horse, off / kTileSize,
                        s_notReached >= 2 ? " for 10 min" : "");
                    s_restUntil = now + (s_notReached >= 2 ? 600000 : 60000);
                    s_approachSince = 0;
                    return;
                }
                g_doorHoldUntil = now + 1500;   // the roam's travel holds its orders meanwhile
                if (now - s_approachStep > 1000)
                {
                    s_approachStep = now;
                    g_walkX = steed->x;
                    g_walkY = steed->y;
                    sendWalk();
                }
                return;
            }
            s_approachSince = 0;
            ++s_unmounted;
        }
        s_at = now;
        LOG("AutoAttack: {} horse {:x} ({:.0f} tiles to the nearest enemy)", code == 0x209 ? "mounting" : "getting off", horse,
            nearest < 1e8 ? nearest / kTileSize : 99.0);
        g_rideCode = code;
        g_rideHorse = horse;
        if (code == 0x209)
        {
            // The route under way is dropped: travel() asks for it again from the saddle (54 % of the mounts with no
            // fight ended «20 s in one place on horseback», one walk order sent and routing() still true).
            ClickWalk::cancel();
            g_doorHoldUntil = now + 2500;
        }
        Inject::engineCall(&sendRide, nullptr);
    }

    void noteTrail(DWORD now, int32_t x, int32_t y, int layer)
    {
        static DWORD s_at = 0;
        static int s_layer = -1;
        if (layer != s_layer)
        {
            s_layer = layer;
            g_fleeTrail.clear();    // another floor: the old way back does not lead from here
        }
        if (now - s_at < 2000)
        {
            return;
        }
        s_at = now;
        if (!g_fleeTrail.empty() && std::hypot(static_cast<double>(x - g_fleeTrail.back().first),
                                           static_cast<double>(y - g_fleeTrail.back().second)) < 2 * kTileSize)
        {
            return;
        }
        g_fleeTrail.emplace_back(x, y);
        if (g_fleeTrail.size() > 60)
        {
            g_fleeTrail.pop_front();
        }
    }

    // The hero's trail (the player's wish, 2026-11-09: the agent knows where it is and how it got there): a point for
    // each tile walked, so a hero shut in backs out the way it came. Seen live: the Vampiress walked into her start
    // house after a fixture, the tile test blind in there, and roamed against its walls for 20 minutes.
    struct Crumb
    {
        int32_t x, y;
        int layer;
    };
    std::vector<Crumb> g_trail;
    bool g_backing = false;     // walking back along the trail (its points are not noted meanwhile)

    void noteTrail(const cCreature* self, int layer)
    {
        if (g_backing)
        {
            return;
        }
        if (!g_trail.empty())
        {
            const Crumb& last = g_trail.back();
            const double d = std::hypot(static_cast<double>(self->x - last.x), static_cast<double>(self->y - last.y));
            if (last.layer != layer || d > 40.0 * kTileSize)
            {
                g_trail.clear();    // a portal, a load: the way back is not this one
            }
            else if (d < kTileSize)
            {
                return;
            }
        }
        g_trail.push_back({self->x, self->y, layer});
        if (g_trail.size() > 400)
        {
            g_trail.erase(g_trail.begin(), g_trail.begin() + 100);
        }
    }

    // Low on health, no healing potion left, enemies close: walk away from them (the order a click on the ground
    // gives, to a point 8 tiles off on the far side of the hero), again every second while it lasts. Ends once health
    // is back up, a potion turns up, no enemy is close any more, or after 12 s (then the hero fights again for 8 s).
    bool retreat(DWORD now, const cCreature* self, int health, int maximum, const AimAssist::Foe* foes, int count,
                 float hx, float hy, float range, cObjectManager* objects)
    {
        const Config::Tactics& c = Config::tactics;
        double cx = 0.0, cy = 0.0;
        int close = 0;
        bool anyNear = false;   // within Range: a retreat ends only once all are further (no back and forth)
        // Those with aggro on the hero are the ones that follow (Manolito, block N): away from them, and over once none
        // is near; those without, standing by, are left out (the old way, all of them, when none has aggro).
        const cCreature* heroCreature = objects->hero();
        const uint32_t heroId = heroCreature ? heroCreature->id : self->id;
        bool anyAggro = false;
        for (int i = 0; i < count; ++i)
        {
            anyAggro = anyAggro || aggroOnHero(objects->object(foes[i].id), heroId, self->id);
        }
        for (int i = 0; i < count; ++i)
        {
            const float dx = foes[i].x - hx, dy = foes[i].y - hy;
            cObject* o = objects->object(foes[i].id);
            if (anyAggro && !aggroOnHero(o, heroId, self->id))
            {
                continue;
            }
            anyNear = anyNear || dx * dx + dy * dy < range * range;
            if (o && dx * dx + dy * dy < (range * 0.45f) * (range * 0.45f))
            {
                cx += o->x;
                cy += o->y;
                ++close;
            }
        }
        // Low on health, or below 40 % with those striking about to take the rest in moments.
        // Or the forecast gives the fight under 50 % with health below 60 % (the analyst, 2026-11-10: out of healing
        // potions at 59 of 158, into another fight of three at 20 % to win).
        const CombatLearn::Forecast& fc = CombatLearn::forecast();
        // Without a healing potion, a big fight forecast lost is left early (the analyst, 2026-11-10 21:03: the
        // Gladiator, Dark Elf and Wood Elf below 20 % of health in 12-13 % of their fights, into 11-16 enemies with
        // the potions gone): at 85 % of health with five or more about.
        // Each class by its own mind (Mind, docs/Mentalidades.md): the frail casters leave sooner; the player's own
        // retreat percent, once changed in the menu from its 25, rules over the class's.
        const Mind::Values& mind = Mind::now();
        // Careful after dying twice from the same save: away 15 points sooner.
        const int retreatPct = (c.retreatPercent != 25 ? c.retreatPercent : mind.retreatPercent) +
                               (AgentSave::deathsSinceSave() >= 2 ? 15 : 0);
        const bool dry = Gear::healingLeft() == 0 && fc.foes >= 5;
        const bool lost = fc.foes > 0 && fc.win < mind.lostWin &&
                          health * 100 <= maximum * (dry ? mind.lostHealthDryPct : mind.lostHealthPct);
        const bool low = health * 100 <= maximum * retreatPct ||
                         (health * 100 <= maximum * 40 && CombatLearn::secondsToDie() < 2.5f) || lost;
        const bool noPotions = CombatState::noPotionsAt.load() != 0;
        // A group the fight with is foreseen hopeless is left at once, potions or not, health full or not (the
        // player, 2026-11-11: «la vampiresa siempre tiene la costumbre de morir en el mismo lugar»: into 8 at 18 % to
        // win, the potions drunk one by one, then dead; twice at the same spot).
        // Also one or two far above the hero (A3, the Battle Mage at level 4, 2026-11-12: 9 deaths in 31 min, each a
        // minute after loading, into one enemy foreseen at 254 % of his health lost; the «careful» after two deaths
        // only moved the retreat by 15 points): more than one and a half lives' worth, or more than one once careful.
        const bool careful = AgentSave::deathsSinceSave() >= 2;
        // On the loss corrected by what fights like it really cost (the player, 2026-11-12: the Daemon fled one thin
        // goblin «foreseeing defeat»: 1000 % raw, but her forecasts ran eleven times too grim, 47 % to win), and never
        // from one enemy alone the hero's blows put down in a few seconds.
        const bool quickOne = fc.foes == 1 && fc.seconds > 0.0f && fc.seconds < 6.0f;
        // C4 (docs/Criterios.md: 3 potions or more in a fight were 38.6 % of the near-deaths): two drunk and two or
        // more still up, the fight is left now, whatever the health.
        // Not at nine tenths of the health or more with the fight foreseen won at nine in ten (the stuck solver, 2026-11-17, A1,
        // a Seraphim of level 27 with 1578 health: «a hopeless fight (4 enemies, 97% to win, 0% to go bad): stepping back at
        // 1578 of 1578 health», 86 in 55 min, the potions of the same fight drunk and the hero whole again; two of them in
        // 10 min is «outmatched here» and the quests above its level are held for good: 13 h with none done).
        const bool drained = CombatLearn::fightPotions() >= 2 && fc.foes >= 2 && !quickOne &&
                             !(health * 100 >= maximum * 90 && fc.win >= 0.9f);
        // More enemies on the hero than the class takes at once (docs/Mentalidades.md §3, maxFoes / maxFoesDry with
        // no healing potion) and the fight not clearly won: left too.
        const int foeCap = Gear::healingLeft() > 0 ? mind.maxFoes : mind.maxFoesDry;
        const bool overrun = foeCap > 0 && fc.foes > foeCap && fc.win < 0.6f;
        // No fights lost: the class's own record says a fight like this goes bad (12 %, about 46 % to win by the
        // prior): left whatever the health, after 4 s in it and 1.5 s of it so; at once from 25 % (about 17 % to win).
        static DWORD s_badSince = 0;
        const float badNow = Config::autoAttack.noLostFights ? CombatLearn::badChance(fc) : 0.0f;
        s_badSince = badNow >= 0.12f ? (s_badSince ? s_badSince : now) : 0;
        const bool goesBad = Config::autoAttack.noLostFights && !quickOne && fc.foes > 0 &&
                             CombatLearn::fightSeconds() >= 4.0f &&
                             ((s_badSince && now - s_badSince >= 1500) || badNow >= 0.25f);
        const bool foreseen = goesBad || overrun || (!quickOne &&
                              ((fc.foes >= 4 && fc.win < 0.25f && fc.expected > 1.0f) ||
                               (fc.foes > 0 && fc.expected > 1.5f && fc.win < 0.75f) ||
                               (careful && fc.foes > 0 && fc.expected > 1.0f && fc.win < 0.85f)));
        // A forecast alone does not send a whole hero running (the player, watching A1, 2026-11-14: the Seraphim at
        // 349 of 349 among ten goblins that did her no harm, «a hopeless fight (11 enemies, 49% to win)», stepping
        // back every 20 s for minutes; «ya hubiera ganado la batalla si en vez de huir empezara a atacar»). The
        // forecast counts heads; what the enemies really do shows on the health. Left on the forecast only once a
        // tenth of the health is gone, or when it foresees three lives' worth of loss; with nine tenths still there the
        // way out is as open as before.
        const bool hurt = health * 100 < maximum * 90;
        const bool doomed = drained || (foreseen && (hurt || fc.expected > 3.0f));
        // Not from a fight about won (the player, 2026-11-10: «huyendo de un enemigo que le falta poco para morir pero
        // se deja matar por huir»): running, the blows come in the back all the same. Kept fighting when the
        // forecast puts all down well before the hero's health would go, or when only one is close and nearly down.
        int lastBreath = 0;
        for (int i = 0; i < count; ++i)
        {
            const float dx = foes[i].x - hx, dy = foes[i].y - hy;
            if (dx * dx + dy * dy < (range * 0.45f) * (range * 0.45f) && foes[i].maxHealth > 0 &&
                foes[i].health * 4 <= foes[i].maxHealth)
            {
                ++lastBreath;
            }
        }
        const float toDie = CombatLearn::secondsToDie();
        const bool aboutWon = (fc.foes > 0 && fc.win >= 0.6f && fc.seconds > 0.0f && fc.seconds < toDie * 0.7f) ||
                              (close == 1 && lastBreath == 1 && toDie > 2.0f);
        if (aboutWon)
        {
            if (g_retreatUntil)
            {
                LOG("AutoAttack: stepping back over: the fight is about won ({:.1f} s to win, {:.1f} s of health)",
                    fc.seconds, toDie);
                g_retreatUntil = 0;
            }
            return false;
        }
        if (g_retreatUntil)
        {
            // Really got away (the player, 2026-11-10: «saber cuándo realmente ha huido»): none has the hero as its
            // aim any more, and none within its aggro reach (Manolito, block N: they give up beyond 1500 u). Then it
            // rests out of their reach a while (health comes back without enemies near) before playing on.
            bool chased = false;
            double nearest = 1e9;
            for (const AggroFoe& f : g_aggroFoes)
            {
                const double d = std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y));
                nearest = std::min(nearest, d);
                chased = chased || f.onHero;
            }
            // Only on the surface: g_aggroFoes is filled there alone, so below ground it would always read as got away
            // (the code reviewer, 2026-11-10).
            if (!*(reinterpret_cast<const uint8_t*>(self) + 0x24) && !chased && nearest > 700.0 && g_retreatWalkAt &&
                now - g_retreatWalkAt > 1500)
            {
                LOG("AutoAttack: got away: no enemy after the hero any more ({:.0f} tiles from the nearest), resting at "
                    "{} of {} health", nearest < 1e8 ? nearest / kTileSize : 99.0, health, maximum);
                remember(std::format("escapó: nadie le persigue ({} de {} de vida)", health, maximum));
                g_retreatUntil = 0;
                g_noRetreatUntil = now + kRetreatPauseMs;
                if (health * 100 < maximum * 70)
                {
                    g_quietUntil = now + 15000;
                }
                return false;
            }
            // Cornered: a retreat that gets nowhere while the blows come is the worst of both (the player, 2026-11-12:
            // the Daemon «se queda atascada sin poder salir, con enemigos atacándola y ella sin reaccionar», fighting
            // back only after a potion ended the retreat, and then winning). Under 1.5 tiles in 3 s with health lost
            // over them: back to the fight, no retreat for the pause.
            static int32_t s_cornerX = 0, s_cornerY = 0;
            static DWORD s_cornerAt = 0;
            static int s_cornerHealth = 0;
            if (!s_cornerAt || g_retreatStartAt > s_cornerAt)
            {
                s_cornerX = self->x, s_cornerY = self->y, s_cornerAt = now, s_cornerHealth = health;
            }
            else if (now - s_cornerAt >= 3000)
            {
                const double moved = std::hypot(static_cast<double>(self->x - s_cornerX), static_cast<double>(self->y - s_cornerY));
                if (moved < 1.5 * kTileSize && health < s_cornerHealth && anyNear)
                {
                    LOG("AutoAttack: cornered while stepping back ({:.1f} tiles in 3 s, {} health lost): fighting back",
                        moved / kTileSize, s_cornerHealth - health);
                    remember(std::format("acorralada al huir: vuelve a luchar ({} de {} de vida)", health, maximum));
                    s_cornerAt = 0;
                    g_retreatUntil = 0;
                    g_retreatDoomed = false;
                    g_noRetreatUntil = now + kRetreatPauseMs;
                    return false;
                }
                s_cornerX = self->x, s_cornerY = self->y, s_cornerAt = now, s_cornerHealth = health;
            }
            const bool recovered =
                health * 100 >= maximum * std::min((c.retreatPercent != 25 ? c.retreatPercent : Mind::now().retreatPercent) + 20, 90);
            bool tooLong = static_cast<int>(now - g_retreatUntil) >= 0;
            // Not back into the fight with little health and no potion (the live verifier, 2026-11-11: 5 of 13
            // deaths within 15 s of «too long, fighting again», one at 30 of 189): the retreat goes on, three times
            // at most, before it does turn to fight.
            if (tooLong && noPotions && anyNear && health * 100 < maximum * 40 && g_retreatExtended < 3)
            {
                ++g_retreatExtended;
                g_retreatUntil = now + kRetreatMaxMs;
                LOG("AutoAttack: stepping back on: {} of {} health and no potion ({} of 3)", health, maximum, g_retreatExtended);
                tooLong = false;
            }
            else if ((recovered && !g_retreatDoomed) || (!noPotions && !g_retreatDoomed) || !anyNear || tooLong)
            {
                g_retreatExtended = 0;
            }
            // Not on the first look that sees fewer (the live verifier, 2026-11-11: 24 of 33 such retreats over in
            // under 3 s, the group still there, only out of sight): 8 s away at least.
            if (g_retreatDoomed && (Config::autoAttack.noLostFights ? badNow <= 0.05f : !doomed) && !tooLong && anyNear &&
                g_retreatStartAt && now - g_retreatStartAt > 8000)
            {
                LOG("AutoAttack: stepping back over (the fight no longer foreseen hopeless)");
                g_retreatUntil = 0;
                g_retreatDoomed = false;
                return false;
            }
            if ((recovered && !g_retreatDoomed) || (!noPotions && !g_retreatDoomed) || !anyNear || tooLong)
            {
                LOG("AutoAttack: stepping back over ({})", recovered    ? "health back up"
                                                           : !noPotions ? "a potion turned up"
                                                           : !anyNear   ? "no enemy near"
                                                                        : "too long, fighting again");
                g_retreatUntil = 0;
                if (tooLong)
                {
                    g_noRetreatUntil = now + kRetreatPauseMs;
                }
                return false;
            }
        }
        else if (!c.retreat || (!low && !doomed) || (!noPotions && !doomed) || !close ||
                 (g_noRetreatUntil && static_cast<int>(now - g_noRetreatUntil) < 0))
        {
            return false;
        }
        else if (!Act::allowed(Act::Kind::Retreat, "step back from a fight that goes badly"))
        {
            return false;
        }
        else
        {
            g_retreatUntil = now + kRetreatMaxMs;
            g_retreatWalkAt = 0;
            g_retreatExtended = 0;
            g_retreatDoomed = doomed && !(low && noPotions);
            g_retreatStartAt = now;
            if (!noPotions)
            {
                CombatState::drinkWantedAt = now;   // a potion before turning the back (the analyst's criterion 2)
            }
            if (g_retreatDoomed)
            {
                g_hopelessAt.push_back(now);
                if (Config::autoAttack.noLostFights)
                {
                    g_noSeekUntil = now + 20000;
                }
                g_hopelessSpots.push_back({static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize), now});
                LOG("AutoAttack: a hopeless fight ({} enemies, {:.0f}% to win, {:.0f}% to go bad{}): stepping back at {} of "
                    "{} health{}",
                    fc.foes, fc.win * 100.0f, badNow * 100.0f, goesBad ? ", the class's record" : "", health, maximum,
                    outmatched(now) ? "; outmatched here: farming and quests only where the enemies are not above the hero"
                                    : "");
            }
            setIntent(Intent::Recover, "low on health, no healing potion or a fight foreseen lost: stepping back");
            LOG("AutoAttack: stepping back at {} of {} health, no healing potion, {} enemies close", health, maximum,
                close);
            // Down below a quarter by them: those close are not gone back to for 3 min, fought only if they come
            // into the melee (the analyst, 2026-11-10: an Orc Warrior of level 5 brought the Seraphim to 5-15 of 158
            // five times in 8 min, the hero healed and went back to it each time).
            if (health * 4 < maximum || g_retreatDoomed)
            {
                for (int i = 0; i < count; ++i)
                {
                    const float dx = foes[i].x - hx, dy = foes[i].y - hy;
                    if (dx * dx + dy * dy < range * range)
                    {
                        g_unreachable[foes[i].id] = now + 180000;
                        g_unreachableAt[foes[i].id] = 1e9f;
                        LOG("AutoAttack: {:x} too strong for now (health {} of {}): not gone back to for 3 min",
                            foes[i].id, health, maximum);
                    }
                }
            }
        }
        if (close && (!g_retreatWalkAt || now - g_retreatWalkAt >= 1000))
        {
            // Where to: back the way the hero came (the player: «muriendo por no saber huir»; straight away from the
            // enemies ran it into walls and unknown ground, caught there): of the hero's last positions, the one
            // farthest from the enemies that lies away from them, at least 8 tiles off; else straight away as before.
            const double ex = cx / close, ey = cy / close;
            double bestScore = 0.0;
            int32_t bx = 0, by = 0;
            int bestCrossed = 0;
            const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
            // Where to run (the player, 2026-11-10: «la idea de saber el aggro es identificar por donde huir o por donde
            // no pasar»): the way back and 16 ways around, each weighed by how far it takes the hero from those after
            // it, less what it costs to pass by the hostiles not after it yet (each within its aggro reach of the way
            // would join: heavy), on walkable ground only.
            std::vector<std::pair<int32_t, int32_t>> options(g_fleeTrail.begin(), g_fleeTrail.end());
            for (int k = 0; k < 16; ++k)
            {
                const double a = k * 3.14159265 / 8.0;
                for (const double tiles : {10.0, 16.0})
                {
                    options.emplace_back(static_cast<int32_t>(self->x + std::cos(a) * tiles * kTileSize),
                                         static_cast<int32_t>(self->y + std::sin(a) * tiles * kTileSize));
                }
            }
            const double heroFromFoes = std::hypot(self->x - ex, self->y - ey);
            for (const auto& [px, py] : options)
            {
                const double fromFoes = std::hypot(px - ex, py - ey), fromHero = std::hypot(px - self->x, py - self->y);
                // Not a trail point far back either (the stuck solver, 2026-11-14, A6: 13 «safest way» runs of 46 to
                // 446 tiles, the trail's points ridden 10-30 tiles apart; a run is 12 s at most and is meant to leave
                // the pack behind over ground walked, not to cross the map).
                if (fromHero < kRetreatWay || fromHero > 45.0 * kTileSize || fromFoes < heroFromFoes + 4 * kTileSize ||
                    ClickWalk::walkable(layer, static_cast<int>(px / kTileSize), static_cast<int>(py / kTileSize)) == 0)
                {
                    continue;
                }
                int crossed = 0;
                for (const AggroFoe& f : g_aggroFoes)
                {
                    if (f.onHero)
                    {
                        continue;
                    }
                    // Its distance to the way (the segment hero -> point).
                    const double vx = px - self->x, vy = py - self->y, wx = f.x - self->x, wy = f.y - self->y;
                    const double t = std::clamp((vx * wx + vy * wy) / std::max(vx * vx + vy * vy, 1.0), 0.0, 1.0);
                    if (std::hypot(wx - t * vx, wy - t * vy) < kAggroTiles * kTileSize)
                    {
                        ++crossed;
                    }
                }
                const double score = fromFoes - 0.3 * fromHero - crossed * 20.0 * kTileSize + 1.0 * kTileSize;
                if (score > bestScore)
                {
                    bestScore = score;
                    bx = px;
                    by = py;
                    bestCrossed = crossed;
                }
            }
            // Running that only draws more enemies in makes the fight harder, not easier (the player, watching A6,
            // 2026-11-14: «al huir solo está cogiendo aggro de más enemigos»; the analyst: fights joined by others
            // end in death five times as often). With no way out that passes by none of them, and a quarter of the
            // health or more left, the hero stands and fights those it has; the retreat is off for a while.
            const bool noCleanWay = bestScore <= 0.0 || bestCrossed > 0;
            if (noCleanWay && health * 4 >= maximum)
            {
                LOG("AutoAttack: no way out that draws no more enemies ({} would join, {} of {} health): standing and "
                    "fighting",
                    bestScore > 0.0 ? bestCrossed : -1, health, maximum);
                g_retreatUntil = 0;
                g_retreatDoomed = false;
                g_noRetreatUntil = now + kRetreatPauseMs;
                return false;
            }
            if (bestScore > 0.0)
            {
                g_walkX = bx;
                g_walkY = by;
            }
            else
            {
                const double ax = self->x - ex, ay = self->y - ey;
                const double len = std::sqrt(ax * ax + ay * ay);
                const double ux = len > 1.0 ? ax / len : 1.0, uy = len > 1.0 ? ay / len : 0.0;
                g_walkX = static_cast<int32_t>(self->x + ux * kRetreatWay);
                g_walkY = static_cast<int32_t>(self->y + uy * kRetreatWay);
            }
            if (!g_retreatWalkAt)
            {
                LOG("AutoAttack: stepping back {} ({:.0f} tiles off, {} hostile not after it on that way)",
                    bestScore > 0.0 ? "the safest way (aggro weighed)" : "straight away",
                    std::hypot(g_walkX - self->x, g_walkY - self->y) / kTileSize, bestCrossed);
            }
            if (!Act::may(Act::Kind::Retreat))
            {
                g_retreatUntil = 0;
                return false;
            }
            sendWalk();
            g_retreatWalkAt = now;
        }
        return true;
    }

    // Which enemy to fight. Those attacking the hero, what it rides or a hireling, and those the player attacked
    // (engaged), and with Seek any other within Range; of them, weighing the situation: those close, coming at the
    // hero (by their own steps, in the world) or shooting at it from afar first, the badly wounded finished off, the
    // current one kept for a moment at least and then unless another is clearly better; one the hero gets no nearer
    // to is given up for a while. Loot is not the auto attack's: the player collects with A.
    // Arrows coming at the hero (the player, 2026-11-10: «el agente no identifica proyectiles, es bueno que lo haga
    // para conseguir esquivarlos»). Manolito, block U: cArrow3D (vtable 0x891AB4) lives in the object table, +0x1E4
    // bit 1 in flight, +0x204 its target, +0x208 the shooter; they fly straight. Seen live 2026-11-10: the world
    // position is the usual one at +0x1C/+0x20; the direction +0x1F4/+0x1F8 is in the game's axes, turned 45 degrees
    // from the world's (world = (dx + dy, dy - dx)), about 16 tiles a second. One whose line passes within a tile of
    // the hero, ahead of it within 15 tiles, is side-stepped: 2.5 tiles across its line, the side away from it first,
    // on walkable ground; once per arrow, at most every 1.2 s.
    // Punished when an arrow hits (the player, 2026-11-11: «castiga al agente cuando sea acertado por un proyectil»):
    // each arrow on its way at the hero is followed; one gone from the air within 5 tiles of it (16 tiles a second, a look every 0.2-0.3 s) while its health fell
    // is a hit, and each hit makes the dodge keener for the rest of the session: seen farther off, a wider line taken
    // for one coming at it, a longer step aside, a shorter wait between two.
    struct DodgeLearn
    {
        double reach = 15.0, line = 1.0, step = 2.5;    // tiles
        DWORD wait = 1200;                              // ms between two side-steps
        int hits = 0, dodged = 0;
    };
    DodgeLearn g_dodge;

    // Who shot at the hero lately, by its object index (an arrow's shooter at +0x208): the player, 2026-11-11: «el
    // agente ignora a los que le atacan de lejos, y son los que más molestan» (their aim is not always read).
    std::unordered_map<uint32_t, DWORD> g_shotBy;

    bool shotAtHero(uint32_t id, DWORD now)
    {
        const auto it = g_shotBy.find(id & 0xFFFF);
        return it != g_shotBy.end() && now - it->second < 8000;
    }

    void noteArrowHits(DWORD now, const cCreature* self, const uint8_t* const* table, size_t entries)
    {
        struct Seen
        {
            double t;   // tiles ahead along its line, last look
            DWORD at;
        };
        static std::unordered_map<uint32_t, Seen> s_coming;
        static int s_health = 0;
        int health = 0, maximum = 0;
        AimAssist::heroHealth(health, maximum);
        const bool fell = s_health && health < s_health;
        s_health = health;
        for (auto it = s_coming.begin(); it != s_coming.end();)
        {
            const uint8_t* o = it->first < entries ? table[it->first] : nullptr;
            const bool flying = o && *reinterpret_cast<const uint32_t*>(o) == 0x891AB4 &&
                                (*reinterpret_cast<const uint32_t*>(o + 0x1E4) & 1);
            if (flying && now - it->second.at < 3000)
            {
                ++it;
                continue;
            }
            if (!flying && fell && it->second.t < 5.0 && now - it->second.at < 600)   // 16 tiles a second: up to 5 between two looks
            {
                ++g_dodge.hits;
                g_dodge.reach = std::min(25.0, g_dodge.reach + 1.5);
                g_dodge.line = std::min(1.8, g_dodge.line + 0.1);
                g_dodge.step = std::min(4.0, g_dodge.step + 0.2);
                g_dodge.wait = std::max<DWORD>(500, g_dodge.wait - 100);
                LOG("AutoAttack: hit by arrow {:x} (hit {}, {} dodged): the dodge keener now (seen at {:.1f} tiles, line "
                    "{:.1f}, step {:.1f}, every {} ms)",
                    it->first, g_dodge.hits, g_dodge.dodged, g_dodge.reach, g_dodge.line, g_dodge.step, g_dodge.wait);
                Findings::note("arrow", self->x, self->y, "hit by an arrow (hit {})", g_dodge.hits);
            }
            it = s_coming.erase(it);
        }
        // The arrows on their way at the hero now.
        for (size_t i = 1; i < entries; ++i)
        {
            const uint8_t* o = table[i];
            if (!o || *reinterpret_cast<const uint32_t*>(o) != 0x891AB4 || !(*reinterpret_cast<const uint32_t*>(o + 0x1E4) & 1))
            {
                continue;
            }
            const float gx = *reinterpret_cast<const float*>(o + 0x1F4), gy = *reinterpret_cast<const float*>(o + 0x1F8);
            double dx = gx + gy, dy = gy - gx;
            const double len = std::hypot(dx, dy);
            if (len < 0.1)
            {
                continue;
            }
            dx /= len;
            dy /= len;
            const double wx = self->x - *reinterpret_cast<const int32_t*>(o + 0x1C);
            const double wy = self->y - *reinterpret_cast<const int32_t*>(o + 0x20);
            const double t = wx * dx + wy * dy;
            if (t > -1.0 * kTileSize && t < 25.0 * kTileSize && std::hypot(wx - t * dx, wy - t * dy) < 1.5 * kTileSize)
            {
                // Only an enemy's arrow (the code reviewer: the hero's own and its hirelings' were followed too, and a
                // fall of health by a blow counted as their hit).
                const uint32_t shooter = *reinterpret_cast<const uint32_t*>(o + 0x208) & 0xFFFF;
                cObjectManager* om = cObjectManager::instance();
                // The shooter by its index in the object table (+0x208 holds the index, not a full id).
                cObject* shot = shooter && shooter < entries ? reinterpret_cast<cObject*>(const_cast<uint8_t*>(table[shooter])) : nullptr;
                cCreature* from = shot ? shot->asCreature() : nullptr;
                cCreature* hero = om ? om->hero() : nullptr;
                if (!from || !hero || !hero->isEnemy(from))
                {
                    continue;
                }
                s_coming[static_cast<uint32_t>(i)] = {std::abs(t) / kTileSize, now};
                g_shotBy[shooter] = now;
            }
        }
    }

    bool dodgeArrow(DWORD now, const cCreature* self, uint32_t heroId)
    {
        static DWORD s_at = 0;
        static uint32_t s_lastArrow = 0;
        // Never through an art going out (the player, 2026-11-11: «esquivar los proyectiles está cancelando las
        // artes»): the main attack is an art too, cast by the game from the click, not by Tactics, so Tactics::busy did
        // not tell; the step would cut it short and its recharge lost. The art's blows first, the arrow taken.
        if (g_retreatUntil || CombatState::casting(self))
        {
            return false;
        }
        // Not a dodge every half second (the live log, 2026-11-11: 71 dodges in a fight against archers, the hero
        // hardly striking, dead): 1.5 s at least between two, none with an enemy in the melee (its blows first), and
        // none on the way to the one shooting (it is the answer).
        if (now - s_at < std::max<DWORD>(g_dodge.wait, 1500) || (g_meleeAt && now - g_meleeAt < 1500) ||
            (g_target && shotAtHero(g_target, now)))
        {
            return false;
        }
        const auto manager = *reinterpret_cast<const uint8_t* const*>(0xAD5C40);
        if (!manager)
        {
            return false;
        }
        const auto table = *reinterpret_cast<const uint8_t* const* const*>(manager + 4);
        const auto tableEnd = *reinterpret_cast<const uint8_t* const* const*>(manager + 8);
        if (!table || tableEnd <= table || tableEnd - table >= 0x40000)
        {
            return false;
        }
        const auto* sides = reinterpret_cast<const uint8_t*>(0x8EB548);
        const size_t entries = static_cast<size_t>(tableEnd - table);
        double bestT = 1e9, offX = 0.0, offY = 0.0, dirX = 0.0, dirY = 0.0;
        uint32_t arrow = 0;
        for (size_t i = 1; i < entries; ++i)
        {
            const uint8_t* o = table[i];
            if (!o || *reinterpret_cast<const uint32_t*>(o) != 0x891AB4 || !(*reinterpret_cast<const uint32_t*>(o + 0x1E4) & 1))
            {
                continue;
            }
            const uint32_t target = *reinterpret_cast<const uint32_t*>(o + 0x204);
            const uint32_t shooter = *reinterpret_cast<const uint32_t*>(o + 0x208) & 0xFFFF;
            bool hostile = target == heroId || target == self->id;
            if (!hostile && shooter && shooter < entries && table[shooter])
            {
                const uint32_t side = *reinterpret_cast<const uint32_t*>(table[shooter] + 0x1F0);
                hostile = side < 16 && side != 1 && sides[16 + side] == 0;
            }
            if (!hostile)
            {
                continue;
            }
            const float gx = *reinterpret_cast<const float*>(o + 0x1F4), gy = *reinterpret_cast<const float*>(o + 0x1F8);
            double dx = gx + gy, dy = gy - gx;
            const double len = std::hypot(dx, dy);
            if (len < 0.1)
            {
                continue;
            }
            dx /= len;
            dy /= len;
            const double wx = self->x - *reinterpret_cast<const int32_t*>(o + 0x1C);
            const double wy = self->y - *reinterpret_cast<const int32_t*>(o + 0x20);
            const double t = wx * dx + wy * dy;     // how far ahead along its line the hero stands
            if (t <= 0.0 || t > g_dodge.reach * kTileSize)
            {
                continue;
            }
            const double ox = wx - t * dx, oy = wy - t * dy;
            if (std::hypot(ox, oy) < g_dodge.line * kTileSize && t < bestT)
            {
                bestT = t;
                offX = ox;
                offY = oy;
                dirX = dx;
                dirY = dy;
                arrow = static_cast<uint32_t>(i);
            }
        }
        if (!arrow || arrow == s_lastArrow)
        {
            return false;
        }
        const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
        // Across its line: the side the hero already leans to first.
        double nx = -dirY, ny = dirX;
        if (offX * nx + offY * ny < 0.0)
        {
            nx = -nx;
            ny = -ny;
        }
        for (const double sign : {1.0, -1.0})
        {
            const int32_t px = static_cast<int32_t>(self->x + sign * nx * g_dodge.step * kTileSize);
            const int32_t py = static_cast<int32_t>(self->y + sign * ny * g_dodge.step * kTileSize);
            if (ClickWalk::walkable(layer, static_cast<int>(px / kTileSize), static_cast<int>(py / kTileSize)) == 0)
            {
                continue;
            }
            if (!Act::allowed(Act::Kind::Retreat, "side-step an arrow"))
            {
                return false;
            }
            s_at = now;
            s_lastArrow = arrow;
            ++g_dodge.dodged;
            LOG("AutoAttack: arrow {:x} coming ({:.1f} tiles off), side-stepping {} ({} dodged, {} hits)", arrow,
                bestT / kTileSize, sign > 0 ? "away from its line" : "the other way", g_dodge.dodged, g_dodge.hits);
            g_walkX = px;
            g_walkY = py;
            sendWalk();
            return true;
        }
        return false;
    }

    // ---- The way to a merchant for a hero too weak to cross a pack (the stuck solver, 2026-11-16, A7: a level 2 Dwarf with
    // one potion and 1 000 108 gold died 11 times in 35 min in two corridors on the way to the merchants, the same goblin
    // pack each life; the load put it back at the start of the same walk) ------------------------------------------------
    struct SeenFoe
    {
        DWORD at;
    };
    std::unordered_map<uint32_t, SeenFoe> g_foesSeen;       // enemies seen in the last 60 s
    struct DangerSpot
    {
        int tx, ty;
        DWORD at;
    };
    std::vector<DangerSpot> g_dangerSpots;                  // where a group of three or more was met on a fragile trip

    // Level 3 or under with one healing potion or none (the count known): the walk to a merchant is not to be fought through.
    bool fragileHero()
    {
        cObjectManager* objects = cObjectManager::instance();
        const cCreature* hero = objects ? objects->hero() : nullptr;
        return hero && Gear::healingLeft() >= 0 && Gear::healingLeft() <= 1 &&
               *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x3FE) <= 3;
    }

    // How many enemies seen in the last 60 s, alive, are within `tiles` of the hero; their middle (world units) in cx, cy.
    int groupWithin(const cCreature* self, double tiles, DWORD now, double& cx, double& cy)
    {
        cObjectManager* objects = cObjectManager::instance();
        int n = 0;
        cx = cy = 0.0;
        std::erase_if(g_foesSeen, [now](const auto& kv) { return now - kv.second.at > 60000; });
        for (const auto& [id, seen] : g_foesSeen)
        {
            const cCreature* c = objects ? objects->creature(id) : nullptr;
            if (c && c->health > 0 &&
                std::hypot(static_cast<double>(c->x - self->x), static_cast<double>(c->y - self->y)) < tiles * kTileSize)
            {
                ++n;
                cx += c->x;
                cy += c->y;
            }
        }
        if (n)
        {
            cx /= n;
            cy /= n;
        }
        return n;
    }

    // Within 30 tiles of a group met on a fragile trip in the last 10 min.
    bool nearDangerGroup(int tx, int ty)
    {
        const DWORD now = GetTickCount();
        std::erase_if(g_dangerSpots, [now](const DangerSpot& d) { return now - d.at > 600000; });
        for (const DangerSpot& d : g_dangerSpots)
        {
            if ((tx - d.tx) * (tx - d.tx) + (ty - d.ty) * (ty - d.ty) < 900)
            {
                return true;
            }
        }
        return false;
    }

    bool deadlyTile(int tx, int ty)
    {
        return AgentSave::nearDeathSpot(tx, ty) || nearDangerGroup(tx, ty);
    }

    // Whether the way from the hero to (toX, toY) (world units) crosses a place where the hero died lately or met a group:
    // the route net's trip when it has one for that goal, else the straight line, a point every 8 tiles; not within 25
    // tiles of where the hero stands (a load at the place itself would shut every way).
    bool deathOnTheWay(const cCreature* self, int32_t toX, int32_t toY, int layer)
    {
        const int hx = static_cast<int>(self->x / kTileSize), hy = static_cast<int>(self->y / kTileSize);
        static int s_hx, s_hy;
        s_hx = hx;
        s_hy = hy;
        if (RouteNet::tripPasses(layer, static_cast<int>(toX / kTileSize), static_cast<int>(toY / kTileSize), [](int tx, int ty) {
                return (tx - s_hx) * (tx - s_hx) + (ty - s_hy) * (ty - s_hy) > 625 && deadlyTile(tx, ty);
            }))
        {
            return true;
        }
        const double dx = static_cast<double>(toX - self->x) / kTileSize, dy = static_cast<double>(toY - self->y) / kTileSize;
        const double length = std::hypot(dx, dy);
        for (double t = 8.0; t < length; t += 8.0)
        {
            const int tx = hx + static_cast<int>(dx * t / length), ty = hy + static_cast<int>(dy * t / length);
            if ((tx - hx) * (tx - hx) + (ty - hy) * (ty - hy) > 625 && deadlyTile(tx, ty))
            {
                return true;
            }
        }
        return false;
    }

    bool decide(DWORD now, Choice& out)
    {
        float hx, hy;
        if (!AimAssist::hero(hx, hy))
        {
            return false;
        }
        int health = 0, maximum = 0;
        if (AimAssist::heroHealth(health, maximum))
        {
            if (g_lastHealth && health < g_lastHealth)
            {
                g_hurtAt = now;
            }
            g_lastHealth = health;
        }
        const bool hurt = g_hurtAt && static_cast<int>(now - g_hurtAt) < static_cast<int>(kHurtMs);

        cObjectManager* objects = cObjectManager::instance();
        cEngine* engine = FrameHooks::engine();
        cCreature* heroObject = objects ? objects->hero() : nullptr;
        cCreature* self = objects && engine ? objects->creature(engine->controlled) : nullptr;
        if (!objects || !engine || !heroObject || !self)
        {
            return false;
        }
        const uint32_t heroId = heroObject->id;
        const uint32_t selfId = engine->controlled;
        // The map memory: fights count as ground seen too (layer at the creature's +0x24).
        {
            const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
            noteTrail(self, layer);
            MapMemory::visit(layer, self->x, self->y);
            MapMemory::wantGround(layer, self->x, self->y, hx, hy);
            MapMemory::save(now, 300000);
            // The reach known in the fights too (at a new game the first fight came before any fill).
            Whereabouts::update(layer, static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize));
        }

        const float range = static_cast<float>(Config::autoAttack.range);
        const float melee = range * 0.45f;
        // Shut in (a yard behind its fence): an enemy on no tile the hero can walk to is out of reach, whatever its
        // aggro. Seen live (2026-11-10): the Dark Elf and the Wood Elf at their start chased the enemies beyond the
        // fence by turns, 4 s each, for up to 3 minutes; their aggro made them strike, so the focus kept switching.
        // A fence, water or a wall on the straight line from the hero to `o` (the walkable test every half tile).
        const auto lineBlocked = [&](const cObject* o) {
            const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
            const double sx = self->x / kTileSize, sy = self->y / kTileSize;
            const double ex = o->x / kTileSize, ey = o->y / kTileSize;
            const int steps = static_cast<int>(std::ceil(std::max(std::abs(ex - sx), std::abs(ey - sy)) * 2.0));
            for (int k = 2; k < steps - 1; ++k)
            {
                const double t = static_cast<double>(k) / steps;
                if (ClickWalk::walkable(layer, static_cast<int>(sx + (ex - sx) * t), static_cast<int>(sy + (ey - sy) * t)) == 0)
                {
                    return true;
                }
            }
            return false;
        };
        const auto walledOff = [&](const cObject* o, float d) {
            // Next to the hero, nothing between. Within the melee reach too a fence counts (the player, 2026-11-11:
            // the Seraphim's spear reaching a goblin over a fence, «acaba nunca pegándole»).
            if (!o || d < 1.5f * static_cast<float>(kTileSize))
            {
                return false;
            }
            if (!Whereabouts::area().shutIn)
            {
                if (d < melee)
                {
                    return lineBlocked(o);
                }
                // Across water or a cliff (the player, 2026-11-11: «no detecta colisión ni casilla no pisable», the
                // Vampiress at archers over a river): no walk there, or one far longer than the line to it.
                const float way = MapMemory::routeTiles(*(reinterpret_cast<const uint8_t*>(self) + 0x24), static_cast<int>(self->x / kTileSize),
                                                        static_cast<int>(self->y / kTileSize),
                                                        static_cast<int>(o->x / kTileSize), static_cast<int>(o->y / kTileSize));
                const float line = d / static_cast<float>(kTileSize);
                if (way == -2.0f || (way >= 0.0f && way > line * 3.0f + 12.0f))
                {
                    return true;
                }
                // Seen only over walkable ground (the player, 2026-11-11: «que la visión del agente se anulara al
                // intentar pasar por una casilla no pisable»): a fence, water or a wall on the straight line hides it,
                // unless a short way round is known.
                return lineBlocked(o) && !(way >= 0.0f && way <= line * 1.5f + 5.0f);
            }
            if (d < melee)
            {
                return false;
            }
            const int tx = static_cast<int>(o->x / kTileSize), ty = static_cast<int>(o->y / kTileSize);
            for (int dy = -1; dy <= 1; ++dy)
            {
                for (int dx = -1; dx <= 1; ++dx)
                {
                    if (Whereabouts::reachable(tx + dx, ty + dy) != 0)
                    {
                        return false;   // reached, or unknown: kept
                    }
                }
            }
            return true;
        };
        noteHirelings(now, heroObject, range * 2.0f);
        AimAssist::Foe foes[kMaxFoes];
        const int count = AimAssist::enemies(range * kEngagedReach, foes, kMaxFoes);
        for (auto it = g_unreachable.begin(); it != g_unreachable.end();)
        {
            if (static_cast<int>(now - it->second) >= 0)
            {
                g_unreachableAt.erase(it->first);
                it = g_unreachable.erase(it);
            }
            else
            {
                ++it;
            }
        }

        // The current target: no nearer in a while without a blow, it is out of reach (across water, up a wall).
        float currentDistance = -1.0f;
        int currentHealth = -1;
        bool inMelee = false;
        for (int i = 0; i < count; ++i)
        {
            const float dx = foes[i].x - hx, dy = foes[i].y - hy;
            const float d = std::sqrt(dx * dx + dy * dy);
            if (foes[i].id == g_target)
            {
                currentDistance = d;
                currentHealth = foes[i].health;
            }
            if (d < melee)
            {
                inMelee = true;
            }
        }
        // No looks for a while (an art went on, the game paused): the time without getting nearer starts again.
        if (now - g_lastLookAt > 1500)
        {
            g_targetBestAt = now;
        }
        g_lastLookAt = now;
        if (g_target && !g_looting && currentDistance >= 0.0f)
        {
            // Striking or casting is progress only if it tells (the player, 2026-11-11: the Seraphim casting her arts
            // at one behind a fence, «did nothing seen» over and over, never left): its health must go down.
            static uint32_t s_healthOf = 0;
            static int s_healthBest = 0;
            if (s_healthOf != g_target || currentHealth > s_healthBest)
            {
                s_healthOf = g_target;
                s_healthBest = currentHealth;
            }
            const bool hurtIt = currentHealth >= 0 && currentHealth < s_healthBest;
            if (hurtIt)
            {
                s_healthBest = currentHealth;
                g_lastHurtAt = now;
            }
            const bool striking = CombatState::action(self) == CombatState::Fighting || CombatState::casting(self);
            // A target never hurt in 12 s of being the target, beyond the melee (the stuck solver, 2026-11-16, A6 on the
            // river's bank: a goblin warrior of level 9 across the water, fights of 4-30 s every 20 s for 20 min,
            // «0 killed, 0 experience», its health 338 of 338 each time; the distance went up and down by more than a
            // tenth along the bank, and each time that started the «no nearer» clock again).
            static uint32_t s_untouchedOf = 0;
            static DWORD s_untouchedSince = 0;
            if (s_untouchedOf != g_target || hurtIt)
            {
                s_untouchedOf = g_target;
                s_untouchedSince = now;
            }
            const bool untouched12 = now - s_untouchedSince > 12000 && currentDistance > melee;
            // Within the melee too: 25 s at its side, striking and casting, its health never down (the owner,
            // 2026-11-24, «atasco de A1»: the Seraphim in a cave casting at a level 38 thief by her side, «art 13 did
            // nothing seen» every 2 s for minutes; casting there counted as progress, so she never left it).
            static uint32_t s_closeUntouchedOf = 0;
            static DWORD s_closeUntouchedSince = 0;
            if (s_closeUntouchedOf != g_target || hurtIt || currentDistance > melee)
            {
                s_closeUntouchedOf = g_target;
                s_closeUntouchedSince = now;
            }
            const bool untouchedClose = now - s_closeUntouchedSince > 25000;
            // Striking over a fence (a spear's reach) is no progress: only its health going down is.
            const cObject* targetObject = objects && self ? objects->object(g_target) : nullptr;
            const bool fencedOff = targetObject && currentDistance >= 1.5f * static_cast<float>(kTileSize) &&
                                   lineBlocked(targetObject);
            const bool progress =
                !untouchedClose &&
                (g_targetBest <= 0.0f || currentDistance < g_targetBest * 0.9f || currentDistance < range * 0.3f ||
                 hurtIt || (striking && currentDistance < melee && !fencedOff) ||
                 // A step back to shoot from afar is no failure to reach it (the stuck solver, 2026-11-14: A1 with a
                 // ranged weapon, «keeping the distance» and the enemy it fought given up as out of reach).
                 (g_keptDistanceAt && now - g_keptDistanceAt < 3000));
            if (progress)
            {
                g_targetBest = g_targetBest > 0.0f ? std::min(g_targetBest, currentDistance) : currentDistance;
                g_targetBestAt = now;
            }
            else if (untouchedClose || now - g_targetBestAt > kStuckMs || untouched12)
            {
                if (untouchedClose)
                {
                    LOG("AutoAttack: {:x} by the hero's side 25 s, struck and cast at, its health never down: left", g_target);
                }
                // Each time again the same one, three times as long (20 s, 1 min, 3 min, then 10 min). Seen live
                // (2026-11-10): an enemy across the water taken again every 20 s for three hours, the 4 s chase
                // each time starting the stuck guard's watch again, so the hero never moved on.
                const int times = ++g_unreachableTimes[g_target];
                DWORD wait = kUnreachableMs;
                for (int t = 1; t < times && wait < 600000; ++t)
                {
                    wait *= 3;
                }
                wait = std::min<DWORD>(wait, 600000);
                LOG("AutoAttack: no nearer to {:x} in {} s ({:.0f} px away): out of reach, left for {} s (time {})",
                    g_target, kStuckMs / 1000, currentDistance, wait / 1000, times);
                if (times <= 2)
                {
                    Findings::note("unreachable", self->x, self->y, "enemy {:x} no nearer in {} s at {:.0f} px",
                                   g_target, kStuckMs / 1000, currentDistance);
                }
                g_unreachable[g_target] = now + wait;
                g_unreachableAt[g_target] = currentDistance;
                if (targetObject)
                {
                    noteUnreachableSpot(g_target, static_cast<int>(targetObject->x / kTileSize),
                                        static_cast<int>(targetObject->y / kTileSize), now);
                }
                g_playerTargets.erase(g_target);
                g_target = 0;
            }
        }

        std::unordered_map<uint32_t, float> distances;
        std::vector<CombatLearn::Foe> learnFoes;
        std::unordered_map<uint32_t, std::pair<int32_t, int32_t>> world;
        std::unordered_map<uint32_t, int> farAim;
        bool threat = hurt;
        float enemyCost = 0.0f;
        uint32_t enemy = 0;
        bool currentCandidate = false;      // the enemy fought now is still there to fight
        bool enemyEngaged = false, currentEngaged = false;
        float currentLeft = 1.0f;           // the current one's health left (a share of its maximum)
        // What an ordinary enemy's maximum health is here: one well above hits harder (a strong one).
        int typical = 0;
        {
            std::vector<int> maxima;
            for (int i = 0; i < count; ++i)
            {
                if (foes[i].maxHealth > 0)
                {
                    maxima.push_back(foes[i].maxHealth);
                }
            }
            if (!maxima.empty())
            {
                std::nth_element(maxima.begin(), maxima.begin() + maxima.size() / 2, maxima.end());
                typical = maxima[maxima.size() / 2];
            }
        }
        // How many have aggro on the hero, logged when it changes (after the loop, as it leaves this scope).
        int aggroCount = 0;
        struct AggroTell
        {
            const int& n;
            ~AggroTell()
            {
                static int s_told = 0;
                if (n != s_told)
                {
                    if (n > s_told)
                    {
                        LOG("AutoAttack: {} enemies with aggro on the hero", n);
                    }
                    s_told = n;
                }
            }
        } aggroTell{aggroCount};
        for (int i = 0; i < count; ++i)
        {
            const AimAssist::Foe& f = foes[i];
            const float dx = f.x - hx, dy = f.y - hy;
            const float d = std::sqrt(dx * dx + dy * dy);
            distances[f.id] = d;
            cObject* foeObject = objects->object(f.id);
            if (foeObject)
            {
                world[f.id] = {foeObject->x, foeObject->y};
                if (f.health > 0)
                {
                    g_foesSeen[f.id] = {now};
                }
            }
            const uint32_t aim = foeObject ? aimOf(objects, foeObject) : 0;
            // Striking or aiming at the hero, or with aggro on it (coming, a blow or two off): a threat either way.
            const bool aggro = aggroOnHero(foeObject, heroId, selfId);
            const bool shooting = shotAtHero(f.id, GetTickCount());     // its arrows at the hero lately
            const bool atHero = (aim && (aim == heroId || aim == selfId)) || aggro || shooting;
            aggroCount += aggro ? 1 : 0;
            const bool atHireling = aim && !atHero && isHireling(aim);
            const bool engagedFoe = g_playerTargets.count(f.id) || atHero || atHireling;
            const bool current = f.id == g_target;
            {
                const auto looks = g_farAimLooks.find(f.id);
                // Within its aggro reach (600 world units, a margin on top) it joins the fight in moments: counted by
                // the forecast (the player, 2026-11-10: «no consigue identificar cuántos enemigos tiene alrededor»;
                // 8 around, the forecast took the 2 striking: 104 % foreseen, 201 % lost).
                const bool soon = foeObject && std::hypot(static_cast<double>(foeObject->x - self->x),
                                                          static_cast<double>(foeObject->y - self->y)) < 750.0;
                learnFoes.push_back({f.id, f.health, f.maxHealth, atHero, atHireling,
                                     looks != g_farAimLooks.end() && looks->second >= 3, soon});
            }
            // A place where three enemies were given up lately: those in it are not sought from afar either.
            if (d > melee && inVetoedCircle(static_cast<int>(f.x / kTileSize), static_cast<int>(f.y / kTileSize), now, 300000))
            {
                continue;
            }
            // Given up on: only if it comes clearly nearer than it was then. Seen live (2026-11-09): one 122 px off
            // behind a graveyard's fence, within the melee look, was taken again at once, for minutes on end.
            if (const auto gone = g_unreachableAt.find(f.id);
                g_unreachable.count(f.id) && d > std::min(melee, gone != g_unreachableAt.end() ? gone->second * 0.6f : melee))
            {
                continue;
            }
            // Across the water: inside the flood fill's window and not reached by it, and not at the hero or the hirelings
            // (the stuck solver, 2026-11-16, A6: goblin warriors of level 9 on the far bank of the river, 7-13 tiles off,
            // 1% of health to lose, taken for a fight every 20 s for 12 min: «fight over, 1-7 s, 0 killed, 0 experience»).
            if (!engagedFoe && !current && d > melee &&
                Whereabouts::reachable(static_cast<int>(f.x / kTileSize), static_cast<int>(f.y / kTileSize)) == 0)
            {
                continue;
            }
            // Careful after dying again and again from the same save (the live verifier, 2026-11-11: A1 and A3 loaded
            // the same game a dozen times, the potions drunk and dead at the same spot each time): only those not
            // above the hero's level are sought; a stronger one only once it strikes the hero in the melee.
            if (AgentSave::deathsSinceSave() >= 2 && foeObject && foeObject->asCreature() && heroObject && !current &&
                !(atHero && d <= melee) &&
                scaledLevel(foeObject) > scaledLevel(heroObject))
            {
                continue;
            }
            // C1 and C2 (docs/Criterios.md, 2026-11-12: enemies two levels or more above the hero gave 67 % of the
            // near-deaths for 4 % of the experience; packs 87 % with them): never sought, only fought once they strike
            // in the melee. Two levels above at most (one at levels 1-4); no pack of 5 above the hero, 10 at levels
            // 1-4, 20 ever (the pack: the same leader, obj +0x24D, within 600 u of it).
            // Never one already at the hero, however far (the code reviewer: an archer above the hero shooting from
            // afar was never answered).
            if (foeObject && foeObject->asCreature() && heroObject && !current && !engagedFoe)
            {
                const auto lv = [](const cObject* o) { return scaledLevel(o); };
                const int fl = lv(foeObject), hl = lv(heroObject);
                if (fl >= hl + 2 || (hl <= 4 && fl >= hl + 1))
                {
                    continue;
                }
                const int32_t leader = *reinterpret_cast<const int32_t*>(reinterpret_cast<const uint8_t*>(foeObject) + 0x24D);
                if (leader > 0)
                {
                    int pack = 0;
                    for (int j = 0; j < count; ++j)
                    {
                        const cObject* o = objects->object(foes[j].id);
                        if (o && foes[j].health > 0 &&
                            *reinterpret_cast<const int32_t*>(reinterpret_cast<const uint8_t*>(o) + 0x24D) == leader &&
                            std::hypot(static_cast<double>(o->x - foeObject->x), static_cast<double>(o->y - foeObject->y)) < 600.0)
                        {
                            ++pack;
                        }
                    }
                    if ((pack >= 5 && fl > hl) || (pack >= 10 && hl <= 4) || pack >= 20)
                    {
                        continue;
                    }
                }
            }
            if (walledOff(foeObject, d))
            {
                continue;
            }
            // Engaged ones within the look's reach (kEngagedReach Range): an archer shooting from afar is gone after
            // too. Seeking fights, any other enemy within Range as well. The current one while it is engaged or
            // within 1.5 Range.
            // On the way to the merchant with the backpack full, or on a trip to a quest: only those that attack (no
            // fight sought). Focus (the player's wish, 2026-11-10): a trip decided on is gone through to the end;
            // only danger (one that attacks) stops it on the way.
            // Farming is seeking the enemies (the intent); elsewhere only as the setting says, never on a trip.
        // C8 (docs/Criterios.md): no fight of its choosing under 60 % of health; those that come are fought all the same.
        const bool fitToSeek = !heroObject || heroObject->maxHealth <= 0 || heroObject->health * 100 >= heroObject->maxHealth * 60;
        const bool questSeek = g_questSeekUntil && static_cast<int>(GetTickCount() - g_questSeekUntil) < 0;
        const bool seek = (Config::autoAttack.seek || g_intent == Intent::Farm || questSeek) && !Gear::wantsShop() &&
                          !g_questTravel && fitToSeek && entryOpen(now);
            if (current ? !engagedFoe && d > range * 1.5f : !engagedFoe && (!seek || d > range))
            {
                continue;
            }
            // Aiming at the hero from beyond the melee look after look: it shoots (archer, caster).
            int farLooks = 0;
            if (atHero && d > melee)
            {
                const auto it = g_farAimLooks.find(f.id);
                farLooks = (it != g_farAimLooks.end() ? it->second : 0) + 1;
                farAim[f.id] = farLooks;
            }
            // Coming at the hero by its own steps (in the world: the hero's own walk says nothing about it).
            bool closing = false;
            const auto last = g_lastWorld.find(f.id);
            if (foeObject && last != g_lastWorld.end() && d >= melee)
            {
                const double mx = foeObject->x - last->second.first, my = foeObject->y - last->second.second;
                const double tx = self->x - foeObject->x, ty = self->y - foeObject->y;
                const double tl = std::sqrt(tx * tx + ty * ty);
                closing = tl > 1.0 && (mx * tx + my * ty) / tl > 0.5 * kTileSize;
            }
            if (d < melee || closing)
            {
                threat = true;
            }
            const Mind::Plan& cp = Mind::plan();
            float cost = d;
            if (closing)
            {
                cost *= cp.closing;     // the one coming at the hero first
            }
            if (farLooks >= 3 && !inMelee)
            {
                cost *= cp.sniper;      // shooting at the hero from afar, nobody in the melee: go for it
            }
            if (shooting && d > melee)
            {
                // Its arrows seen at the hero: the shooter before those about, unless one in the melee hits hard
                // (the strong-foe pull below); a player goes for the archer that keeps hitting.
                cost *= inMelee ? cp.shooterInMelee : cp.shooterAlone;
            }
            // The threat first: who strikes the hero (the strong ones before the weak), then who strikes the
            // hireling (it dies fast alone); a weak one standing by waits.
            // Strong: well above the ordinary health here, or learned to hit far harder than those around.
            const float hardness = CombatLearn::relativeDanger(f.id);
            const bool strongFoe = (typical > 0 && f.maxHealth * 2 >= typical * 3) || hardness >= 1.6f;
            if (atHero && d < melee)
            {
                cost *= strongFoe ? cp.atHeroStrong : cp.atHero;
            }
            if (atHireling)
            {
                cost *= strongFoe ? cp.atHirelingStrong : cp.atHireling;
            }
            if ((atHero || atHireling || current) && f.maxHealth > 0)
            {
                // Among those in the fight, the less health left, the sooner it is down (from x0.7 at its last breath
                // to x1 unhurt): one focused down instead of blows spread. A weak one standing by gets no such pull.
                const float left = std::clamp(static_cast<float>(f.health) / static_cast<float>(f.maxHealth), 0.0f, 1.0f);
                cost *= cp.woundedFloor + (1.0f - cp.woundedFloor) * left;
            }
            const bool striking = atHero || atHireling;
            if (striking)
            {
                // Focus fire (the player, 2026-11-10: «parece que deja los más peligrosos para el final»): of those
                // striking, the one that takes the most of the hero's health for the blows it still needs goes down
                // first: how hard it hits (learned, against an ordinary one) weighed above its health left (against an
                // ordinary one's), so a hard hitter is not left for last because it has more health.
                const float healthShare =
                    typical > 0 ? std::clamp(static_cast<float>(f.health) / static_cast<float>(typical), 0.15f, 4.0f) : 1.0f;
                const float priority =
                    std::clamp(std::pow(hardness, cp.hardnessPower) / std::sqrt(healthShare), 0.3f, 6.0f);
                cost /= priority;
            }
            // The forecast's kill order (the least health lost: the highest blows per second needed to kill it, a
            // summoner weighed with what it brings): its first one pulled ahead among several.
            if (CombatLearn::forecast().foes > 1 && CombatLearn::killRank(f.id) == 0)
            {
                cost *= cp.killFirst;
            }
            if (current)
            {
                // Stay on it: a player finishes the enemy they fight, unless another is far nearer; a new one at least
                // a moment (no back and forth).
                cost *= cp.stay;
                currentCandidate = true;
                currentEngaged = striking;
                currentLeft = f.maxHealth > 0 ? static_cast<float>(f.health) / static_cast<float>(f.maxHealth) : 1.0f;
            }
            // One that strikes always before one that does not, whatever the distance.
            if (!enemy || (striking && !enemyEngaged) || (striking == enemyEngaged && cost < enemyCost))
            {
                enemy = f.id;
                enemyCost = cost;
                enemyEngaged = striking;
            }
        }
        // Hurt with nobody in the melee and no enemy seen striking (an archer's or caster's aim is not always read):
        // the nearest enemy within the look's reach is taken for the shooter and gone for. Seen live (2026-11-09):
        // the hero stood taking arrows until it died.
        if (inMelee)
        {
            g_meleeAt = now;
        }
        // Only with nobody in the melee for 3 s (a blow from one just killed is no shot from afar) and within twice
        // the Range (the nearest at any distance was a guess: the review of the findings, 2026-11-09).
        if (hurt && !inMelee && !enemyEngaged && (!g_meleeAt || now - g_meleeAt > 3000))
        {
            float best = 0.0f;
            uint32_t shooter = 0;
            for (int i = 0; i < count; ++i)
            {
                const auto d = distances.find(foes[i].id);
                if (d == distances.end() || d->second > range * 2.0f || (g_unreachable.count(foes[i].id) && d->second > melee) ||
                    walledOff(objects->object(foes[i].id), d->second))
                {
                    continue;
                }
                if (!shooter || d->second < best)
                {
                    shooter = foes[i].id;
                    best = d->second;
                }
            }
            if (shooter)
            {
                if (shooter != g_target && shooter != g_lastShooter)
                {
                    LOG("AutoAttack: hurt with nobody close: {:x} at {:.0f} px taken for the shooter", shooter, best);
                    Findings::note("shooter", self->x, self->y, "hurt with nobody close: {:x} at {:.0f} px taken for the shooter",
                                   shooter, best);
                }
                g_lastShooter = shooter;
                enemy = shooter;
                enemyEngaged = true;
                threat = true;
            }
        }
        // Hurt again and again with no enemy to answer (none seen, or all out of reach): never stand there. Seen live
        // (2026-11-09): hit every 3.5 s from somewhere out of reach, the hero went from the loot to the shooter and
        // back until it died. Off 10 tiles away from the enemies seen (anywhere when none), the agent quiet meanwhile.
        // With no enemy seen too (seen live, 2026-11-10, three Daemon starts): drained to death by the chest at her
        // arrival, by something the look does not list. A lone hit (her arrival's) is not enough: two within 12 s.
        if (hurt && !inMelee && !enemyEngaged && g_hurtAt == now)
        {
            g_unseenHits = static_cast<int>(now - g_unseenHitAt) < 12000 ? g_unseenHits + 1 : 1;
            g_unseenHitAt = now;
            if (g_unseenHits >= 2)
            {
                double cx = 0.0, cy = 0.0;
                int seen = 0;
                for (int i = 0; i < count; ++i)
                {
                    if (const cObject* o = objects->object(foes[i].id))
                    {
                        cx += o->x;
                        cy += o->y;
                        ++seen;
                    }
                }
                double ax = seen ? self->x - cx / seen : std::cos(now * 0.001), ay = seen ? self->y - cy / seen : std::sin(now * 0.001);
                const double len = std::sqrt(ax * ax + ay * ay);
                ax = len > 1.0 ? ax / len : 1.0;
                ay = len > 1.0 ? ay / len : 0.0;
                // Hurt there again within 10 minutes (the analyst, 2026-11-10: three times on the same two tiles, the
                // goals bringing the hero back): farther off each time, 10, 25, then 40 tiles.
                static int32_t s_spotX = 0, s_spotY = 0;
                static DWORD s_spotAt = 0;
                static int s_spotTimes = 0;
                const bool again = s_spotAt && now - s_spotAt < 600000 && std::abs(self->x - s_spotX) < 8 * kTileSize &&
                                   std::abs(self->y - s_spotY) < 8 * kTileSize;
                s_spotTimes = again ? s_spotTimes + 1 : 1;
                s_spotX = self->x;
                s_spotY = self->y;
                s_spotAt = now;
                g_unseenSpotX = self->x;
                g_unseenSpotY = self->y;
                g_unseenSpotAt = now;
                const int tiles = s_spotTimes >= 3 ? 40 : s_spotTimes == 2 ? 25 : 10;
                g_walkX = static_cast<int32_t>(self->x + ax * tiles * kTileSize);
                g_walkY = static_cast<int32_t>(self->y + ay * tiles * kTileSize);
                sendWalk();
                g_quietUntil = now + 4000 + 1500 * (tiles / 10);
                g_unseenHits = 0;
                LOG("AutoAttack: hurt again with no enemy to answer ({} seen): off {} tiles away (time {} here)", seen,
                    tiles, s_spotTimes);
                Findings::note("unseen-hit", self->x, self->y, "hurt twice in 12 s with no enemy to answer ({} seen, health {} of {})",
                               seen, health, maximum);
                return false;
            }
        }
        // Focus (the player's wish, 2026-11-10): the enemy taken is fought to the end (down, gone, or out of reach);
        // only danger changes it: another one strikes the hero (or a hireling) while this one does not.
        if (currentCandidate && g_target && enemy != g_target)
        {
            if (enemyEngaged && !currentEngaged)
            {
                LOG("AutoAttack: focus: {:x} left for {:x}, which strikes (danger)", g_target, enemy);
            }
            else if (enemyEngaged && currentEngaged && currentLeft > 0.3f)
            {
                // Both strike: the other came out well ahead though the current one is kept at 0.4 of its cost (it
                // hits far harder for the health it has left); the current one is kept when nearly down.
                LOG("AutoAttack: focus: {:x} left for {:x}, far more dangerous ({:.0f} % of its health left on {:x})",
                    g_target, enemy, currentLeft * 100.0f, g_target);
            }
            else
            {
                enemy = g_target;
            }
        }
        CombatLearn::observe({now, heroObject, self, learnFoes.data(), static_cast<int>(learnFoes.size()),
                              g_hirelings.data(), static_cast<int>(g_hirelings.size())});
        g_lastDistance = std::move(distances);
        g_lastWorld = std::move(world);
        g_farAimLooks = std::move(farAim);

        bool chosen = false;
        g_lootInstead = false;
        // Loot before a fight only when the fight is a new decision: one under way is finished first (focus).
        if (enemy && enemy != g_target && Config::autoAttack.pickup && Config::autoAttack.lootInFight)
        {
            AimAssist::Target loot;
            const auto it = distances.find(enemy);
            if (it != distances.end() &&
                AimAssist::findObject(static_cast<float>(Config::autoAttack.lootRange), &acceptLoot, nullptr, loot))
            {
                // Nobody strikes the hero and nothing hurts it: all the loot about first, the fight sought after it
                // (the player's wish, 2026-11-09: never a fight picked while loot lies there). Attacked: loot first
                // with no danger of dying (60 % of health or more, not being hurt), one piece at a time; in danger
                // only loot nearer than the enemy.
                const float lootDistance = std::hypot(loot.x - hx, loot.y - hy);
                const bool calm = !enemyEngaged && !hurt;
                const bool safe = maximum > 0 && health * 10 >= maximum * 6 && !hurt;
                // Mounted, loot is taken slowly (the player, 2026-11-11): left on the ground while enemies strike, all of
                // it gathered once the fight is over («mapea los objetos del suelo para recoger después de batallar»).
                const bool saddle = HeroProfile::current().mounted;
                if (calm || (!saddle && (safe || lootDistance < it->second)))
                {
                    LOG("AutoAttack: loot {:x} first ({:.0f} px; enemy {:x} at {:.0f} px; {})", loot.id, lootDistance,
                        enemy, it->second, calm ? "nobody attacks" : safe ? "no danger" : "nearer");
                    g_lootInstead = true;
                    g_lootInsteadAll = calm;
                    enemy = 0;
                }
            }
        }
        if (enemy)
        {
            out = {enemy, threat};
            chosen = true;
        }
        // The radar on the agent's map: the enemies seen, the one fought, the hirelings, and where it heads.
        MapMemory::beginRadar();
        for (const auto& [id, at] : g_lastWorld)
        {
            MapMemory::addBlip(id == enemy ? MapMemory::Blip::Target : MapMemory::Blip::Enemy, at.first, at.second);
        }
        for (uint32_t id : g_hirelings)
        {
            if (cObject* h = objects->object(id))
            {
                MapMemory::addBlip(MapMemory::Blip::Hireling, h->x, h->y);
            }
        }
        radarLoot();
        MapMemory::endRadar();
        {
            const auto it = chosen ? g_lastWorld.find(enemy) : g_lastWorld.end();
            if (it != g_lastWorld.end())
            {
                MapMemory::setRoute(true, it->second.first, it->second.second);
            }
            else
            {
                MapMemory::setRoute(g_roamAt != 0, g_walkX, g_walkY);
            }
        }

        // Combat arts and consumables, on the same look: at the enemy the hero fights now.
        Tactics::Situation situation;
        situation.now = now;
        situation.health = health;
        situation.maxHealth = maximum;
        situation.hurt = hurt;
        situation.threat = threat;
        situation.target = g_target && !g_looting && g_lastDistance.count(g_target) ? g_target : (chosen ? out.id : 0);
        situation.foes = foes;
        situation.count = count;
        situation.hx = hx;
        situation.hy = hy;
        // The arrows seen every frame, through arts and retreats too (who shoots, and the hits for the dodge's
        // learning), the dodge itself only when free.
        if (const auto m = *reinterpret_cast<const uint8_t* const*>(0xAD5C40))
        {
            const auto tb = *reinterpret_cast<const uint8_t* const* const*>(m + 4);
            const auto te = *reinterpret_cast<const uint8_t* const* const*>(m + 8);
            if (tb && te > tb && te - tb < 0x40000)
            {
                noteArrowHits(now, self, tb, static_cast<size_t>(te - tb));
            }
        }
        // Low on health with no potion: step back instead (unless an art is under way); no arts meanwhile.
        if (!Tactics::busy(now) && retreat(now, self, health, maximum, foes, count, hx, hy, range, objects))
        {
            return false;
        }
        if (!Tactics::busy(now) && dodgeArrow(now, self, objects->hero() ? objects->hero()->id : self->id))
        {
            return false;
        }
        situation.range = range;
        situation.hirelings = g_hirelings.data();
        situation.hirelingCount = static_cast<int>(g_hirelings.size());
        Gear::setHirelings(situation.hirelingCount);
        Tactics::think(situation);
        return chosen;
    }

    // Seeking fights with none around: the hero goes looking, as a player farming would. After a few quiet seconds (and
    // with most of its health back) it walks on in one direction a step (2 tiles) at a time, turning when it gets no further, and
    // back toward where it began once it strays too far from there. Any enemy or loot seen ends it.
    constexpr DWORD kRoamQuietMs = 4000;
    constexpr DWORD kRoamStepMs = 500;       // at least this between steps
    constexpr DWORD kRoamStepMaxMs = 4000;   // at most this on one step
    constexpr double kRoamLeash = 60 * kTileSize;
    DWORD g_quietSince = 0;
    double g_roamAngle = 0.0;
    int32_t g_roamFromX = 0, g_roamFromY = 0;   // the hero at the last walk order
    int32_t g_homeX = 0, g_homeY = 0;
    bool g_homeSet = false;
    int g_roamStuck = 0;    // walk orders in a row that got the hero no further
    int g_roamLayer = -1;
    int g_roamSteps = 0;    // steps since the way was chosen
    constexpr size_t kLayer = 0x24;     // a creature's layer: the surface, a dungeon, an interior

    // The quest journal (seen live, 2026-11-09): a std::vector of 0x174-byte records at [0xAAD3A4]..[0xAAD3A8]
    // (the quest manager 0xAACF80 +0x424): +0 kind (3 main, 4 side), +4 state (1-2 under way, 100 done, 101
    // failed), +0x14 the target object's id (a creature to speak to, or -1), +0x18/+0x1C the target's tile, +0x20
    // its radius in world units (a zone: inside it the hero is there), +0x24/+0x28 title and objective text keys.
    //
    // The quest book (the player's wish, 2026-11-09: the agent knows the quests under way, those not done, those to
    // take, and goes for the nearest objective): every quest under way, every creature offering a quest ("?!") or
    // waiting for a report ("!") the hero can take now, ordered by distance. The agent goes for the nearest it can
    // reach; one it found no way to is left a while (travel's block) and the next one taken.
    enum class GoalKind { Journal, Offer, Report, Giver };
    struct QuestGoal
    {
        GoalKind kind;
        bool main = false;
        int32_t x = 0, y = 0;       // world
        double radius = 0.0;
        uint32_t who = 0;           // creature to speak to (or -1)
        uint32_t titleKey = 0, objectiveKey = 0;
        int32_t number = 0;         // the quest's number (record +0x08), journal goals only
        int tier = 0;               // 2 a deadline running, 1 before it is lost, 0 normal, -1 last
        int32_t minutesLeft = -1;   // game minutes to its deadline, -1 none
        double distance = 0.0;
        bool blocked = false;
        int rank = 0;               // its place in kQuestOrder (the campaign's order), after the list if not in it
        double way = 0.0;           // the way's length to it (world units), with none of the weights on distance
        bool band = false;          // in the hero's level band and not chained after an undone one (questTarget)
        double cost = 0.0;          // in the band: tiles of way + 15 a place after the band's first in the order
        int book = -1;              // journal goals: its place in the quest book (chapter tab, then record), -1 none
    };

    // The quest's number: DQ_<n> is n; R<rr>NQ<qq> is 100*rr + qq, but region 1's are 150 + qq (the journal's own
    // titles in every copy's logs, 2026-11-16: 151 «Ojos de lobo» R01NQ01, 302 «Ladrones de ganado» R03NQ02, 1002
    // «Planes de la inquisición» R10NQ02, 1101 «Hábitos negros» R11aNQ01, 2401 R24NQ01; Manolito, block BN: the script's
    // variable is named so). The 100 + 50*rr + qq of block X held only for regions 1 and 2.
    constexpr int32_t rq(int32_t region, int32_t quest)
    {
        return region == 1 ? 150 + quest : 100 * region + quest;
    }
    // From the quest reader's table (docs/QUESTS.md, 2026-11-10): 1 = do before it is lost or because it opens
    // something (the Book of Wisdom: rune swaps and the combo master), -1 = leave for last (the Riddle in the Desert,
    // Pure Water before the Whiskey Supplier, Moca not to be fought...).
    int questPriority(int32_t number)
    {
        // Ravenous Beasts (R04NQ03) among them: it fails once the infected wolves have killed all of the farmer's
        // cows (QUESTS.md «Ir rápido»; the player, 2026-11-12: «el enano no consigue hacer la misión de las vacas»,
        // A7 went for it 95-122 tiles off among 17 goals and it failed).
        // And the quests with a deadline (QUESTS.md, «3 días» and the rest: «entregar antes que cualquier otra
        // cosa»), whose timer is not always read: Sheepless in Bellevue (DQ_15005, the sheep the wolves kill; the
        // player, 2026-11-13: «la misión de la oveja nadie consiguió hacerla», A7 went for it 818-847 tiles off),
        // Messenger, Kidnapped, Tournament, Goods Messenger, Kalim-Khor, Ancarian Snow, Gallows, the dragon's egg and
        // the Lentil Liqueur.
        static constexpr int32_t kFirst[] = {15005, 15009, 15015, 15036, rq(1, 2), rq(2, 4), rq(3, 1), rq(4, 3),
                                             rq(5, 1), rq(5, 2), rq(7, 3), rq(9, 1), rq(12, 2), rq(13, 2), rq(13, 3),
                                             rq(14, 1), rq(17, 3), rq(18, 3), rq(22, 1), rq(24, 11), rq(25, 3),
                                             // Cattle Thieves (302, R03NQ02: its farmer follows the hero from the
                                             // taking and dies if left; also an escort, tier 2).
                                             rq(3, 2)};
        static constexpr int32_t kLast[] = {10259, 10260, rq(6, 2), rq(13, 1), rq(22, 3)};
        if (std::find(std::begin(kFirst), std::end(kFirst), number) != std::end(kFirst))
        {
            return 1;
        }
        if (std::find(std::begin(kLast), std::end(kLast), number) != std::end(kLast))
        {
            return -1;
        }
        return 0;
    }

    // Quests that fail if left once taken, with no timer the agent reads (docs/QUESTS.md, their «Trampas» from the
    // game's own Qfail texts): defences and races («You turned tail»: A5 2026-11-17 01:29, 703 «Un puente lejano»
    // taken and followed from 809 tiles off, failed on the way), those whose people die if not reached in time, and
    // the deadlines of one to three game days. Done at once, before anything else, like the escorts (tier 2); their
    // giver is not spoken to until the hero has the level of its ground (the coordinator, 2026-11-17).
    bool doneAtOnce(int32_t number)
    {
        static constexpr int32_t kAtOnce[] = {
            // defences and races
            rq(3, 1),   // ¡Orcos!: the farmers die if the orcs reach them
            rq(4, 3),   // Bestias feroces: the cows
            rq(7, 1),   // Pozos envenenados: the King's spy dies when Faeries Crossing is overrun
            rq(7, 3),   // Un puente lejano: defend the bridge, fails if the hero is not there
            rq(10, 3),  // El Campamento gitano: a race behind the gypsy
            rq(11, 1),  // Hábitos negros: the girl on the altar
            rq(22, 1),  // El Monstruo Araña de Moorbrook: the girl
            // deadlines of one to three game days
            rq(1, 2),   // Mensajero: 3 days
            rq(9, 1),   // Secuestradas: 3 days, the women follow the hero
            rq(11, 2),  // Situación comprometida: 1 day
            rq(12, 2),  // Hierbas curativas: 3 days
            rq(13, 2),  // El Torneo: 3 days
            rq(13, 3),  // Mensajero de mercancías: 3 days
            rq(14, 1),  // Negocios turbios: 1 day, and an escort
            rq(18, 3),  // Kalim-Khor: 3 days
            5005,       // Pony Express: a relay against the clock
            // escorts whose objective may not read as one (Lore::kindOf covers the rest)
            rq(2, 2), rq(8, 1), rq(14, 3), rq(14, 4), rq(15, 2), rq(16, 2), rq(17, 1), rq(19, 3), rq(24, 2), rq(24, 3),
            rq(25, 1), 9010, 6003, 10254, 15005};
        return std::find(std::begin(kAtOnce), std::end(kAtOnce), number) != std::end(kAtOnce);
    }

    // The game minutes left on a quest's deadline, -1 if none (Manolito's block W2, 2026-11-10): the script's
    // timers at [0xAA4540] +0x2C..+0x30, 0x4C bytes each (+0 key = the quest's number, +4 length and +8 start in
    // game minutes); the clock's date at +0x18 (u32 year, u16 month, day, hour, minute). Timers of 6 h or less are
    // a scene's pauses, not deadlines. 24 game minutes go by in a real one.
    int32_t deadlineLeft(int32_t number)
    {
        const uint8_t* clk = *reinterpret_cast<const uint8_t* const*>(0xAA4540);
        if (!clk || number <= 0)
        {
            return -1;
        }
        const auto begin = *reinterpret_cast<const uint8_t* const*>(clk + 0x2C);
        const auto end = *reinterpret_cast<const uint8_t* const*>(clk + 0x30);
        constexpr size_t kTimer = 0x4C;
        if (!begin || end <= begin || (end - begin) % kTimer || (end - begin) / kTimer > 256)
        {
            return -1;
        }
        const auto u16 = [&](size_t at) { return static_cast<int64_t>(*reinterpret_cast<const uint16_t*>(clk + at)); };
        const int64_t nowMin =
            u16(0x22) +
            60 * (u16(0x20) + 24 * (u16(0x1E) + 30 * (u16(0x1C) + 12 * static_cast<int64_t>(
                                                                         *reinterpret_cast<const uint32_t*>(clk + 0x18)))));
        int64_t best = -1;
        for (const uint8_t* t = begin; t < end; t += kTimer)
        {
            const int32_t key = *reinterpret_cast<const int32_t*>(t);
            const int64_t length = *reinterpret_cast<const int32_t*>(t + 4), start = *reinterpret_cast<const int32_t*>(t + 8);
            if (key != number || length <= 360)
            {
                continue;
            }
            const int64_t left = start + length - nowMin;
            if (left > 0 && (best < 0 || left < best))
            {
                best = left;
            }
        }
        return best > 0x7FFFFFFF ? 0x7FFFFFFF : static_cast<int32_t>(best);
    }
    std::vector<QuestGoal> g_questBook;     // rebuilt by questTarget, nearest first

    bool questGoalNear(int32_t x, int32_t y, double tiles)
    {
        // The journal's goals only: a giver's offer near a spot would have it clicked before the quest is taken.
        return std::any_of(g_questBook.begin(), g_questBook.end(), [&](const QuestGoal& g) {
            return g.kind == GoalKind::Journal &&
                   std::hypot(static_cast<double>(g.x - x), static_cast<double>(g.y - y)) < tiles * kTileSize;
        });
    }
    int g_questsDone = 0, g_questsFailed = 0;
    std::vector<int32_t> g_doneNumbers;     // the journal's quests done (record +0x08), at its last read
    DWORD g_questsDoneAt = 0;           // when the count of quests done last changed
    DWORD g_questPauseUntil = 0;        // quests left a while for farming (a long spell of neither fights nor quests)
    // The yellow "?!" / "!" signs of the last pass (creatures the hero can speak to now), on the hero's layer.
    struct Sign
    {
        GoalKind kind;
        uint32_t id;
        int32_t x, y;
    };
    std::vector<Sign> g_signs;
    // Givers come to whose sign was not seen (the owner's GAME02 against the copies, 2026-11-23: 1403, 1202, 15001 and
    // 15029 never taken; A5 came to 1403's giver at 2399,2134 and went on): the creature standing at the giver's tile
    // is spoken to as a player who knows him does, as a sign of its own for 2 min; once a creature each 10 min.
    struct GiverTalk
    {
        int32_t number, tx, ty;
        DWORD since;
    };
    std::vector<GiverTalk> g_giverTalks;
    std::unordered_map<uint32_t, DWORD> g_giverSpokenAt;

    constexpr double kSignRange = 150.0;                    // tiles: farther quest signs are not goals
    bool goalBlocked(int32_t x, int32_t y, DWORD now);     // travel gave up on it for now
    bool talkedLately(uint32_t id, DWORD now);              // spoken to a short while ago
    void forgetTalks();                                     // a quest step done: anyone may be spoken to again

    bool sectorLevels(const uint8_t* world, int tx, int ty, int& lo, int& hi);

    // The journal quest followed, and those failed while followed (the failure loads the last save, where the quest
    // is open again: A7 failed side quest 302 after each load, 52 failures in a day). One failed so is left: the
    // book skips it for this run, as a player leaves a quest he cannot do.
    int32_t g_followedNumber = 0;
    // A goal on the way gone to now instead of the order's (questTarget), and its place: the order's clocks wait, and a
    // jam there parks its tile, not the order's goal's.
    bool g_detouring = false;
    int32_t g_detourX = 0, g_detourY = 0;
    std::vector<int32_t> g_givenUpQuests;

    // Failed quests and the copy's slot (the coordinator, 2026-11-16: no save ever after a quest failed; one failed for
    // good is a fault of the agent to study): the journal's failed numbers now, those the slot holds (read once after
    // each load or save) and those paid for with a load.
    std::vector<int32_t> g_failedNow, g_failedInSlot, g_paidFailures;
    unsigned g_slotGeneration = ~0u;

    // Quests on offer by a giver the agent has not come to (the script's variable 1, a giver in quest_givers.inc), as
    // read with the journal: the campaign's last quest waits for them.
    int g_giversLeft = 0;
    struct QuestGiver
    {
        int32_t number;
        int x, y, lo, hi;   // tile; the sector's levels
    };
    constexpr QuestGiver kQuestGivers[] = {
#include "game/quest_givers.inc"
    };

    // The campaign's quests in the order they are done (the owner, 2026-11-17: «crea una orden cronológica de las
    // misiones según nivel y obliga a los agentes hacer las misiones en su orden»): by level, then region, then
    // number, each main quest after the one before it. Generated by tools/quest_order.py from the game's sector levels
    // at each giver and objective (Manolito's block BN) or the zone's level (docs/QUESTS.md); each line names its source.
    // The next goal is always the first of the list neither done nor failed that can be gone for; the rest are skipped,
    // their reason logged («quest order: N skipped: ...»), and tried again later.
    struct QuestOrder
    {
        int32_t number;
        int level;      // 0: no source has one (last in the list)
        bool main;
    };
    constexpr QuestOrder kQuestOrder[] = {
#include "game/quest_order.inc"
    };
    constexpr int kOrderCount = static_cast<int>(sizeof(kQuestOrder) / sizeof(kQuestOrder[0]));
    int orderRank(int32_t number)
    {
        for (int i = 0; number > 0 && i < kOrderCount; ++i)
        {
            if (kQuestOrder[i].number == number)
            {
                return i;
            }
        }
        return -1;
    }
    // A goal with no number (a sign not at a known giver, a report) or one not in the list: placed among the quests of
    // its ground's level, at the first of the list of that level or above.
    int orderRankByLevel(int lo)
    {
        for (int i = 0; i < kOrderCount; ++i)
        {
            if (kQuestOrder[i].level >= lo && kQuestOrder[i].level > 0)
            {
                return i;
            }
        }
        return kOrderCount;
    }
    // The level band (the owner, 2026-11-17 13:00, «los 2 criterios son buenos»: the campaign's order and the quests
    // of the hero's level, the nearest first): quests of level hero - 5 to hero + 2 are taken by way and place in the
    // order together; the rest by the order as before.
    constexpr int kBandBelow = 5, kBandAbove = 2;
    bool inLevelBand(int rank, int heroLv)
    {
        if (heroLv <= 0 || rank < 0 || rank >= kOrderCount || kQuestOrder[rank].level <= 0)
        {
            return false;
        }
        const int lv = kQuestOrder[rank].level;
        return lv >= heroLv - kBandBelow && lv <= heroLv + kBandAbove;
    }
    // Quests skipped (gone for 20 min, 40 for an escort or deadline, with no step done nor nearer; a giver not reached
    // in 20 min): 30 min the first time; skipped twice in a row, at the end of the list until something changes, the
    // hero's level or the journal (the coordinator, 2026-11-17: A5 went between escorts 701, 4027 tiles off, and 202
    // the whole night, 28 quests done at 01:49 and at 08:32; each change of goal began the other's 20 min anew).
    struct OrderSkip
    {
        DWORD until = 0;
        int count = 0;          // skips in a row
        int level = 0, done = 0, failed = 0;
        int untilDone = 0;      // the cap's: back once this many quests are done (or its 2 h are over), 0 none
    };
    std::unordered_map<int32_t, OrderSkip> g_orderSkips;
    // Times in a row the goal followed was given up by the travel (no way for now, left a few minutes) with no step
    // done nor nearer: at 3 it is skipped (A3 2026-11-17 08:50-08:56: 501, 203 and 402 each «no progress for 25 s on
    // this spot: the goal left 3 min» in turn; A5 202, 38 tiles off, «stuck again: left 10 min», then 701, and back).
    std::unordered_map<int32_t, int> g_orderBlocks;
    // The skips kept beside the exe across the copy's restarts and installs (the coordinator, 2026-11-17: A3 went back
    // to 501 after the install of 12:07, its skip forgotten): SacredBild-skips.txt, a line a quest «number count level
    // done failed ms-left»; read on first use, written after a pass that changed them, removed by AgentSave on a new
    // game.
    std::wstring giversPath();
    bool g_journalSeen = false;     // the journal read in this run: the skips' level and counts compared only then
    bool g_skipsRead = false, g_skipsDirty = false;
    std::wstring skipsPath()
    {
        const std::wstring path = giversPath();
        return path.substr(0, path.find_last_of(L"\\/") + 1) + L"SacredBild-skips.txt";
    }
    void readSkips(DWORD now)
    {
        g_skipsRead = true;
        FILE* f = _wfopen(skipsPath().c_str(), L"r");
        if (!f)
        {
            return;
        }
        char line[96];
        while (std::fgets(line, sizeof(line), f))
        {
            int number = 0, count = 0, level = 0, done = 0, failed = 0, untilDone = 0;
            unsigned long left = 0;
            if (std::sscanf(line, "%d %d %d %d %d %lu %d", &number, &count, &level, &done, &failed, &left, &untilDone) < 6)
            {
                continue;
            }
            if (number > 0 && count > 0)
            {
                OrderSkip& k = g_orderSkips[number];
                k.count = count;
                k.level = level;
                k.done = done;
                k.failed = failed;
                k.untilDone = untilDone;
                const DWORD until = now + static_cast<DWORD>(left);
                k.until = left ? (until ? until : 1) : 0;
            }
        }
        std::fclose(f);
        LOG("AutoAttack: {} quests skipped before, kept from the last runs", g_orderSkips.size());
    }
    void writeSkips(DWORD now)
    {
        g_skipsDirty = false;
        if (FILE* f = _wfopen(skipsPath().c_str(), L"w"))
        {
            for (const auto& [number, k] : g_orderSkips)
            {
                const unsigned long left =
                    k.until && static_cast<int>(now - k.until) < 0 ? static_cast<unsigned long>(k.until - now) : 0;
                std::fprintf(f, "%d %d %d %d %d %lu %d\n", number, k.count, k.level, k.done, k.failed, left, k.untilDone);
            }
            std::fclose(f);
        }
    }
    // The 45 min cap's clocks by quest number (questTarget), kept beside the exe: «number ms-gone done failed».
    struct Cap
    {
        DWORD since = 0;
        int done = 0, failed = 0;   // the journal's counts when it began
    };
    std::unordered_map<int32_t, Cap> g_caps;
    bool g_capsRead = false, g_capsDirty = false;
    std::wstring capsPath()
    {
        const std::wstring path = giversPath();
        return path.substr(0, path.find_last_of(L"\\/") + 1) + L"SacredBild-caps.txt";
    }
    void readCaps(DWORD now)
    {
        g_capsRead = true;
        FILE* f = _wfopen(capsPath().c_str(), L"r");
        if (!f)
        {
            return;
        }
        int number = 0, done = 0, failed = 0;
        unsigned long gone = 0;
        while (std::fscanf(f, "%d %lu %d %d", &number, &gone, &done, &failed) == 4)
        {
            if (number > 0)
            {
                Cap& c = g_caps[number];
                c.since = now - static_cast<DWORD>(gone);
                c.since = c.since ? c.since : 1;
                c.done = done;
                c.failed = failed;
            }
        }
        std::fclose(f);
        LOG("AutoAttack: {} quests' 45 min clocks kept from the last runs", g_caps.size());
    }
    void writeCaps(DWORD now)
    {
        g_capsDirty = false;
        if (FILE* f = _wfopen(capsPath().c_str(), L"w"))
        {
            for (const auto& [number, c] : g_caps)
            {
                std::fprintf(f, "%d %lu %d %d\n", number, static_cast<unsigned long>(now - c.since), c.done, c.failed);
            }
            std::fclose(f);
        }
    }
    bool orderSkipped(int32_t number, DWORD now)
    {
        if (!g_skipsRead)
        {
            readSkips(now);
        }
        const auto it = g_orderSkips.find(number);
        if (number <= 0 || it == g_orderSkips.end())
        {
            return false;
        }
        OrderSkip& k = it->second;
        // Set aside by the cap: back once 3 other quests are done, or after its 2 h (the coordinator, 2026-11-17)
        if (k.untilDone)
        {
            if (!g_journalSeen || (g_questsDone < k.untilDone && k.until && static_cast<int>(now - k.until) < 0))
            {
                return true;
            }
            LOG("AutoAttack: quest order: {} set aside by the cap: back ({} quests done, its 2 h {})", number,
                g_questsDone, static_cast<int>(now - k.until) >= 0 ? "over" : "not over");
            k.untilDone = 0;
            k.until = 0;
            g_skipsDirty = true;
        }
        if (k.until && static_cast<int>(now - k.until) < 0)
        {
            return true;
        }
        if (k.count >= 2)
        {
            // Not before the journal and the hero are read (a skip kept from the last run is compared with them)
            if (!g_journalSeen || HeroProfile::current().level <= 0 ||
                (k.level == HeroProfile::current().level && k.done == g_questsDone && k.failed == g_questsFailed))
            {
                return true;
            }
            LOG("AutoAttack: quest order: {} back in its place (the hero's level or the journal changed)", number);
            k.count = 1;   // one more stall parks it again (the journal moves on any failure and load too)
            g_skipsDirty = true;
        }
        return false;
    }
    void orderSkip(int32_t number, DWORD now, const char* why)
    {
        if (!g_skipsRead)
        {
            readSkips(now);
        }
        g_skipsDirty = true;
        OrderSkip& k = g_orderSkips[number];
        ++k.count;
        k.until = now + 1800000;
        k.level = HeroProfile::current().level;
        k.done = g_questsDone;
        k.failed = g_questsFailed;
        if (k.count >= 2)
        {
            LOG("AutoAttack: quest order: {} skipped: {} (twice in a row: at the end of the list until the level or the "
                "journal changes)",
                number, why);
        }
        else
        {
            LOG("AutoAttack: quest order: {} skipped: {} (tried again in 30 min)", number, why);
        }
    }
    int32_t g_orderNext = 0;                                // the first of the list neither done nor failed
    int g_orderPos = 0;                                     // its place, from 1
    // The script's quest values and the givers come to, as the last pass read them (for the order's reasons).
    const std::unordered_map<int32_t, uint32_t>* g_scriptValuesSeen = nullptr;
    // The quests the script sets up (SetUpQuest, value 1, their givers created) the moment the hero enters their
    // region, with no other condition: the blocks Region<N>Enter of bin/NetScript (tools/sqw_quest_open.py, 2026-11-18).
    // Until then the variable is 0 or missing; a player who walks there finds the giver with his sign (the owner,
    // 2026-11-18: «haz que las misiones puedan ser completadas»: 72 skipped as «not on offer yet»).
    constexpr int32_t kRegionOpened[] = {
        201,  202,  203,  204,  301,  302,  303,  401,  402,  403,  501,  502,  503,  601,  602,  603,  701,  702,  703,
        801,  802,  803,  901,  902,  903,  1001, 1002, 1003, 1101, 1102, 1103, 1111, 1112, 1113, 1201, 1202, 1203, 1301,
        1302, 1303, 1401, 1402, 1403, 1404, 1405, 1501, 1502, 1503, 1601, 1602, 1603, 1701, 1702, 1703, 1801, 1802, 1803,
        1901, 1902, 1903, 2001, 2002, 2003, 2101, 2102, 2201, 2202, 2203, 2301, 2302, 2401, 2501, 2502, 2503, 2504};
    bool regionOpened(int32_t n)
    {
        return std::find(std::begin(kRegionOpened), std::end(kRegionOpened), n) != std::end(kRegionOpened);
    }
    // On offer, or to be: 1 in the script, a DQ_ one, or one its region's entering sets up and not begun (0 or none).
    bool offerOrRegion(const std::unordered_map<int32_t, uint32_t>& values, int32_t n)
    {
        const auto value = values.find(n);
        return n >= 10000 || (value != values.end() && value->second == 1) ||
               (regionOpened(n) && (value == values.end() || value->second == 0));
    }
    const std::vector<int32_t>* g_giversVisitedSeen = nullptr;

    // The script's variables (Manolito's block BN, docs/Misiones-todas.md): a vector [0xAACF80+0x7550 .. +0x7554) of
    // 0x24-byte records, char[0x20] name and u32 value at +0x20. A quest's is named by its journal number in decimal:
    // 0 not available, 1 offered and not taken, bit 1 taken; dungeon quests (15001+) have none.
    bool scriptQuestValues(std::unordered_map<int32_t, uint32_t>& values)
    {
        const auto begin = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7550);
        const auto end = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7554);
        constexpr size_t kRecord = 0x24;
        if (!begin || end <= begin || (end - begin) % kRecord || (end - begin) / kRecord > 5000)
        {
            return false;   // the last ones read kept
        }
        std::unordered_map<int32_t, uint32_t> out;
        for (const uint8_t* r = begin; r < end; r += kRecord)
        {
            int32_t n = 0;
            int i = 0;
            for (; i < 0x20 && r[i]; ++i)
            {
                if (r[i] < '0' || r[i] > '9' || i >= 7)
                {
                    n = -1;
                    break;
                }
                n = n * 10 + (r[i] - '0');
            }
            if (n > 0 && i < 0x20 && !r[i])
            {
                out[n] = *reinterpret_cast<const uint32_t*>(r + 0x20);
            }
        }
        if (out.empty())
        {
            return false;
        }
        values.swap(out);
        return true;
    }

    // The givers come to (or left after 20 min), kept beside the exe across the copy's restarts (the coordinator,
    // 2026-11-16: each install walked to them all again): SacredBild-givers.txt, one quest number a line, «-» before
    // one left unreached; AgentSave removes it when a new game begins.
    std::wstring giversPath()
    {
        wchar_t exe[MAX_PATH] = {};
        GetModuleFileNameW(nullptr, exe, MAX_PATH);
        const std::wstring path = exe;
        return path.substr(0, path.find_last_of(L"\\/") + 1) + L"SacredBild-givers.txt";
    }

    void readGivers(std::vector<int32_t>& visited)
    {
        FILE* f = _wfopen(giversPath().c_str(), L"r");
        if (!f)
        {
            return;
        }
        char line[32];
        while (std::fgets(line, sizeof(line), f))
        {
            // «-n»: not reached in 20 min, kept only to study; tried again (the campaign's order, 2026-11-17)
            const int32_t number = line[0] == '-' ? 0 : std::atoi(line);
            if (number > 0 && std::find(visited.begin(), visited.end(), number) == visited.end())
            {
                visited.push_back(number);
            }
        }
        std::fclose(f);
        LOG("AutoAttack: {} quest givers come to before, kept from the last runs", visited.size());
    }

    void noteGiver(int32_t number, bool reached)
    {
        if (FILE* f = _wfopen(giversPath().c_str(), L"a"))
        {
            std::fprintf(f, reached ? "%d\n" : "-%d\n", number);
            std::fclose(f);
        }
    }

    // The giver followed now and since when, for the 20 min a giver is gone to at most (its tile may not be reached:
    // the script gives no layer).
    int32_t g_giverFollowed = 0;
    DWORD g_giverFollowedLast = 0;
    std::unordered_map<int32_t, DWORD> g_giverTime;     // ms followed in all, a giver

    // The order's head and the quests skipped before it (the owner, 2026-11-17): the first of the list neither done
    // nor failed is «next»; each before the goal picked is skipped with its reason, logged once in 30 min. The goal
    // picked and followed 20 min with no quest done (its giver unreachable, a step the agent cannot do) is skipped
    // 30 min, then tried again. Escorts and deadlines (tier 2) are never skipped so.
    template <typename TooLow> void questOrderPass(DWORD now, int heroLv, const TooLow& tooLow)
    {
        const auto has = [](const std::vector<int32_t>& v, int32_t n) { return std::find(v.begin(), v.end(), n) != v.end(); };
        const QuestGoal* front = g_questBook.empty() || g_questBook.front().blocked ? nullptr : &g_questBook.front();
        static std::unordered_map<int32_t, DWORD> s_told;
        int logged = 0;
        g_orderNext = 0;
        g_orderPos = 0;
        // A main quest is passed once a later one is done or open: each class has its own start (A3's journal, 17-11:
        // mains 1, 10, 12, 20, 43-45 done, 51 open, no 2, 3, 9, 11, 22 nor 31).
        int32_t mainReached = 0;
        for (const int32_t n : g_doneNumbers)
        {
            if (n > 0 && n < 100)
            {
                mainReached = std::max(mainReached, n);
            }
        }
        for (const QuestGoal& o : g_questBook)
        {
            if (o.kind == GoalKind::Journal && o.main && o.number > 0 && o.number < 100)
            {
                mainReached = std::max(mainReached, o.number);
            }
        }
        for (int i = 0; i < kOrderCount; ++i)
        {
            const int32_t n = kQuestOrder[i].number;
            if (has(g_doneNumbers, n) || has(g_failedNow, n) || (kQuestOrder[i].main && n < mainReached))
            {
                continue;
            }
            if (!g_orderNext)
            {
                g_orderNext = n;
                g_orderPos = i + 1;
            }
            // Up to the goal picked: the ones before it are those skipped.
            if (front && (front->rank <= i || front->number == n))
            {
                break;
            }
            const auto goal = std::find_if(g_questBook.begin(), g_questBook.end(), [n](const QuestGoal& o) { return o.number == n; });
            std::string why;
            if (goal != g_questBook.end())
            {
                why = goal->blocked ? "no way to it for now (or given up after a failure)"
                      : orderSkipped(n, now) ? "gone for long with no step done nor nearer: tried again later"
                      : goal->tier < 0 ? "held: left for last (it breaks another quest)"
                      : front && front->band && goal->tier == front->tier
                          ? "the level band's cheaper one first (way and place together; done after)"
                                       : "a quest that cannot wait goes first (an escort, a deadline, one lost if left)";
            }
            else if (tooLow(n))
            {
                why = "held: under its least level";
            }
            else
            {
                const QuestGiver* giver = nullptr;
                for (const QuestGiver& q : kQuestGivers)
                {
                    if (q.number == n)
                    {
                        giver = &q;
                        break;
                    }
                }
                bool onOffer = false;
                if (g_scriptValuesSeen)
                {
                    onOffer = offerOrRegion(*g_scriptValuesSeen, n);
                }
                if (!giver)
                {
                    why = kQuestOrder[i].main ? "a main quest not yet given (the one before it first)"
                                              : "no giver known: taken from its sign when one is seen";
                }
                else if (!onOffer)
                {
                    why = "not on offer yet (the script's value is not 1)";
                }
                else if (orderSkipped(n, now))
                {
                    why = "its giver not reached in 20 min: tried again later";
                }
                else if (g_giversVisitedSeen && has(*g_giversVisitedSeen, n))
                {
                    why = "its giver come to and the quest not taken (not yet for the hero)";
                }
                else if (heroLv > 0 && giver->lo > heroLv + 2)
                {
                    why = std::format("held: its giver's ground is level {}, the hero {}", giver->lo, heroLv);
                }
                else
                {
                    why = "its giver not among the goals this pass";
                }
            }
            if (front && front->book >= 0 && !front->blocked &&
                (goal == g_questBook.end() || (goal->book < 0 && !goal->blocked) || goal->book > front->book) &&
                !why.starts_with("held") && !why.starts_with("not on offer") && !why.starts_with("no giver"))
            {
                why = "a quest taken goes first (the book's order, page 1 on, top to bottom)";
            }
            DWORD& told = s_told[n];
            if (logged < 8 && (!told || now - told > 1800000))
            {
                told = now ? now : 1;
                ++logged;
                LOG("AutoAttack: quest order: {} skipped: {}", n, why);
            }
        }
        // «next» is the quest gone for now when it is in the list, the first not done otherwise; the first not done is
        // named beside it, so one that holds the list shows (the coordinator, 2026-11-17: «next» stood on 151, 154,
        // 210 and 10254 for 6 h, quests never on offer or whose giver had been come to, while others were done).
        const int32_t head = g_orderNext;
        const int headPos = g_orderPos;
        if (front)
        {
            if (const int r = orderRank(front->number); r >= 0)
            {
                g_orderNext = front->number;
                g_orderPos = r + 1;
            }
        }
        static int32_t s_toldNext = 0;
        static DWORD s_nextTold = 0;
        if (g_orderNext != s_toldNext && (!s_nextTold || now - s_nextTold > 60000))   // at most a line a minute (Q2)
        {
            s_toldNext = g_orderNext;
            s_nextTold = now ? now : 1;
            LOG("AutoAttack: quest order: next {} (level {}), place {}/{}; first not done {} (place {})", g_orderNext,
                g_orderPos ? kQuestOrder[g_orderPos - 1].level : 0, g_orderPos, kOrderCount, head, headPos);
        }
    }

    // The goal picked by questTarget's last pass, for the time it is actually gone for (orderFollowTick).
    struct OrderPick
    {
        int32_t number = 0;
        GoalKind kind = GoalKind::Journal;
        int tier = 0;
        double distance = 0.0;
        uint32_t objectiveKey = 0;
    } g_orderPick;

    // Whether the game's list of the hero's companions (hero+0x39C..+0x3A0, records of 9 bytes, +0 the id, +8 non-zero for a
    // hired mercenary) holds a live creature the script made follow: an escorted man (Manolito, AGENT_ADDRESSES
    // «Escolta»). False when the list does not read well.
    bool escorteeFollows()
    {
        cObjectManager* objects = cObjectManager::instance();
        const cCreature* hero = objects ? objects->hero() : nullptr;
        if (!hero)
        {
            return true;    // nothing known: nothing done
        }
        const uint8_t* heroBytes = reinterpret_cast<const uint8_t*>(hero);
        const auto begin = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x39C);
        const auto end = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x3A0);
        if (begin && (end < begin || ((end - begin) % 9) || (end - begin) / 9 > 8))
        {
            return true;
        }
        for (const uint8_t* r = begin; r && r < end; r += 9)
        {
            const uint32_t id = *reinterpret_cast<const uint32_t*>(r);
            const cCreature* c = objects->creature(id);
            // The script's follower (+8 = 0), or the journal's own creature (a rescued girl is in the list with +8 = 1).
            if (c && c->health > 0 &&
                (r[8] == 0 || std::any_of(g_questBook.begin(), g_questBook.end(), [id](const QuestGoal& g) {
                    return g.kind == GoalKind::Journal && g.who == id;
                })))
            {
                return true;
            }
        }
        return false;
    }

    // ---- An escort lost: back for the one escorted (the stuck solver, 2026-11-17, A5: Escolta 202, Jacob to the West
    // Bridge; the hero had left him behind, the journal still held the quest, and it walked to the bridge alone three
    // times in 2 h; the owner wants every quest done) ------------------------------------------------------------------
    // Per quest number: the escorted creature's type (the game's creature type, object +0x10) and where it was last seen
    // following the hero. Learned from the companions list the first time an escorted one is in it; Jacob (Manolito, AGENT_
    // ADDRESSES «Escolta»: type 0x29D, side 3) is known from the start. Kept beside the exe in SacredBild-escoltas.txt,
    // «number type x y» (tiles).
    struct EscortInfo
    {
        uint32_t type = 0;
        int32_t x = 0, y = 0;       // world units; 0: not known
    };
    std::unordered_map<int32_t, EscortInfo> g_escortInfo = {{202, {0x29D, 0, 0}}};
    bool g_escortRead = false, g_escortDirty = false;
    DWORD g_escortWrittenAt = 0;
    // The type looked for in the object list (scanQuestMarks), and the creature of it found, alive, on the surface.
    uint32_t g_escortWantType = 0;
    struct EscortSeen
    {
        uint32_t id = 0, type = 0;
        int32_t x = 0, y = 0;
        DWORD at = 0;
    } g_escortSeen;

    std::wstring escortPath()
    {
        const std::wstring path = giversPath();
        return path.substr(0, path.find_last_of(L"\\/") + 1) + L"SacredBild-escoltas.txt";
    }
    void readEscorts()
    {
        g_escortRead = true;
        FILE* f = _wfopen(escortPath().c_str(), L"r");
        if (!f)
        {
            return;
        }
        char line[96];
        while (std::fgets(line, sizeof(line), f))
        {
            int number = 0, x = 0, y = 0;
            unsigned type = 0;
            if (std::sscanf(line, "%d %u %d %d", &number, &type, &x, &y) >= 2 && number > 0 && type)
            {
                g_escortInfo[number] = {type, static_cast<int32_t>((x + 0.5) * kTileSize), static_cast<int32_t>((y + 0.5) * kTileSize)};
                if (x <= 0 || y <= 0)
                {
                    g_escortInfo[number].x = g_escortInfo[number].y = 0;
                }
            }
        }
        std::fclose(f);
    }
    void writeEscorts(DWORD now)
    {
        g_escortDirty = false;
        g_escortWrittenAt = now;
        if (FILE* f = _wfopen(escortPath().c_str(), L"w"))
        {
            for (const auto& [number, info] : g_escortInfo)
            {
                std::fprintf(f, "%d %u %d %d\n", number, info.type, static_cast<int>(info.x / kTileSize),
                             static_cast<int>(info.y / kTileSize));
            }
            std::fclose(f);
        }
    }

    // Each pass of the world scan: the escorted one in the companions list, if any, teaches the quest's type (when not
    // known) and where it was last with the hero.
    void learnEscortee(DWORD now)
    {
        if (!g_escortRead)
        {
            readEscorts();
        }
        const int32_t number = g_followedNumber;
        cObjectManager* objects = cObjectManager::instance();
        const cCreature* hero = objects ? objects->hero() : nullptr;
        if (number <= 0 || !hero || Lore::questKind() != Lore::QuestKind::Escort)
        {
            return;
        }
        const uint8_t* heroBytes = reinterpret_cast<const uint8_t*>(hero);
        const auto begin = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x39C);
        const auto end = *reinterpret_cast<const uint8_t* const*>(heroBytes + 0x3A0);
        if (!begin || end < begin || ((end - begin) % 9) || (end - begin) / 9 > 8)
        {
            return;
        }
        for (const uint8_t* r = begin; r < end; r += 9)
        {
            const cCreature* c = objects->creature(*reinterpret_cast<const uint32_t*>(r));
            if (!c || c->health <= 0 || r[8] != 0)
            {
                continue;
            }
            const uint32_t type = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(c) + 0x10);
            EscortInfo& info = g_escortInfo[number];
            if (!info.type)
            {
                info.type = type;
                g_escortDirty = true;
                LOG("AutoAttack: quest {}: the escorted one is of type {:x} (learned from the companions list)", number, type);
            }
            if (info.type == type &&
                std::hypot(static_cast<double>(c->x - info.x), static_cast<double>(c->y - info.y)) > 8.0 * kTileSize)
            {
                info.x = c->x;
                info.y = c->y;
                g_escortDirty = true;
            }
            break;
        }
        if (g_escortDirty && now - g_escortWrittenAt > 30000)
        {
            writeEscorts(now);
        }
    }

    // The escort's goal when the escorted one is not with the hero: where he is looked for (the last place he was with
    // the hero, the quest's giver, one then the other every 4 min), and himself once seen: spoken to like any quest
    // creature, which puts him in the companions list again and the escort code goes on from there. 15 min without
    // finding him: the quest is skipped as any other that goes nowhere.
    void escortFetch(int32_t number, DWORD now, int32_t& x, int32_t& y, double& radius, uint32_t& who)
    {
        static std::unordered_map<int32_t, DWORD> s_since;
        if (!g_escortRead)
        {
            readEscorts();
        }
        if (escorteeFollows())
        {
            s_since.erase(number);
            g_escortWantType = 0;
            return;
        }
        const auto info = g_escortInfo.find(number);
        if (info == g_escortInfo.end() || !info->second.type)
        {
            g_escortWantType = 0;
            return;     // not known who: the destination, and the park rule at it
        }
        g_escortWantType = info->second.type;
        DWORD& since = s_since[number];
        if (!since)
        {
            since = now;
            LOG("AutoAttack: quest {}: the escorted one (type {:x}) is not with the hero: looked for first", number,
                info->second.type);
        }
        else if (now - since > 900000)
        {
            since = 0;
            g_escortWantType = 0;
            orderSkip(number, now, "its escorted one not found in 15 min");
            return;
        }
        if (g_escortSeen.id && g_escortSeen.type == info->second.type && now - g_escortSeen.at < 6000)
        {
            x = g_escortSeen.x;
            y = g_escortSeen.y;
            radius = 3.0 * kTileSize;
            who = g_escortSeen.id;
            return;
        }
        std::vector<std::pair<int32_t, int32_t>> places;
        if (info->second.x > 0 && info->second.y > 0)
        {
            places.emplace_back(info->second.x, info->second.y);
        }
        for (const QuestGiver& q : kQuestGivers)
        {
            if (q.number == number)
            {
                places.emplace_back(static_cast<int32_t>((q.x + 0.5) * kTileSize), static_cast<int32_t>((q.y + 0.5) * kTileSize));
                break;
            }
        }
        if (places.empty())
        {
            g_escortWantType = 0;
            return;
        }
        const auto& place = places[((now - since) / 240000) % places.size()];
        x = place.first;
        y = place.second;
        radius = 8.0 * kTileSize;
        who = 0xFFFFFFFFu;
    }

    // Called each step the agent goes for its quest goal (not while farming, paused or held): the goal picked, gone
    // for 20 min in all with no step of it done and never 10 tiles nearer than before, is skipped 30 min, then tried
    // again (its giver unreachable, a step the agent cannot do). Escorts and deadlines (tier 2) are never skipped so;
    // a giver has its own 20 min.
    void orderFollowTick(DWORD now)
    {
        // One clock a quest: going between two goals no longer starts each one's time anew (A5, the night of 17-11).
        struct Clock
        {
            DWORD last = 0, spent = 0;
            double best = 0.0;
            uint32_t objective = 0;
        };
        static std::unordered_map<int32_t, Clock> s_clocks;
        const OrderPick& p = g_orderPick;
        // A goal on the way gone to now: the order's clock waits (its 30 s gap drops the detour's time).
        if (p.number <= 0 || p.kind == GoalKind::Giver || g_detouring)
        {
            return;
        }
        // An escort at its place without the one escorted (the stuck solver, 2026-11-17, A5: Escolta 202, Jacob to the West
        // Bridge at 2661,3055; the journal holds it, the hero's companions list only a hired mercenary, and it walked to
        // the bridge alone three times in 2 h, «at the quest's goal: looking around it» 5-10 min each time and the quest
        // never done; the escorted one was left behind, where, nothing in the log says): after 3 min there alone, the
        // quest is skipped as any other that goes nowhere (30 min, then at the end of the list until the journal changes).
        {
            static std::unordered_map<int32_t, DWORD> s_aloneSince;
            if (p.tier >= 2 && p.kind == GoalKind::Journal && Lore::questKind() == Lore::QuestKind::Escort &&
                p.distance < 25.0 * kTileSize && !escorteeFollows())
            {
                DWORD& since = s_aloneSince[p.number];
                if (!since)
                {
                    since = now;
                }
                else if (now - since > 180000)
                {
                    since = 0;
                    orderSkip(p.number, now, "an escort at its place without the one escorted");
                    return;
                }
            }
            else
            {
                s_aloneSince.erase(p.number);
            }
        }
        auto [it, fresh] = s_clocks.try_emplace(p.number);
        Clock& c = it->second;
        if (fresh || p.objectiveKey != c.objective || p.distance < c.best - 10.0 * kTileSize)
        {
            if (!fresh && p.objectiveKey != c.objective)
            {
                if (g_orderSkips.erase(p.number))   // a step done: its skips in a row are over
                {
                    g_skipsDirty = true;
                }
            }
            if (!fresh)
            {
                g_orderBlocks.erase(p.number);  // a step done or nearer: not stuck on its way
            }
            c.best = fresh || p.objectiveKey != c.objective ? p.distance : std::min(c.best, p.distance);
            c.objective = p.objectiveKey;
            c.spent = 0;
            c.last = now;
            return;
        }
        // At the goal's place (killing there, waiting for something): not stalled, whatever the distance does
        // (review Q3).
        if (now - c.last < 30000 && p.distance > 15.0 * kTileSize)
        {
            c.spent += now - c.last;
        }
        c.last = now;
        // An escort or one with a deadline: 40 min, but 20 once it has been skipped before.
        const auto before = g_orderSkips.find(p.number);
        const bool skippedBefore = before != g_orderSkips.end() && before->second.count > 0;
        if (c.spent > (p.tier >= 2 && !skippedBefore ? 2400000u : 1200000u))
        {
            orderSkip(p.number, now, p.tier >= 2 ? "gone for 40 min, no step done nor nearer"
                                                 : "gone for 20 min, no step done nor nearer");
            c.spent = 0;
        }
    }

    // A detour on the way starts or ends: the walk under way is to the other goal, cut (travelTo sends a new step only
    // with no walk routing: Estudio-rutas §3, A2 11:34:30, the detour to the giver 39 tiles off while ClickWalk went on
    // to the order's goal 454 tiles off, «over (out of reach…)» 3-156 s later). Only the agent's own walk is cut.
    void cutWalkForDetour()
    {
        if (ClickWalk::routing())
        {
            ClickWalk::cancel();
        }
    }

    bool questTarget(int32_t heroX, int32_t heroY, int32_t& x, int32_t& y, double& radius, uint32_t& who)
    {
        const DWORD now = GetTickCount();
        if (g_skipsDirty)
        {
            writeSkips(now);    // the last pass's skips (and orderFollowTick's after it)
        }
        g_questBook.clear();
        const auto begin = *reinterpret_cast<const uint8_t* const*>(0xAAD3A4);
        const auto end = *reinterpret_cast<const uint8_t* const*>(0xAAD3A8);
        constexpr size_t kRecord = 0x174;
        if (begin && end > begin && !((end - begin) % kRecord) && (end - begin) / kRecord <= 512)
        {
            int done = 0, failed = 0;
            std::vector<int32_t> failedNumbers;
            g_doneNumbers.clear();
            for (const uint8_t* r = begin; r < end; r += kRecord)
            {
                const int32_t kind = *reinterpret_cast<const int32_t*>(r), state = *reinterpret_cast<const int32_t*>(r + 4);
                done += state == 100;
                failed += state == 101;
                if (state == 100)
                {
                    g_doneNumbers.push_back(*reinterpret_cast<const int32_t*>(r + 0x08));
                }
                if (state == 101)
                {
                    failedNumbers.push_back(*reinterpret_cast<const int32_t*>(r + 0x08));
                }
                if (state != 1 && state != 2)
                {
                    continue;
                }
                const int32_t tx = *reinterpret_cast<const int32_t*>(r + 0x18), ty = *reinterpret_cast<const int32_t*>(r + 0x1C);
                if (tx <= 0 || ty <= 0)
                {
                    continue;
                }
                QuestGoal g{GoalKind::Journal};
                g.main = kind == 3;
                g.x = static_cast<int32_t>((tx + 0.5) * kTileSize);
                g.y = static_cast<int32_t>((ty + 0.5) * kTileSize);
                g.radius = std::max(2.0 * kTileSize, static_cast<double>(*reinterpret_cast<const int32_t*>(r + 0x20)));
                // +0x10/+0x14: a fixed destination's tile, -1 at +0x10 when +0x14 is the creature to speak to
                // (Manolito, 2026-11-09: the arena fight's "14a" was the tile's y, 330, not a creature).
                g.who = *reinterpret_cast<const int32_t*>(r + 0x10) == -1 ? *reinterpret_cast<const uint32_t*>(r + 0x14)
                                                                         : 0xFFFFFFFFu;
                g.titleKey = *reinterpret_cast<const uint32_t*>(r + 0x24);
                g.objectiveKey = *reinterpret_cast<const uint32_t*>(r + 0x28);
                g.number = *reinterpret_cast<const int32_t*>(r + 0x08);
                g.minutesLeft = deadlineLeft(g.number);
                g.tier = g.minutesLeft > 0 ? 2 : questPriority(g.number);
                // The book's order (Manolito, block BW: 0x6B07E0 lists tab by tab, max(u16 +0x16C, 1) - 1, each in the
                // records' order): page 1 on, top to bottom, as the owner reads it.
                g.book = (std::max<int>(*reinterpret_cast<const uint16_t*>(r + 0x16C), 1) - 1) * 1024 +
                         static_cast<int>((r - begin) / kRecord);
                g_questBook.push_back(g);
            }
            // A quest left for last because it breaks another (docs/QUESTS.md, «Reglas para el agente»: Boris
            // Richfield R06NQ02 breaks Magical Thistle R12NQ02; Collect Orc Rings DQ_10259 spoils Stolen Iron Bars
            // DQ_15015) is an ordinary one once that other is done (the quests' session, 2026-11-16: 402 open in 7
            // copies, picked by none in a day, though 702 was done in 6 of them).
            // An escort once taken is done at once, before anything else (Manolito, block BQ: 302 «Cattle
            // Thieves», its farmer follows the hero from the taking; left for another goal she follows him through
            // the wolves by her farm and dies, the quest failed though the hero is 900 tiles off: 302 failed in the
            // saves of A1, A2, A5, A6 and A8, done in A3 and A7. A4, 2026-11-16 23:17: Adelina, 201, spoken to and
            // left a second later for 203, 196 tiles off; failed 2.5 min on). By the objective's words, and those
            // whose first step reads otherwise («Encuentra a Adelina»).
            static constexpr int32_t kEscorts[] = {201, 302};
            for (QuestGoal& g : g_questBook)
            {
                if (g.kind == GoalKind::Journal && !g.main && g.tier < 2 &&
                    (std::find(std::begin(kEscorts), std::end(kEscorts), g.number) != std::end(kEscorts) ||
                     doneAtOnce(g.number) || Lore::kindOf(g.titleKey, g.objectiveKey) == Lore::QuestKind::Escort))
                {
                    g.tier = 2;
                    // Once a quest each run (two escorts open at once flipped a single «told», 2026-11-17: A5 1096
                    // lines in 3 min, 202 and 15044).
                    static std::vector<int32_t> s_told;
                    if (std::find(s_told.begin(), s_told.end(), g.number) == s_told.end())
                    {
                        s_told.push_back(g.number);
                        LOG("AutoAttack: quest {} is an escort or fails if left (a defence, a short deadline): first of "
                            "all, until done",
                            g.number);
                    }
                }
            }
            // Moca (R13NQ01) after Goods Messenger (R13NQ03): the owner did it (GAME02, 2026-11-23), held in all 8 copies.
            static constexpr std::pair<int32_t, int32_t> kAfter[] = {
                {rq(6, 2), rq(12, 2)}, {10259, 15015}, {rq(13, 1), rq(13, 3)}};
            for (QuestGoal& g : g_questBook)
            {
                for (const auto& [quest, first] : kAfter)
                {
                    if (g.number == quest && g.tier < 0 &&
                        std::find(g_doneNumbers.begin(), g_doneNumbers.end(), first) != g_doneNumbers.end())
                    {
                        g.tier = 0;
                    }
                }
            }
            // A step done or failed (the journal moved on): who was spoken to lately may have the next one at once.
            // Seen live (2026-11-09): the arena won, Julius' next quest waited out the 2 min of «spoken to lately»
            // with the hero roaming the yard.
            static bool s_journalRead = false;  // this run read the journal before (a failure is a change since)
            const bool readBefore = s_journalRead;
            s_journalRead = true;
            // The quests failed since the last read: those, not the one followed (the quests' session, 2026-11-16,
            // docs/Misiones-tope-40.md §3: A2 «gave up» main quest 44, which cannot fail, four times today for a side
            // quest failed meanwhile).
            static std::vector<int32_t> s_failedSeen;
            std::vector<int32_t> newlyFailed;
            for (const int32_t number : failedNumbers)
            {
                if (std::find(s_failedSeen.begin(), s_failedSeen.end(), number) == s_failedSeen.end())
                {
                    newlyFailed.push_back(number);
                }
            }
            s_failedSeen = failedNumbers;
            g_failedNow = failedNumbers;
            // The journal as the slot holds it, once after each load or save: a quest failed in it is failed for good.
            if (const unsigned generation = AgentSave::generation();
                generation != g_slotGeneration && !AgentSave::worldChanging())
            {
                g_slotGeneration = generation;
                for (const int32_t number : failedNumbers)
                {
                    if (std::find(g_failedInSlot.begin(), g_failedInSlot.end(), number) == g_failedInSlot.end())
                    {
                        LOG("AutoAttack: quest {} failed for good: failed in the saved game", number);
                    }
                }
                g_failedInSlot = failedNumbers;
            }
            if ((done != g_questsDone || failed != g_questsFailed) && (g_questsDone || g_questsFailed || done || failed))
            {
                LOG("AutoAttack: the journal moved on ({} done, {} failed): anyone may be spoken to again", done, failed);
                // A quest done (the count up, not the reset of a new game): the copy's game saved (the player,
                // 2026-11-11: «el momento de guardar partida tiene que ser en el momento que se supera una mision»).
                if (done == g_questsDone + 1)   // one more; a jump is the journal first read after a load
                {
                    AgentSave::questDone();
                }
                // A quest failed: a death (the player, 2026-11-11: «el fracaso cuenta como muerte»). Only one more
                // than this run read before, not the first read of a run nor right after a load.
                // More than one at a time too: none of them is let into a save. Those the slot holds (read just above
                // after a load) are not new: a save loaded with two failed in it is no death.
                std::vector<int32_t> newFails;
                for (const int32_t number : newlyFailed)
                {
                    if (std::find(g_failedInSlot.begin(), g_failedInSlot.end(), number) == g_failedInSlot.end())
                    {
                        newFails.push_back(number);
                    }
                }
                if (readBefore && failed > g_questsFailed && !newFails.empty() && !AgentSave::worldChanging())
                {
                    for (const int32_t number : newlyFailed)
                    {
                        if (std::find(g_givenUpQuests.begin(), g_givenUpQuests.end(), number) == g_givenUpQuests.end())
                        {
                            g_givenUpQuests.push_back(number);
                            LOG("AutoAttack: quest {} failed{}: left for this run", number,
                                number == g_followedNumber ? " while followed" : "");
                        }
                    }
                    // A quest's failure is paid for once (the live verifier, 2026-11-13: A7's quest with a deadline
                    // failed 3-7 min after every load, 30 failures and 14 «deaths» in 45 min, its level 11 save set
                    // aside and a new game begun): one that failed before in this run fails again after the load,
                    // and is let be, as a player does not load his game for a quest he cannot make in time.
                    bool fresh = false;
                    for (const int32_t number : newFails)
                    {
                        if (std::find(g_paidFailures.begin(), g_paidFailures.end(), number) == g_paidFailures.end())
                        {
                            g_paidFailures.push_back(number);
                            fresh = true;
                        }
                    }
                    if (!fresh && !failedNumbers.empty())
                    {
                        for (const int32_t number : newFails)
                        {
                            LOG("AutoAttack: quest {} failed for good: it failed again after its load{}", number,
                                number == g_followedNumber ? ", followed" : ", not followed");
                        }
                        LOG("AutoAttack: a quest failed again after the load ({} failed now): not counted again, left failed",
                            failed);
                    }
                    else
                    {
                        LOG("AutoAttack: a quest failed ({} failed now): as a death, the last save loaded", failed);
                        remember("falló una misión: cuenta como muerte");
                        AgentSave::questFailed();
                        // The save loaded has the quest open again (A8, 2026-11-17: the rescued girl of 1101 died with the hero,
                        // «left for this run» and the quest forgotten though the load gave it back): tried again; a second
                        // failure is let be by the branch above (paid once).
                        for (const int32_t number : newFails)
                        {
                            std::erase(g_givenUpQuests, number);
                        }
                    }
                }
                Findings::note("quest", heroX, heroY, "the journal moved on: {} done, {} failed", done, failed);
                forgetTalks();
            }
            // When a quest was last done: set at each read of the journal it was every few seconds, so neither the
            // stuck report (AgentStuck: «no quest done») nor the 8 min with no fight nor quest ever came.
            if (done > g_questsDone && readBefore)
            {
                g_questsDoneAt = GetTickCount();
            }
            g_questsDone = done;
            g_questsFailed = failed;
            g_journalSeen = true;
        }
        for (const Sign& sign : g_signs)
        {
            // A creature the journal already leads to is not a goal of its own.
            const bool known = std::any_of(g_questBook.begin(), g_questBook.end(), [&](const QuestGoal& g) {
                return g.kind == GoalKind::Journal && g.who == sign.id;
            });
            // Only signs near enough to walk to: the scan sees the whole world's creatures, and a sign thousands of
            // tiles off (seen live: 2474 and 2924 tiles, from inside the closed arena) is no goal for now.
            const double off = std::hypot(static_cast<double>(sign.x - heroX), static_cast<double>(sign.y - heroY));
            if (known || talkedLately(sign.id, now) || off > kSignRange * kTileSize)
            {
                continue;
            }
            QuestGoal g{sign.kind};
            g.x = sign.x;
            g.y = sign.y;
            g.radius = 2.0 * kTileSize;
            g.who = sign.id;
            g_questBook.push_back(g);
        }
        // Quests whose ground is far above a low hero, held until he has the level (a player comes back later): the
        // Dreamer of Winters (1002, zone 40, docs/QUESTS.md): Valoria goes to the stone circle and dies there, the
        // quest failed 35-55 s after it was taken, heroes of level 16-24 (the quests' session, 2026-11-16: A2 16:03,
        // A3 21:02 and 21:38, A4 18:22). Neither followed nor taken: its giver's sign is left too.
        // 1802 is the Dreamer of Winters (R18NQ02, zone 40). 1002 is the journal's R10NQ02 «Planes de la
        // inquisición» (zone 8-18), held too: a stealth quest, failed once its guards see the hero (docs/QUESTS.md;
        // 35-55 s after it was taken in A2, A3, A4 and A8): not for the agent until it can lure them off with the
        // bells and keep out of their sight.
        static constexpr std::pair<int32_t, int> kMinLevel[] = {{rq(18, 2), 35}, {1002, 35}};
        const int heroLv = HeroProfile::current().level;
        auto tooLow = [heroLv](int32_t number) {
            for (const auto& [quest, least] : kMinLevel)
            {
                if (number == quest && heroLv > 0 && heroLv < least)
                {
                    return true;
                }
            }
            return false;
        };
        // A quest sign at a giver's tile is that giver's quest: numbered so (the level hold and the given-up list
        // apply to it).
        for (QuestGoal& o : g_questBook)
        {
            if (o.kind != GoalKind::Offer)
            {
                continue;
            }
            for (const QuestGiver& q : kQuestGivers)
            {
                if (std::hypot(o.x / kTileSize - (q.x + 0.5), o.y / kTileSize - (q.y + 0.5)) < 6.0)
                {
                    o.number = q.number;
                    break;
                }
            }
        }
        // The givers of the quests on offer (the script's variable 1, Manolito's block BN), gone to as a player who
        // has heard of them: each until the hero comes within 20 tiles of it, where its sign, if the game shows one,
        // is seen and spoken to, or until it has been gone to for 20 min (its tile not reached: logged to study). One
        // in a region far above the hero waits, and holds nothing meanwhile; the three nearest are goals (the
        // coordinator, 2026-11-16).
        {
            static std::unordered_map<int32_t, uint32_t> s_values;
            static DWORD s_valuesAt = 0;
            static std::vector<int32_t> s_visited;
            static bool s_visitedRead = false;
            if (!s_visitedRead)
            {
                s_visitedRead = true;
                readGivers(s_visited);
            }
            if ((!s_valuesAt || now - s_valuesAt > 5000) && !AgentSave::worldChanging())
            {
                s_valuesAt = now ? now : 1;
                scriptQuestValues(s_values);
            }
            g_scriptValuesSeen = &s_values;
            g_giversVisitedSeen = &s_visited;
            g_giversLeft = 0;
            std::vector<std::pair<double, const QuestGiver*>> nearest;
            for (const QuestGiver& q : kQuestGivers)
            {
                // Not one the journal has (open, done or failed): a quest's variable is not always bits, 1 can be a
                // step of one taken (Manolito, block BP: 901's is a counter, 1 = its cave entered).
                const auto value = s_values.find(q.number);
                // A DQ_ quest (10250+) has no script variable (Manolito, block BR): on offer while the journal does not
                // have it; its giver, set up by QIS_OnSetUp<n>, may not be there at every time (then it is come to and
                // tried again later, as any giver whose quest was not taken).
                const bool onOffer = offerOrRegion(s_values, q.number);
                if (onOffer && q.number < 10000 && (value == s_values.end() || value->second != 1))
                {
                    static std::unordered_set<int32_t> s_regionTold;
                    if (s_regionTold.insert(q.number).second)
                    {
                        LOG("AutoAttack: quest {} set up when the hero enters its region: its giver at tile {},{} gone "
                            "to", q.number, q.x, q.y);
                    }
                }
                const bool inJournal =
                    std::find(g_doneNumbers.begin(), g_doneNumbers.end(), q.number) != g_doneNumbers.end() ||
                    std::find(g_failedNow.begin(), g_failedNow.end(), q.number) != g_failedNow.end() ||
                    std::any_of(g_questBook.begin(), g_questBook.end(), [&](const QuestGoal& o) {
                        return o.kind == GoalKind::Journal && o.number == q.number;
                    });
                // A giver come to whose quest was not taken (its sign not shown yet: a quest before it, the hero's
                // level) is gone to again once the hero has gained a level or done a quest since (the coordinator,
                // 2026-11-17: 40 quests so in the 8 copies, A5's 151 among them, the giver never tried again).
                if (onOffer && !inJournal)
                {
                    static std::unordered_map<int32_t, std::pair<int, int>> s_visitedWhen;    // level, quests done
                    if (const auto v = std::find(s_visited.begin(), s_visited.end(), q.number); v != s_visited.end())
                    {
                        const auto [when, fresh] = s_visitedWhen.try_emplace(q.number, heroLv, g_questsDone);
                        // A DQ_ giver may not be there when its quest is not active (QIS_OnSetUp<n>, Manolito's block
                        // BR): gone to again after 30 min too, not left for good.
                        static std::unordered_map<int32_t, DWORD> s_visitedTick;
                        const auto [tick, freshTick] = s_visitedTick.try_emplace(q.number, now);
                        const bool dqAgain = q.number >= 10000 && !freshTick && now - tick->second > 1800000;
                        if (!fresh && heroLv > 0 &&
                            (heroLv > when->second.first || g_questsDone > when->second.second || dqAgain))
                        {
                            s_visited.erase(v);
                            g_giverTime.erase(q.number);
                            LOG("AutoAttack: the giver of quest {} gone to again: the hero has gained a level or done a "
                                "quest since (level {} -> {}, quests done {} -> {})",
                                q.number, when->second.first, heroLv, when->second.second, g_questsDone);
                            s_visitedWhen.erase(when);
                            s_visitedTick.erase(tick);
                        }
                    }
                }
                if (!onOffer || inJournal ||
                    std::find(s_visited.begin(), s_visited.end(), q.number) != s_visited.end())
                {
                    continue;
                }
                const double off = std::hypot(heroX / kTileSize - (q.x + 0.5), heroY / kTileSize - (q.y + 0.5));
                const auto spent = g_giverTime.find(q.number);
                if (off < 20.0 || (spent != g_giverTime.end() && spent->second > 1200000))
                {
                    noteGiver(q.number, off < 20.0);
                    if (off < 20.0)
                    {
                        s_visited.push_back(q.number);
                        const bool signed_ = std::any_of(g_questBook.begin(), g_questBook.end(), [&](const QuestGoal& o) {
                            return o.kind == GoalKind::Offer &&
                                   std::hypot(o.x / kTileSize - (q.x + 0.5), o.y / kTileSize - (q.y + 0.5)) < 20.0;
                        });
                        if (!signed_)
                        {
                            g_giverTalks.push_back({q.number, q.x, q.y, now ? now : 1});
                        }
                        LOG("AutoAttack: the giver of quest {} at tile {},{} come to: {}", q.number, q.x, q.y,
                            signed_ ? "its sign is spoken to" : "no sign seen: the one at its tile spoken to");
                    }
                    else
                    {
                        // Skipped 30 min and tried again (the owner, 2026-11-17: «la salta, lo registra y vuelve a
                        // intentarla más tarde»), its 20 min begun anew.
                        g_giverTime.erase(q.number);
                        orderSkip(q.number, now, "its giver not reached in 20 min (to study: its layer or its way)");
                    }
                    continue;
                }
                if (orderSkipped(q.number, now))
                {
                    continue;
                }
                if ((heroLv > 0 && q.lo > heroLv + 2) || tooLow(q.number) ||
                    (doneAtOnce(q.number) && heroLv > 0 && heroLv < q.lo))
                {
                    continue;
                }
                ++g_giversLeft;
                const bool signThere = std::any_of(g_questBook.begin(), g_questBook.end(), [&](const QuestGoal& o) {
                    return o.kind == GoalKind::Offer && std::hypot(o.x / kTileSize - (q.x + 0.5), o.y / kTileSize - (q.y + 0.5)) < 20.0;
                });
                if (!signThere)
                {
                    nearest.emplace_back(off, &q);
                }
            }
            // The three first in the campaign's order (then the nearest), not the three nearest (the owner, 2026-11-17).
            std::sort(nearest.begin(), nearest.end(), [](const auto& a, const auto& b) {
                const int ra = orderRank(a.second->number), rb = orderRank(b.second->number);
                if (ra != rb)
                {
                    return (ra < 0 ? kOrderCount : ra) < (rb < 0 ? kOrderCount : rb);
                }
                return a.first < b.first;
            });
            for (size_t i = 0; i < nearest.size() && i < 3; ++i)
            {
                QuestGoal g{GoalKind::Giver};
                g.x = static_cast<int32_t>((nearest[i].second->x + 0.5) * kTileSize);
                g.y = static_cast<int32_t>((nearest[i].second->y + 0.5) * kTileSize);
                g.radius = 6.0 * kTileSize;
                g.number = nearest[i].second->number;
                // Left for last (kLast) if so (A3, 2026-11-17 00:00: the giver of 602, Boris, 586 tiles off at weight
                // 0); a quest of kFirst not yet taken waits its turn in the order like the rest.
                g.tier = std::min(0, questPriority(g.number));
                g_questBook.push_back(g);
            }
            // And any other within 40 tiles: a goal on the way (the coordinator, 2026-11-17), taken in passing; and up to
            // 8 more of the hero's level band, for the band's choice by way and place (questTarget).
            int bandMore = 0;
            for (size_t i = 3; i < nearest.size(); ++i)
            {
                const bool inBand = inLevelBand(orderRank(nearest[i].second->number), heroLv);
                if (nearest[i].first > 40.0 && !(inBand && bandMore < 8))
                {
                    continue;
                }
                bandMore += nearest[i].first > 40.0;
                QuestGoal g{GoalKind::Giver};
                g.x = static_cast<int32_t>((nearest[i].second->x + 0.5) * kTileSize);
                g.y = static_cast<int32_t>((nearest[i].second->y + 0.5) * kTileSize);
                g.radius = 6.0 * kTileSize;
                g.number = nearest[i].second->number;
                g.tier = std::min(0, questPriority(g.number));
                g_questBook.push_back(g);
            }
            // Quests on offer with no giver known (the script's own list is longer than quest_givers.inc): they hold
            // nothing, but are named every 30 min to be looked for.
            static DWORD s_unknownAt = 0;
            if (!s_values.empty() && (!s_unknownAt || now - s_unknownAt > 1800000))
            {
                s_unknownAt = now ? now : 1;
                std::string list;
                int count = 0;
                for (const auto& [number, value] : s_values)
                {
                    if (value == 1 && std::none_of(std::begin(kQuestGivers), std::end(kQuestGivers),
                                                   [number](const QuestGiver& q) { return q.number == number; }))
                    {
                        if (++count <= 40)
                        {
                            list += (list.empty() ? "" : " ") + std::to_string(number);
                        }
                    }
                }
                LOG("AutoAttack: {} quests on offer with no giver known (held for nothing; to find): {}", count, list);
            }
        }
        // C6 (docs/Criterios.md: A3 646 «off to the quest» over 326 goals): the goal followed now counts 30 % nearer, so
        // two goals at much the same way are not flipped between at each step.
        static uint32_t s_followed = 0;
        // A side quest in a region far below the hero (its enemies' top level 5 or more under the hero's) counts as
        // 2.5 times as far: done still, but after the main quest and the quests of fitting regions, which lead on to
        // where the experience is (the player, 2026-11-12: «pasar del nivel 13 es un desafío»; five heroes of level
        // 13 in regions of levels 1-10, 3 to 33 thousand experience an hour).
        const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40);
        const uint8_t* world = holder ? *reinterpret_cast<const uint8_t* const*>(holder) : nullptr;
        const int heroLevel = HeroProfile::current().level;
        // (The main quest put first for a hero who had outgrown his region, 2026-11-13, is gone: the campaign's order
        // takes the main quests in their turn, by level.)
        for (QuestGoal& g : g_questBook)
        {
            g.distance = wayLength(heroX, heroY, g.x, g.y);
            g.way = g.distance;
            g.rank = orderRank(g.number);
            if (g.rank < 0)
            {
                int glo = 0, ghi = 0;
                g.rank = world && sectorLevels(world, static_cast<int>(g.x / kTileSize), static_cast<int>(g.y / kTileSize),
                                               glo, ghi)
                             ? orderRankByLevel(glo)
                             : kOrderCount;
            }
            // Skipped a while (followed 20 min with no quest done): after the whole list until tried again.
            if (orderSkipped(g.number, now))
            {
                g.rank = kOrderCount + 1;
                g.tier = std::min(g.tier, 0);   // a kFirst one skipped too, or it stays first (review Q1)
            }
            g.blocked = goalBlocked(g.x, g.y, now) ||
                        (g.number > 0 &&
                         std::find(g_givenUpQuests.begin(), g_givenUpQuests.end(), g.number) != g_givenUpQuests.end());
            if (s_followed && (g.who ^ static_cast<uint32_t>(g.x) ^ (static_cast<uint32_t>(g.y) << 7)) == s_followed)
            {
                g.distance *= 0.7;
            }
            // The campaign's last quest (HQ_8_1_1 «Shaddar», docs/QUESTS.md) only once every other quest is done (the
            // player, 2026-11-13: «el agente solo puede superar la campaña y pasar para el próximo nivel de dificultad
            // cuando complete todas las misiones del juego»): held while the journal has a side quest open or failed,
            // or a quest is on offer anywhere known.
            if (g.main && g.kind == GoalKind::Journal)
            {
                static std::unordered_map<uint32_t, bool> s_isLast;
                auto last = s_isLast.find(g.titleKey);
                if (last == s_isLast.end())
                {
                    last = s_isLast.emplace(g.titleKey, Lore::textUtf8(g.titleKey) == "Shaddar").first;
                }
                if (last->second)
                {
                    const bool sideOpen = std::any_of(g_questBook.begin(), g_questBook.end(), [](const QuestGoal& o) {
                        return o.kind != GoalKind::Journal || !o.main;
                    });
                    // Not the quests failed for good (the coordinator, 2026-11-16: one left failed in a save held
                    // it for ever): the givers not yet come to instead.
                    if (sideOpen || !g_signs.empty() || g_giversLeft > 0)
                    {
                        g.blocked = true;
                        static DWORD s_toldAt = 0;
                        if (!s_toldAt || now - s_toldAt > 600000)
                        {
                            s_toldAt = now;
                            LOG("AutoAttack: the campaign's last quest is held: quests still open or on offer "
                                "({} goals in the book, {} signs, {} givers not come to; {} failed)",
                                g_questBook.size(), g_signs.size(), g_giversLeft, g_questsFailed);
                        }
                    }
                }
            }
            int lo = 0, hi = 0;
            if (!g.main && g.tier <= 0 && world && heroLevel > 0 &&
                sectorLevels(world, static_cast<int>(g.x / kTileSize), static_cast<int>(g.y / kTileSize), lo, hi) &&
                hi + 5 <= heroLevel)
            {
                g.distance *= 2.5;
            }
            for (const auto& [quest, level] : kMinLevel)
            {
                if (g.number == quest && heroLevel > 0 && heroLevel < level)
                {
                    g.blocked = true;
                }
            }
            // A quest taken goes before those not taken, in the book's order, only while the hero is fit for its step
            // (the owner, 2026-11-24: «el objetivo principal siempre serán las misiones, pero no se pueden hacer sin
            // fortificarse antes»): its ground more than 2 levels over the hero, or skipped a while, it waits as before.
            if (g.book >= 0 &&
                (orderSkipped(g.number, now) ||
                 (world && heroLevel > 0 && !g.main &&
                  sectorLevels(world, static_cast<int>(g.x / kTileSize), static_cast<int>(g.y / kTileSize), lo, hi) &&
                  lo > heroLevel + 2)))
            {
                g.book = -1;
            }
            // A quest done at once on offer (its sign at its giver): not taken while the hero is under its ground's
            // level, as it would have to be done there and then.
            if (g.kind == GoalKind::Offer && doneAtOnce(g.number) && heroLevel > 0)
            {
                for (const QuestGiver& q : kQuestGivers)
                {
                    if (q.number == g.number && heroLevel < q.lo)
                    {
                        g.blocked = true;
                    }
                }
            }
        }
        // The goal followed is kept until done, skipped, given up by the travel (blocked) or a goal of a higher tier
        // comes (an escort just taken): never left for another of its tier by distance or place in the order (the
        // coordinator, 2026-11-17: A3 501 -> 203 -> 402 -> 501, A5 202 <-> 701). A quest is known by its number (its
        // goal's tile moves with its steps and its escorted one), another goal by its creature and tile.
        // The level band: each goal of a quest of the hero's level band (a giver or a sign of one not taken yet only if
        // no quest before it in the order with the same giver is undone: a chain is done in its order), costed by its
        // way plus 150 tiles every 10 places after the band's first, so the order still weighs. None in the band: the
        // order's first as before (farming for its level if short of it). Those far under the hero are left to the
        // order and the goals on the way.
        int bandFirst = kOrderCount;
        for (QuestGoal& g : g_questBook)
        {
            g.band = !g.blocked && g.rank < kOrderCount && inLevelBand(g.rank, heroLevel);
            // A quest taken whose level is under the band: the band's too, cheap and safe for the hero (the owner's
            // GAME02 against the copies, 2026-11-23: 402 and 1405 open in all 8, never picked: «the level band's cheaper
            // one first» every pass, the hero at 36-38 and they at 7-12 and 18-31).
            if (!g.band && !g.blocked && g.kind == GoalKind::Journal && g.rank < kOrderCount && heroLevel > 0 &&
                kQuestOrder[g.rank].level > 0 && kQuestOrder[g.rank].level < heroLevel - kBandBelow)
            {
                g.band = true;
            }
            if (g.band && g.kind != GoalKind::Journal && g.number > 0)
            {
                const QuestGiver* mine = nullptr;
                for (const QuestGiver& q : kQuestGivers)
                {
                    if (q.number == g.number)
                    {
                        mine = &q;
                        break;
                    }
                }
                for (const QuestGiver& q : kQuestGivers)
                {
                    if (!mine || q.number == g.number || std::abs(q.x - mine->x) > 3 || std::abs(q.y - mine->y) > 3)
                    {
                        continue;
                    }
                    const int r = orderRank(q.number);
                    if (r >= 0 && r < g.rank &&
                        std::find(g_doneNumbers.begin(), g_doneNumbers.end(), q.number) == g_doneNumbers.end() &&
                        std::find(g_failedNow.begin(), g_failedNow.end(), q.number) == g_failedNow.end())
                    {
                        g.band = false;     // chained after q, not done
                        break;
                    }
                }
            }
            if (g.band)
            {
                bandFirst = std::min(bandFirst, g.rank);
            }
        }
        for (QuestGoal& g : g_questBook)
        {
            if (g.band)
            {
                g.cost = g.way / kTileSize + 150.0 * (g.rank - bandFirst) / 10.0;
            }
        }
        static int32_t s_keptNumber = 0;
        static GoalKind s_keptKind = GoalKind::Journal;
        // A quest taken from the giver gone to stays the one kept (the owner, 2026-11-24: «cuando un agente coge una
        // misión, que la empiece y la termine con persistencia»): its goal turns from Giver/Offer to Journal with the same
        // number, and by kind alone it was no longer kept, so the band's cheaper one took its place.
        const auto kept = [](const QuestGoal& o) {
            return s_keptNumber > 0
                       ? o.number == s_keptNumber &&
                             (o.kind == s_keptKind || (s_keptKind != GoalKind::Journal && o.kind == GoalKind::Journal))
                       : s_followed && (o.who ^ static_cast<uint32_t>(o.x) ^ (static_cast<uint32_t>(o.y) << 7)) == s_followed;
        };
        std::stable_sort(g_questBook.begin(), g_questBook.end(), [&kept](const QuestGoal& a, const QuestGoal& b) {
            if (a.blocked != b.blocked)
            {
                return !a.blocked;
            }
            // By tier first (an escort or a deadline, a quest lost if left, the rest, those for last), then the goal
            // followed, then the soonest deadline, the campaign's order and the nearest.
            if (a.tier != b.tier)
            {
                return a.tier > b.tier;
            }
            // Not a goal skipped (its rank after the list): kept, it stayed first though skipped (A3 501, 2026-11-17:
            // skipped by the cap at 13:14 and gone for again in the same pass, 2 h with 51 quests done)
            const bool ak = kept(a) && a.rank <= kOrderCount, bk = kept(b) && b.rank <= kOrderCount;
            if (ak != bk)
            {
                return ak;
            }
            if (a.tier == 2 && a.minutesLeft != b.minutesLeft)
            {
                return a.minutesLeft < b.minutesLeft;
            }
            // The quests taken first, in the book's order: done before more are taken from givers far off (those near are
            // taken on the way).
            if ((a.book >= 0) != (b.book >= 0))
            {
                return a.book >= 0;
            }
            if (a.book >= 0 && a.book != b.book)
            {
                return a.book < b.book;
            }
            if (a.band != b.band)
            {
                return a.band;
            }
            if (a.band && a.cost != b.cost)
            {
                return a.cost < b.cost;
            }
            if (a.rank != b.rank)
            {
                return a.rank < b.rank;
            }
            return a.distance < b.distance;
        });
        questOrderPass(now, heroLv, tooLow);
        // The quest followed until now given up by the travel (blocked) for another: counted; three times in a row with
        // no step done nor nearer, it is skipped.
        if (s_keptNumber > 0 && s_keptKind != GoalKind::Giver)
        {
            const auto prev = std::find_if(g_questBook.begin(), g_questBook.end(), [](const QuestGoal& o) {
                return o.number == s_keptNumber && o.kind == s_keptKind;
            });
            const bool left = g_questBook.empty() || g_questBook.front().number != s_keptNumber;
            if (left && prev != g_questBook.end() && prev->blocked)
            {
                if (++g_orderBlocks[s_keptNumber] >= 3)
                {
                    g_orderBlocks.erase(s_keptNumber);
                    orderSkip(s_keptNumber, now, "its way given up 3 times in a row (no way for now)");
                }
            }
        }
        if (g_questBook.empty() || g_questBook.front().blocked)
        {
            s_keptNumber = 0;
            s_followed = 0;
            g_detouring = false;
            return false;
        }
        const QuestGoal& g = g_questBook.front();
        if (g.band && (g.number != s_keptNumber || g.kind != s_keptKind))
        {
            LOG("AutoAttack: quest order: band [{},{}], picked {} (cost {:.0f}, place {}; {:.0f} tiles, the band's first "
                "place {})",
                std::max(1, heroLevel - kBandBelow), heroLevel + kBandAbove, g.number, g.cost, g.rank + 1,
                g.way / kTileSize, bandFirst + 1);
        }
        s_keptNumber = g.number;
        // A hard cap (the coordinator, 2026-11-17: «ninguna meta seguida más de 45 min sin un paso de misión hecho,
        // pase lo que pase»; A3 501, A5 701, A6 1602 followed 09:10-10:43 and never skipped: the stall clock counts only
        // steps of the quest branch, under 30 s apart, away from the goal and with no new best distance, and shops,
        // farming and recovering between them, long trips that keep getting nearer, and jams of the place kept it from
        // ever filling). Wall time by quest number since it was first followed, begun anew only when the journal moves on
        // (a quest done or failed; not a change of objective: A3's 501 went 2 h so), kept across restarts in
        // SacredBild-caps.txt; at 45 min it is set aside until 3 other quests are done or for 2 h.
        if (g.number > 0 && g.kind != GoalKind::Giver && g_journalSeen)
        {
            if (!g_capsRead)
            {
                readCaps(now);
            }
            Cap& c = g_caps[g.number];
            // Only a quest done: a failure and the load after it move the failed count up and down (A5 701, 2026-11-17:
            // «28 done, 2 failed» then «1 failed», each such change began every clock anew)
            if (!c.since || g_questsDone > c.done)
            {
                c.since = now ? now : 1;
                c.done = g_questsDone;
                c.failed = g_questsFailed;
                g_capsDirty = true;
            }
            else if (g_questsDone < c.done)
            {
                c.done = g_questsDone;  // an older save loaded: the clock goes on
                g_capsDirty = true;
            }
            if (now - c.since > 2700000)
            {
                g_caps.erase(g.number);
                g_capsDirty = true;
                orderSkip(g.number, now,
                          "followed 45 min with no quest done (the cap, whatever else; back after 3 other quests or 2 h)");
                OrderSkip& k = g_orderSkips[g.number];
                k.until = now + 7200000;
                k.until = k.until ? k.until : 1;
                k.untilDone = g_questsDone + 3;
            }
            static DWORD s_capsWritten = 0;
            if (g_capsDirty || now - s_capsWritten > 60000)
            {
                s_capsWritten = now;
                writeCaps(now);
            }
        }
        s_keptKind = g.kind;
        s_followed = g.who ^ static_cast<uint32_t>(g.x) ^ (static_cast<uint32_t>(g.y) << 7);
        g_followedNumber = g.kind == GoalKind::Journal ? g.number : 0;
        g_orderPick = {g.number, g.kind, g.tier, g.distance, g.objectiveKey};
        // On the way (the coordinator, 2026-11-17: «mientras va a la meta del orden, coger cualquier misión cuyo dador o
        // paso pendiente esté a ≤40 casillas de su ruta o posición …, sin desviarse más de eso, y volver a la meta …
        // Nada de esto cambia la meta del orden»): another goal 40 tiles or less from the hero (60 by the way), not
        // blocked nor skipped nor one left for last, nor a giver or sign of a quest done at once (taken, it would become
        // the goal), is gone to first while the order's is more than 40 tiles off. The order's goal stays the one kept,
        // its clocks waiting (not the 45 min cap). One goal on the way is kept until done, gone, out of reach or 5 min
        // spent at that step of it (then left 30 min), so two are not flipped between.
        const QuestGoal* by = nullptr;
        {
            struct Detour
            {
                DWORD spent = 0, last = 0, until = 0;
            };
            static std::unordered_map<uint64_t, Detour> s_detours;
            static uint64_t s_on = 0;
            static QuestGoal s_onLast{};    // the goal on the way as last seen in the book
            static DWORD s_goneSince = 0;   // out of the book since (0: in it)
            const auto keyOf = [](const QuestGoal& o) {
                const uint32_t id = o.number > 0 ? static_cast<uint32_t>(o.number)
                                                 : (o.who ^ static_cast<uint32_t>(o.x) ^ (static_cast<uint32_t>(o.y) << 7)) |
                                                       0x80000000u;
                return (static_cast<uint64_t>(id) << 32) | o.objectiveKey;
            };
            const auto offOf = [&](const QuestGoal& o) {
                return std::hypot(static_cast<double>(o.x - heroX), static_cast<double>(o.y - heroY)) / kTileSize;
            };
            // Why a goal is not one to go to on the way (empty: it is). Each part said apart, the way's length with it
            // (docs/Estudio-rutas.md §2.1: «its way over 60 tiles» was the catch-all, no route measured).
            const auto unfit = [&](const QuestGoal& o, double limit) -> std::string {
                if (&o == &g || (o.number > 0 && o.number == g.number))
                {
                    return "it is the order's own goal now";
                }
                if (o.blocked)
                {
                    return "blocked (no way, given up, or under its level)";
                }
                if (o.tier < 0)
                {
                    return "left for last (it breaks another quest)";
                }
                if (o.number > 0 && orderSkipped(o.number, now))
                {
                    return "skipped a while";
                }
                // A giver of a quest done at once waits for the order; its sign on the way is taken (the owner,
                // 2026-11-24, A2 1202/1303/1401 and A8 15005 «not gone to: done at once»): it is blocked while the
                // hero is under its ground's level, and taken it goes first as a deadline, as a player would.
                if (o.kind == GoalKind::Giver && o.number > 0 && doneAtOnce(o.number))
                {
                    return "a quest done at once: its giver waits for the order";
                }
                if (offOf(o) > limit)
                {
                    return std::format("{:.0f} tiles off (over {:.0f})", offOf(o), limit);
                }
                // A way round a wall or a yard in a town: 1.1-1.6 times the line (Estudio-rutas §2.4, A2's 1202 at 63
                // tiles for 40): 70 for an offer 40 off, 90 to keep on a detour.
                const double way = wayLength(heroX, heroY, o.x, o.y) / kTileSize, cap = std::max(limit * 1.5, limit + 30.0);
                if (way > cap)
                {
                    return std::format("its way {:.0f} tiles (over {:.0f})", way, cap);
                }
                return {};
            };
            const auto fits = [&](const QuestGoal& o, double limit) { return unfit(o, limit).empty(); };
            const auto kindName = [](const QuestGoal& o) {
                return o.kind == GoalKind::Journal ? (o.main ? "main quest" : "side quest")
                       : o.kind == GoalKind::Offer ? "a quest offered"
                       : o.kind == GoalKind::Giver ? "the giver of quest"
                                                   : "a report";
            };
            if (s_on)
            {
                const auto on = std::find_if(g_questBook.begin(), g_questBook.end(),
                                             [&](const QuestGoal& o) { return keyOf(o) == s_on; });
                Detour& d = s_detours[s_on];
                // Out of the book a moment: kept 10 s on toward where it was (A4, 2026-11-24 18:49-18:52: offer 15060 at
                // 27-30 tiles picked and «over, its step done or gone» 7 times in 3 min, each flip cutting the walk; a
                // giver at the edge of sight comes and goes from the goals).
                const QuestGoal* cur = nullptr;
                if (on != g_questBook.end())
                {
                    s_onLast = *on;
                    s_goneSince = 0;
                    cur = &*on;
                }
                else
                {
                    if (!s_goneSince)
                    {
                        s_goneSince = now ? now : 1;
                    }
                    if (now - s_goneSince < 10000)
                    {
                        cur = &s_onLast;
                    }
                }
                const std::string whyOver = !cur ? std::string("its step done or gone") : unfit(*cur, 60.0);
                if (!whyOver.empty())
                {
                    LOG("AutoAttack: on the way: {} over ({}, after {} s): back to the order's {}",
                        (s_on >> 32) & 0x7FFFFFFF, whyOver, d.spent / 1000, g.number);
                    // Gone for and not done (the stuck solver, 2026-11-17, A5: 10261 «at 0 tiles» and 1702 over «out of reach,
                    // blocked or skipped» after 252-299 s, picked again the same second, 6 times in 25 min with the 5 min
                    // counted only on the way that ends well): a minute or more spent on it and the goal still there is left
                    // 30 min as the 5 min would.
                    if (on != g_questBook.end() && d.spent >= 60000)
                    {
                        d.until = now + 1800000;
                    }
                    s_on = 0;
                    s_goneSince = 0;
                    cutWalkForDetour();
                }
                else
                {
                    if (now - d.last < 30000)
                    {
                        d.spent += now - d.last;
                    }
                    d.last = now;
                    if (d.spent > 300000)
                    {
                        d.until = now + 1800000;
                        LOG("AutoAttack: on the way: {} {} given 5 min with its step not done: left 30 min, back to the "
                            "order's {}",
                            kindName(*cur), cur->number, g.number);
                        s_on = 0;
                        s_goneSince = 0;
                        cutWalkForDetour();
                    }
                    else
                    {
                        by = cur;
                    }
                }
            }
            // A quest offered, a giver or a report near is gone to even when the order's goal is near too (the owner,
            // 2026-11-24: «les veo pasar de largo de muchas misiones sin aceptarlas»): a word with someone on the way, the
            // order's goal after it. A step of another quest under way still waits for the order's goal to be far.
            if (!s_on)
            {
                const bool orderFar = offOf(g) > 40.0;
                const QuestGoal* best = nullptr;
                for (const QuestGoal& o : g_questBook)
                {
                    if (!orderFar && o.kind == GoalKind::Journal)
                    {
                        continue;
                    }
                    const auto d = s_detours.find(keyOf(o));
                    if (d != s_detours.end() && d->second.until && static_cast<int>(now - d->second.until) < 0)
                    {
                        continue;
                    }
                    if (fits(o, 40.0) && (!best || offOf(o) < offOf(*best)))
                    {
                        best = &o;
                    }
                }
                if (best)
                {
                    s_on = keyOf(*best);
                    s_onLast = *best;
                    s_goneSince = 0;
                    Detour& d = s_detours[s_on];
                    if (d.until && static_cast<int>(now - d.until) >= 0)
                    {
                        d = {};     // its 30 min over: 5 min anew
                    }
                    d.last = now;
                    by = best;
                    LOG("AutoAttack: on the way: {} {} at {:.0f} tiles, then back to the order's {} ({:.0f} tiles off)",
                        kindName(*best), best->number, offOf(*best), g.number, offOf(g));
                    cutWalkForDetour();
                }
                else
                {
                    // An offer 40 tiles or less off not gone to: why, once in 5 min a quest (the owner's «pasan de largo»).
                    static std::unordered_map<int32_t, DWORD> s_toldWhy;
                    for (const QuestGoal& o : g_questBook)
                    {
                        if (o.kind != GoalKind::Offer || &o == &g || offOf(o) > 40.0)
                        {
                            continue;
                        }
                        const auto d = s_detours.find(keyOf(o));
                        std::string why = unfit(o, 40.0);
                        if (why.empty())
                        {
                            why = d != s_detours.end() && d->second.until && static_cast<int>(now - d->second.until) < 0
                                      ? "gone to before with no quest taken: left 30 min"
                                      : "none of the reasons (it fits: gone to next pass)";
                        }
                        DWORD& told = s_toldWhy[o.number];
                        if (!told || now - told > 300000)
                        {
                            told = now ? now : 1;
                            LOG("AutoAttack: on the way: quest offered {} at {:.0f} tiles not gone to: {}", o.number,
                                offOf(o), why);
                        }
                    }
                }
            }
        }
        g_detouring = by != nullptr;
        if (by)
        {
            g_detourX = by->x;
            g_detourY = by->y;
        }
        // The giver's own 20 min count only while it is the one gone to.
        if (g.kind == GoalKind::Giver && !by)
        {
            if (g_giverFollowed == g.number && now - g_giverFollowedLast < 30000)
            {
                g_giverTime[g.number] += now - g_giverFollowedLast;
            }
            g_giverFollowed = g.number;
            g_giverFollowedLast = now;
        }
        const QuestGoal& to = by ? *by : g;
        x = to.x;
        y = to.y;
        radius = to.radius;
        who = to.who;
        if (to.kind == GoalKind::Journal)
        {
            Lore::readQuest(to.titleKey, to.objectiveKey);     // the quest's title and objective read: its kind
        }
        // An escort whose escorted one is not with the hero: back for him first.
        g_escortWantType = 0;
        if (to.kind == GoalKind::Journal && to.number > 0 && to.tier >= 2 && !by && Lore::questKind() == Lore::QuestKind::Escort)
        {
            escortFetch(to.number, now, x, y, radius, who);
        }
        static uint32_t told = 0;
        const uint32_t pick = g.who ^ static_cast<uint32_t>(g.x) ^ (static_cast<uint32_t>(g.y) << 7);
        if (pick != told)
        {
            told = pick;
            LOG("AutoAttack: quest book: {} goals ({} done, {} failed), going for: {} {} (weight {}, {} game min left) "
                "at {:.0f} tiles",
                g_questBook.size(), g_questsDone, g_questsFailed,
                g.kind == GoalKind::Journal ? (g.main ? "main quest" : "side quest")
                                            : g.kind == GoalKind::Offer ? "a quest offered"
                                            : g.kind == GoalKind::Giver ? "the giver of quest" : "a report",
                g.number, g.tier, g.minutesLeft, g.distance / kTileSize);
        }
        return true;
    }

    // The goal walked to now: one on the way (questTarget's detour) if so, else the book's first.
    const QuestGoal& goalWalked()
    {
        if (g_detouring)
        {
            for (const QuestGoal& o : g_questBook)
            {
                if (o.x == g_detourX && o.y == g_detourY)
                {
                    return o;
                }
            }
        }
        return g_questBook.front();
    }

    void drawQuestBook()
    {
        ImGui::Text("Misiones hechas: %d, fallidas: %d", g_questsDone, g_questsFailed);
        if (g_questBook.empty())
        {
            ImGui::TextDisabled("Ninguna misión en curso ni ofrecida a la vista.");
            return;
        }
        if (g_orderPos)
        {
            ImGui::Text("Orden: siguiente %d, posición %d/%d", g_orderNext, g_orderPos, kOrderCount);
        }
        ImGui::TextDisabled("Escoltas y plazos primero, luego por el orden de la campaña (nivel); la primera es la que sigue el agente.");
        int n = 0;
        for (const QuestGoal& g : g_questBook)
        {
            std::string line = std::to_string(++n) + ". ";
            if (g.kind == GoalKind::Journal)
            {
                const std::string title = Lore::textUtf8(g.titleKey), objective = Lore::textUtf8(g.objectiveKey);
                line += std::string(g.main ? "[principal] " : "[secundaria] ") + (title.empty() ? "?" : title);
                if (!objective.empty())
                {
                    line += ": " + objective;
                }
            }
            else
            {
                line += g.kind == GoalKind::Offer   ? "[ofrece misión] alguien con ?!"
                        : g.kind == GoalKind::Giver ? "[dador] de la misión " + std::to_string(g.number)
                                                    : "[informar] alguien con !";
            }
            line += " (" + std::to_string(static_cast<int>(g.distance / kTileSize)) + " casillas)";
            if (g.blocked)
            {
                line += " - sin camino por ahora";
            }
            ImGui::TextWrapped("%s", line.c_str());
        }
    }

    // The quest signs for the agent's map, once a second: every creature the game marks with an overhead icon (object
    // flags +0x14 & 0x80000), its icon as npcIconId (ENG 00499E90) picks it: crafts first (creature +0x200: 0x1000
    // smith, 0x2000 merchant, 0x4000 combo master, 0x4000000 stable; none of them a quest sign), else the dialog record
    // +0x245 (u32 index, seen live 2026-11-09; 0 none) of [0xAACF80 +0x755C .. +0x7560), 0x50 bytes, icon at +0x48:
    // 0 "?!" (dialogs "auftrag*", quest offered), 1 "!" ("ziel*", report), 4/5 the others ("?"); +10 greyed (taken
    // first for «not yet for the hero»; by what was seen live, the side quests: to be confirmed by Manolito). Plus the journal's targets under way, the one the agent goes for in yellow.
    DWORD g_questMarksAt = 0;
    // The merchants in the world (creature +0x200 & 0x2000), from the same pass: where a full backpack goes.
    struct Merchant
    {
        uint32_t id;
        uint8_t layer;
        int32_t x, y;
    };
    std::vector<Merchant> g_merchants;
    // The combo masters (creature +0x200 & 0x4000): where runes of other classes are swapped for the hero's own.
    std::vector<Merchant> g_masters;
    // The smiths (+0x200 & 0x1000): where sockets are filled.
    std::vector<Merchant> g_smiths;
    // The stable men (+0x200 & 0x4000000): where a horse is bought.
    std::vector<Merchant> g_stables;

    // Farming zones, from the same pass (the object list holds the whole world): living hostile creatures on the
    // surface counted per sector (64x64 tiles), the sector's level range from its block ([sector +0x17C] +0xD3 min,
    // +0xD5 max; sector id u16 at world +0x284 + 2 * ((ty >> 6) * 128 + (tx >> 6)), sector [world +0x240][id]; seen
    // live 2026-11-09). The best: many enemies, of the hero's level, not too far.
    struct FarmCount
    {
        int count = 0;
        int64_t sumX = 0, sumY = 0;     // tiles, for where they gather
    };
    std::unordered_map<int, FarmCount> g_farmBuilding;

    // Chests not yet opened anywhere on the surface (the object list holds the whole world; opened: flags +0x14 &
    // 0x4000), the nearest kept as a place to go: no need to explore blind for them.
    uint32_t g_chestVtable = 0;
    uint32_t g_chestId = 0, g_chestBuilding = 0;
    double g_chestBest = 0.0;
    int32_t g_chestX = 0, g_chestY = 0;
    DWORD g_chestSince = 0;            // since when the hero heads for this one
    uint32_t g_chestHeading = 0;

    bool isChestClass(const uint8_t* o)
    {
        const uint32_t vtable = *reinterpret_cast<const uint32_t*>(o);
        if (g_chestVtable)
        {
            return vtable == g_chestVtable;
        }
        const auto* locator = reinterpret_cast<const CompleteObjectLocator* const*>(vtable)[-1];
        if (locator && locator->type && std::strcmp(locator->type->name, ".?AVcChest3D@@") == 0)
        {
            g_chestVtable = vtable;
            return true;
        }
        return false;
    }

    // A chest to open: a cChest3D but a town's storage chest (the hero's own store, kept on the map instead).
    bool isChest(const uint8_t* o)
    {
        if (!isChestClass(o))
        {
            return false;
        }
        if (*reinterpret_cast<const uint16_t*>(o + 0x10) == kStorageChest)
        {
            storageSeen(reinterpret_cast<cObject*>(const_cast<uint8_t*>(o)));
            return false;
        }
        return true;
    }
    bool g_farmKnown = false;
    int32_t g_farmX = 0, g_farmY = 0;   // world: the chosen zone's middle (where its enemies gather)
    int g_farmSector = -1;

    bool sectorLevels(const uint8_t* world, int tx, int ty, int& lo, int& hi)
    {
        if (!world || tx < 0 || ty < 0 || tx >= 128 * 64 || ty >= 128 * 64)
        {
            return false;
        }
        const uint16_t id = *reinterpret_cast<const uint16_t*>(world + 0x284 + 2 * ((ty >> 6) * 128 + (tx >> 6)));
        const auto table = *reinterpret_cast<const uint8_t* const* const*>(world + 0x240);
        const auto tableEnd = *reinterpret_cast<const uint8_t* const* const*>(world + 0x244);
        if (!table || id >= tableEnd - table || !table[id])
        {
            return false;
        }
        const uint8_t* block = *reinterpret_cast<const uint8_t* const*>(table[id] + 0x17C);
        if (!block)
        {
            return false;
        }
        lo = *reinterpret_cast<const uint16_t*>(block + 0xD3);
        hi = *reinterpret_cast<const uint16_t*>(block + 0xD5);
        return hi > 0;
    }

    // The region of a tile's sector (Manolito, AGENT_ADDRESSES «Dónde está el héroe»: [sector+0x17C] +0xD7, the
    // level range beside it at +0xD3/+0xD5), or -1. Regions span many sectors; the game names them by script only.
    int sectorRegion(const uint8_t* world, int tx, int ty)
    {
        if (!world || tx < 0 || ty < 0 || tx >= 128 * 64 || ty >= 128 * 64)
        {
            return -1;
        }
        const uint16_t id = *reinterpret_cast<const uint16_t*>(world + 0x284 + 2 * ((ty >> 6) * 128 + (tx >> 6)));
        const auto table = *reinterpret_cast<const uint8_t* const* const*>(world + 0x240);
        const auto tableEnd = *reinterpret_cast<const uint8_t* const* const*>(world + 0x244);
        if (!table || id >= tableEnd - table || !table[id])
        {
            return -1;
        }
        const uint8_t* block = *reinterpret_cast<const uint8_t* const*>(table[id] + 0x17C);
        return block ? *(block + 0xD7) : -1;
    }

    // The zone the hero is in (the player's wish, 2026-11-09: the agent knows which zone it is in, what it can do
    // there, and whether staying is worth it; with nothing to do there it looks for another). A zone is a region of
    // sectors; what it holds is counted from what the once-a-second scan sees: quest goals (journal and signs),
    // living enemies of a fitting level, chests not yet opened.
    struct ZoneBrief
    {
        bool valid = false;
        int region = -1, lo = 0, hi = 0, heroLevel = 0;
        int quests = 0, enemies = 0, chests = 0;
        bool worth = false;
        // With nothing here: the next zone's goal (a quest sign beyond the book's 150 tiles), if one is known.
        bool next = false;
        int nextRegion = -1;
        int32_t nextX = 0, nextY = 0;
        double nextDistance = 0.0;
        GoalKind nextKind = GoalKind::Offer;
    };
    ZoneBrief g_zone;

    void judgeZone(const uint8_t* world, int heroLevel, int32_t heroX, int32_t heroY, DWORD now)
    {
        ZoneBrief z;
        const int htx = static_cast<int>(heroX / kTileSize), hty = static_cast<int>(heroY / kTileSize);
        z.region = sectorRegion(world, htx, hty);
        if (z.region < 0)
        {
            g_zone = z;
            return;
        }
        z.valid = true;
        z.heroLevel = heroLevel;
        sectorLevels(world, htx, hty, z.lo, z.hi);
        const auto inZone = [&](int32_t x, int32_t y) {
            return sectorRegion(world, static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize)) == z.region;
        };
        for (const QuestGoal& g : g_questBook)
        {
            // Only goals the hero can go for: not parked, within 300 tiles of walking, and a side quest not from a
            // region 5+ levels below the hero (the stuck solver, 2026-11-14: A5 level 15 «worth staying» in a 6-10
            // region for 3 quests it never went for, 0 enemies of its level).
            const bool outgrown = !g.main && z.hi + 5 <= heroLevel;
            z.quests += !g.blocked && !outgrown && g.distance < 300.0 * kTileSize && inZone(g.x, g.y);
        }
        for (const auto& [key, f] : g_farmBuilding)
        {
            const int n = std::max(f.count, 1);
            const int cx = static_cast<int>(f.sumX / n), cy = static_cast<int>(f.sumY / n);
            int lo = 0, hi = 0;
            // Not far below the hero either: a level 11 Dwarf «worth staying» in a 1-4 region, 269 enemies there
            // giving next to nothing (the analyst, 2026-11-12: 54 xp/h).
            if (sectorRegion(world, cx, cy) == z.region && sectorLevels(world, cx, cy, lo, hi) && lo <= heroLevel + 5 &&
                hi + 4 >= heroLevel)
            {
                z.enemies += f.count;
            }
        }
        z.chests = g_chestBuilding && inZone(g_chestX, g_chestY) ? 1 : 0;
        z.worth = z.quests > 0 || z.enemies >= 3 || z.chests > 0;
        if (!z.worth)
        {
            // The nearest quest sign anywhere (the book keeps only those within 150 tiles), not spoken to lately and
            // not given up on by travel: the next zone to go to.
            for (const Sign& sign : g_signs)
            {
                const double d = std::hypot(static_cast<double>(sign.x - heroX), static_cast<double>(sign.y - heroY));
                if (talkedLately(sign.id, now) || goalBlocked(sign.x, sign.y, now) || (z.next && d >= z.nextDistance))
                {
                    continue;
                }
                // Not back to a region far below the hero for a quest merely offered (docs/Estudio-mejoras.md P2: the
                // Daemon, level 13, from region 2 of levels 4-7 back to region 1); a report is still handed in.
                int signLo = 0, signHi = 0;
                if (sign.kind != GoalKind::Report &&
                    sectorLevels(world, static_cast<int>(sign.x / kTileSize), static_cast<int>(sign.y / kTileSize), signLo, signHi) &&
                    signHi + 5 <= heroLevel)
                {
                    continue;
                }
                z.next = true;
                z.nextX = sign.x;
                z.nextY = sign.y;
                z.nextDistance = d;
                z.nextKind = sign.kind;
                z.nextRegion = sectorRegion(world, static_cast<int>(sign.x / kTileSize), static_cast<int>(sign.y / kTileSize));
            }
        }
        static int toldRegion = -2, toldWorth = -1, toldNext = -2;
        if (z.region != toldRegion || static_cast<int>(z.worth) != toldWorth || (!z.worth && z.nextRegion != toldNext))
        {
            toldRegion = z.region;
            toldWorth = z.worth;
            toldNext = z.nextRegion;
            if (z.worth)
            {
                LOG("Zone: region {} (levels {}-{}, hero {}): {} quest goals, {} enemies of its level, {} chests: worth "
                    "staying",
                    z.region, z.lo, z.hi, heroLevel, z.quests, z.enemies, z.chests);
            }
            else if (z.next)
            {
                LOG("Zone: region {} (levels {}-{}, hero {}): nothing to do here; next: {} in region {} at {:.0f} tiles",
                    z.region, z.lo, z.hi, heroLevel, z.nextKind == GoalKind::Report ? "a report" : "a quest offered",
                    z.nextRegion, z.nextDistance / kTileSize);
            }
            else
            {
                LOG("Zone: region {} (levels {}-{}, hero {}): nothing to do here and no other zone's goal known: "
                    "farming or exploring",
                    z.region, z.lo, z.hi, heroLevel);
            }
        }
        g_zone = z;
    }

    void drawZone()
    {
        const ZoneBrief& z = g_zone;
        if (!z.valid)
        {
            ImGui::TextDisabled("Zona aún sin leer.");
            return;
        }
        ImGui::Text("Región %d, niveles %d-%d (héroe %d)", z.region, z.lo, z.hi, z.heroLevel);
        ImGui::Text("Misiones aquí: %d   Enemigos de su nivel: %d   Cofres sin abrir: %d", z.quests, z.enemies, z.chests);
        if (z.worth)
        {
            ImGui::TextColored(ImVec4(0.5f, 1.0f, 0.5f, 1.0f), "Vale la pena quedarse.");
        }
        else if (z.next)
        {
            ImGui::TextWrapped("Nada que hacer aquí: siguiente zona, región %d (%s, %.0f casillas).", z.nextRegion,
                               z.nextKind == GoalKind::Report ? "informar" : "misión ofrecida", z.nextDistance / kTileSize);
        }
        else
        {
            ImGui::TextWrapped("Nada que hacer aquí ni otra zona con misión conocida: cultivar o explorar.");
        }
    }

    // Where the hero died lately (tiles): the farming zone it was in and where it fell, shunned 30 min (the live
    // verifier, 2026-11-11: A3 died 8 times running in the zone at 3223,2664 «levels 1-4», loaded and went back to it).
    bool nearDeathSpot(int tx, int ty)
    {
        return AgentSave::nearDeathSpot(tx, ty) || nearDangerGroup(tx, ty);
    }

    void chooseFarm(const uint8_t* world, int heroLevel, int32_t heroX, int32_t heroY)
    {
        float best = 0.0f;
        int bestKey = -1;
        int32_t bestX = 0, bestY = 0;
        int bestLo = 0, bestHi = 0, bestCount = 0;
        for (const auto& [key, f] : g_farmBuilding)
        {
            if (f.count < 3)
            {
                continue;
            }
            const int cx = static_cast<int>(f.sumX / f.count), cy = static_cast<int>(f.sumY / f.count);
            int lo = 0, hi = 0;
            if (!sectorLevels(world, cx, cy, lo, hi))
            {
                continue;
            }
            // Not a zone well above the hero's level, by the class's mind (the class strategist, 2026-11-10: the
            // Gladiator at level 1 sent to a zone of 19-32, the Daemon to one of 45-80).
            if (lo > heroLevel + Mind::now().farmLevelSlack)
            {
                continue;
            }
            if (nearDeathSpot(cx, cy) || (Config::autoAttack.noLostFights && nearHopelessSpot(cx, cy, GetTickCount())))
            {
                continue;
            }
            if (inVetoedCircle(cx, cy, GetTickCount(), 900000))
            {
                continue;
            }
            // Careful (2+ deaths from the same save): only ground whose enemies the hero tops or matches (the analyst,
            // 2026-11-11: the Mage, level 3 with 102 health, sent to a zone of levels 4-7 and dead 15 times running).
            if (AgentSave::deathsSinceSave() >= 2 && hi > heroLevel + 1)
            {
                continue;
            }
            if (outmatched(GetTickCount()) && hi > heroLevel)
            {
                continue;
            }
            // Of its level: full worth; below it less and less (little experience); well above it, risky.
            float fit = 1.0f;
            if (heroLevel > hi)
            {
                // Over 4 levels below: next to no experience, a last resort only (A7, level 11, in a 1-4 zone).
                fit = hi + 4 < heroLevel ? 0.03f : std::max(0.15f, static_cast<float>(hi) / static_cast<float>(heroLevel));
            }
            else if (lo > heroLevel + 5)
            {
                fit = 0.25f;
            }
            double tiles = std::hypot(cx - heroX / kTileSize, cy - heroY / kTileSize);
            if (tiles < 300.0)
            {
                // The walk there, not the straight line.
                tiles = wayLength(heroX, heroY, static_cast<int32_t>((cx + 0.5) * kTileSize),
                                  static_cast<int32_t>((cy + 0.5) * kTileSize)) / kTileSize;
            }
            float score = static_cast<float>(f.count) * fit / static_cast<float>(1.0 + tiles / 150.0);
            if (key == g_farmSector)
            {
                score *= 1.5f;      // the zone chosen stays unless another is clearly better
            }
            if (score > best)
            {
                best = score;
                bestKey = key;
                bestX = static_cast<int32_t>((cx + 0.5) * kTileSize);
                bestY = static_cast<int32_t>((cy + 0.5) * kTileSize);
                bestLo = lo;
                bestHi = hi;
                bestCount = f.count;
            }
        }
        g_farmKnown = bestKey >= 0;
        if (g_farmKnown)
        {
            if (bestKey != g_farmSector)
            {
                LOG("AutoAttack: farming zone at tile {},{}: {} enemies, levels {}-{} (hero {}), {:.0f} tiles away",
                    static_cast<int>(bestX / kTileSize), static_cast<int>(bestY / kTileSize), bestCount, bestLo, bestHi,
                    heroLevel, std::hypot(static_cast<double>(bestX - heroX), static_cast<double>(bestY - heroY)) / kTileSize);
                g_farmSector = bestKey;
            }
            g_farmX = bestX;
            g_farmY = bestY;
        }
    }


    // The door or way in the agent heads for (an interior, a quest's house), for the overlay; 0 at none.
    int32_t g_doorX = 0, g_doorY = 0;
    DWORD g_doorAt = 0;

    void noteDoor(int tx, int ty)
    {
        g_doorX = static_cast<int32_t>((tx + 0.5) * kTileSize);
        g_doorY = static_cast<int32_t>((ty + 0.5) * kTileSize);
        g_doorAt = GetTickCount();
    }

    void scanQuestMarks(DWORD now, int32_t heroX, int32_t heroY, int heroLevel, uint8_t heroLayer)
    {
        if (g_questMarksAt && now - g_questMarksAt < 1000)
        {
            return;
        }
        g_questMarksAt = now;
        g_signs.clear();
        // The givers to speak to with no sign (g_giverTalks): the living creature, not of the hero's side nor a horse or an animal, nearest the
        // giver's tile within 3 tiles on the hero's layer, as an offer's sign for 2 min.
        std::erase_if(g_giverTalks, [now](const GiverTalk& t) { return now - t.since > 120000; });
        if (!g_giverTalks.empty())
        {
            const auto om = *reinterpret_cast<const uint8_t* const*>(0xAD5C40);
            const auto first = om ? *reinterpret_cast<const uint8_t* const* const*>(om + 4) : nullptr;
            const auto last = om ? *reinterpret_cast<const uint8_t* const* const*>(om + 8) : nullptr;
            for (const GiverTalk& t : g_giverTalks)
            {
                const uint8_t* best = nullptr;
                double bestOff = 3.0;
                for (const uint8_t* const* it = first; first && last > first && last - first < 0x40000 && it < last; ++it)
                {
                    const uint8_t* o = *it;
                    // The side read only once the entry is known to be a creature (A8, 2026-11-23: three crashes at
                    // DDRAW.dll+47694 in 17 min, the side read first from an entry that was no object, past its page).
                    if (!o || *reinterpret_cast<const uint32_t*>(o) < 0x880000 || *reinterpret_cast<const uint32_t*>(o) >= 0x8A0000 ||
                        (*reinterpret_cast<const uint32_t*>(o + 0xC) & 0xFFFF) != static_cast<uint32_t>(it - first) ||
                        !reinterpret_cast<cObject*>(const_cast<uint8_t*>(o))->asCreature() ||
                        *reinterpret_cast<const int32_t*>(o + 0x4D8) <= 0)
                    {
                        continue;
                    }
                    const uint32_t side = *reinterpret_cast<const uint32_t*>(o + 0x1F0);   // 1 the hero's, 4 horses, 6 animals
                    if (side == 1 || side == 4 || side == 6)
                    {
                        continue;
                    }
                    const double off = std::hypot(*reinterpret_cast<const int32_t*>(o + 0x1C) / kTileSize - (t.tx + 0.5),
                                                  *reinterpret_cast<const int32_t*>(o + 0x20) / kTileSize - (t.ty + 0.5));
                    if (off < bestOff)
                    {
                        best = o;
                        bestOff = off;
                    }
                }
                const uint32_t id = best ? *reinterpret_cast<const uint32_t*>(best + 0xC) : 0;
                if (!id)
                {
                    continue;
                }
                const auto spoken = g_giverSpokenAt.find(id);
                if (spoken != g_giverSpokenAt.end() && spoken->second != t.since && now - spoken->second < 600000)
                {
                    continue;   // spoken to for another giver's visit in the last 10 min
                }
                if (spoken == g_giverSpokenAt.end() || spoken->second != t.since)
                {
                    g_giverSpokenAt[id] = t.since;
                    LOG("AutoAttack: quest {}: {:x} at the giver's tile {},{} spoken to (no sign seen)", t.number, id, t.tx,
                        t.ty);
                }
                g_signs.push_back({GoalKind::Offer, id, *reinterpret_cast<const int32_t*>(best + 0x1C),
                                   *reinterpret_cast<const int32_t*>(best + 0x20)});
            }
        }
        std::vector<MapMemory::QuestMark> marks;
        g_merchants.clear();
        g_masters.clear();
        g_smiths.clear();
        g_stables.clear();
        g_wildHorses.clear();
        g_farmBuilding.clear();
        g_chestBuilding = 0;
        g_chestBest = 0.0;
        g_aggroFoes.clear();
        g_aggroHeroX = heroX;
        g_aggroHeroY = heroY;
        const auto manager = *reinterpret_cast<const uint8_t* const*>(0xAD5C40);
        const auto dialogs = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x755C);
        const auto dialogsEnd = *reinterpret_cast<const uint8_t* const*>(0xAACF80 + 0x7560);
        if (manager && dialogs && dialogsEnd > dialogs)
        {
            const size_t dialogCount = static_cast<size_t>(dialogsEnd - dialogs) / 0x50;
            const auto table = *reinterpret_cast<const uint8_t* const* const*>(manager + 4);
            const auto tableEnd = *reinterpret_cast<const uint8_t* const* const*>(manager + 8);
            if (table && tableEnd > table && tableEnd - table < 0x40000)
            {
                for (const uint8_t* const* it = table; it < tableEnd; ++it)
                {
                    const uint8_t* o = *it;
                    // A living hostile creature on the surface, for the farming zones and the aggro rings: hostile
                    // to the hero's side (1) by the game's own live side matrix (Manolito, 2026-11-10: u8
                    // [0x8EB548 + a*16 + b], 0 hostile; by default 0, 3 civilians, 4 horses, 6 animals such as
                    // rabbits and 7 soldiers are not).
                    if (o && *reinterpret_cast<const uint32_t*>(o) >= 0x880000 && *reinterpret_cast<const uint32_t*>(o) < 0x8A0000 &&
                        (*reinterpret_cast<const uint32_t*>(o + 0xC) & 0xFFFF) == static_cast<uint32_t>(it - table) &&
                        !*(o + 0x24) && reinterpret_cast<cObject*>(const_cast<uint8_t*>(o))->asCreature() &&
                        *reinterpret_cast<const int32_t*>(o + 0x4D8) > 0)
                    {
                        const uint32_t side = *reinterpret_cast<const uint32_t*>(o + 0x1F0);
                        const auto* sides = reinterpret_cast<const uint8_t*>(0x8EB548);
                        if (side == 4 && heroLayer == 0 && !*reinterpret_cast<const uint32_t*>(o + 0x570))
                        {
                            const int32_t hx = *reinterpret_cast<const int32_t*>(o + 0x1C), hy = *reinterpret_cast<const int32_t*>(o + 0x20);
                            if (std::hypot(static_cast<double>(hx - heroX), static_cast<double>(hy - heroY)) < 25.0 * kTileSize)
                            {
                                g_wildHorses.push_back({*reinterpret_cast<const uint32_t*>(o + 0xC), hx, hy, Gear::horseWorth(o)});
                            }
                        }
                        if (side < 16 && side != 1 && sides[16 + side] == 0)
                        {
                            const int tx = static_cast<int>(*reinterpret_cast<const int32_t*>(o + 0x1C) / kTileSize);
                            const int ty = static_cast<int>(*reinterpret_cast<const int32_t*>(o + 0x20) / kTileSize);
                            const int32_t fx = *reinterpret_cast<const int32_t*>(o + 0x1C);
                            const int32_t fy = *reinterpret_cast<const int32_t*>(o + 0x20);
                            if (heroLayer == 0 && std::hypot(static_cast<double>(fx - heroX), static_cast<double>(fy - heroY)) <
                                                      40.0 * kTileSize)
                            {
                                const int32_t target = *reinterpret_cast<const int32_t*>(o + 0x251);
                                const uint32_t ai = *reinterpret_cast<const uint32_t*>(o + 0x1F4);
                                g_aggroFoes.push_back({static_cast<uint32_t>(it - table), fx, fy, target >= 1 && target <= 0x10 && (ai & 4) && !(ai & 0x100)});
                            }
                            FarmCount& f = g_farmBuilding[(tx >> 6) * 1024 + (ty >> 6)];
                            ++f.count;
                            f.sumX += tx;
                            f.sumY += ty;
                        }
                    }
                    // The escorted one looked for (escortFetch): a living creature of its type on the surface.
                    if (g_escortWantType && o && *reinterpret_cast<const uint32_t*>(o) >= 0x880000 &&
                        *reinterpret_cast<const uint32_t*>(o) < 0x8A0000 &&
                        (*reinterpret_cast<const uint32_t*>(o + 0xC) & 0xFFFF) == static_cast<uint32_t>(it - table) &&
                        !*(o + 0x24) && reinterpret_cast<cObject*>(const_cast<uint8_t*>(o))->asCreature() &&
                        *reinterpret_cast<const int32_t*>(o + 0x4D8) > 0 &&
                        *reinterpret_cast<const uint32_t*>(o + 0x10) == g_escortWantType)
                    {
                        g_escortSeen = {*reinterpret_cast<const uint32_t*>(o + 0xC), g_escortWantType,
                                        *reinterpret_cast<const int32_t*>(o + 0x1C), *reinterpret_cast<const int32_t*>(o + 0x20), now};
                    }
                    if (o && *reinterpret_cast<const uint32_t*>(o) >= 0x880000 && *reinterpret_cast<const uint32_t*>(o) < 0x8A0000 &&
                        (*reinterpret_cast<const uint32_t*>(o + 0xC) & 0xFFFF) == static_cast<uint32_t>(it - table) &&
                        !*(o + 0x24) && isChest(o) && !(*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x4000))
                    {
                        const uint32_t id = *reinterpret_cast<const uint32_t*>(o + 0xC);
                        double d = std::hypot(static_cast<double>(*reinterpret_cast<const int32_t*>(o + 0x1C) - heroX),
                                              static_cast<double>(*reinterpret_cast<const int32_t*>(o + 0x20) - heroY));
                        if (d < 150.0 * kTileSize && !lootBlocked(id, now) && !g_lootDone.count(lootKey(id)))
                        {
                            d = wayLength(heroX, heroY, *reinterpret_cast<const int32_t*>(o + 0x1C),
                                          *reinterpret_cast<const int32_t*>(o + 0x20));    // the walk
                        }
                        if (!lootBlocked(id, now) && !g_lootDone.count(lootKey(id)) && (!g_chestBuilding || d < g_chestBest))
                        {
                            g_chestBuilding = id;
                            g_chestBest = d;
                            g_chestX = *reinterpret_cast<const int32_t*>(o + 0x1C);
                            g_chestY = *reinterpret_cast<const int32_t*>(o + 0x20);
                        }
                    }
                    if (o && (*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x80000) &&
                        (*reinterpret_cast<const uint32_t*>(o + 0x200) & 0x2000))
                    {
                        g_merchants.push_back({*reinterpret_cast<const uint32_t*>(o + 0xC), *(o + 0x24),
                                               *reinterpret_cast<const int32_t*>(o + 0x1C),
                                               *reinterpret_cast<const int32_t*>(o + 0x20)});
                    }
                    if (o && (*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x80000) &&
                        (*reinterpret_cast<const uint32_t*>(o + 0x200) & 0x4000))
                    {
                        g_masters.push_back({*reinterpret_cast<const uint32_t*>(o + 0xC), *(o + 0x24),
                                             *reinterpret_cast<const int32_t*>(o + 0x1C),
                                             *reinterpret_cast<const int32_t*>(o + 0x20)});
                    }
                    if (o && (*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x80000) &&
                        (*reinterpret_cast<const uint32_t*>(o + 0x200) & 0x1000))
                    {
                        g_smiths.push_back({*reinterpret_cast<const uint32_t*>(o + 0xC), *(o + 0x24),
                                            *reinterpret_cast<const int32_t*>(o + 0x1C),
                                            *reinterpret_cast<const int32_t*>(o + 0x20)});
                    }
                    if (o && (*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x80000) &&
                        (*reinterpret_cast<const uint32_t*>(o + 0x200) & 0x4000000))
                    {
                        g_stables.push_back({*reinterpret_cast<const uint32_t*>(o + 0xC), *(o + 0x24),
                                             *reinterpret_cast<const int32_t*>(o + 0x1C),
                                             *reinterpret_cast<const int32_t*>(o + 0x20)});
                    }
                    if (!o || !(*reinterpret_cast<const uint32_t*>(o + 0x14) & 0x80000) ||
                        (*reinterpret_cast<const uint32_t*>(o + 0x200) & (0x1000 | 0x2000 | 0x4000 | 0x4000000)))
                    {
                        continue;
                    }
                    const uint32_t dialog = *reinterpret_cast<const uint32_t*>(o + 0x245);
                    if (!dialog || dialog >= dialogCount)
                    {
                        continue;
                    }
                    const uint32_t icon = *reinterpret_cast<const uint32_t*>(dialogs + dialog * 0x50 + 0x48);
                    MapMemory::Glyph glyph;
                    switch (icon % 10)
                    {
                    case 0: glyph = MapMemory::Glyph::Offer; break;
                    case 1: glyph = MapMemory::Glyph::Report; break;
                    case 4:
                    case 5: glyph = MapMemory::Glyph::Other; break;
                    default: continue;
                    }
                    if (icon >= 20)
                    {
                        continue;
                    }
                    marks.push_back({glyph, icon < 10, *(o + 0x24), *reinterpret_cast<const int32_t*>(o + 0x1C),
                                     *reinterpret_cast<const int32_t*>(o + 0x20)});
                    // A quest to take or a report to make, yellow or grey: the yellow ones are the main quest's (seen live
                    // 2026-11-09: the only yellow sign was the Vampiress's main quest giver), the grey ones the side quests
                    // (up to 7 in a town, never spoken to: the player saw no side quest taken).
                    // One on the other layer (a floor up, inside a house) within 30 tiles too: a click on it sends the hero
                    // there by the game's own path through the doors, as for a merchant in a house (the quests study,
                    // 2026-11-23: the givers of 15001 and 15029 stand on layer 1, DefPos «3216,2513,0,1», and were never
                    // seen from the street).
                    if ((*(o + 0x24) == heroLayer ||
                         std::hypot(*reinterpret_cast<const int32_t*>(o + 0x1C) - heroX,
                                    *reinterpret_cast<const int32_t*>(o + 0x20) - heroY) < 30.0 * kTileSize) &&
                        (glyph == MapMemory::Glyph::Offer || glyph == MapMemory::Glyph::Report))
                    {
                        g_signs.push_back({glyph == MapMemory::Glyph::Offer ? GoalKind::Offer : GoalKind::Report,
                                           *reinterpret_cast<const uint32_t*>(o + 0xC), *reinterpret_cast<const int32_t*>(o + 0x1C),
                                           *reinterpret_cast<const int32_t*>(o + 0x20)});
                    }
                }
            }
        }
        learnEscortee(now);
        // The journal: every quest under way, its target a ring; the agent's own (questTarget's pick) in yellow.
        int32_t gx = 0, gy = 0;
        double radius = 0.0;
        uint32_t who = 0;
        const bool goal = questTarget(heroX, heroY, gx, gy, radius, who);
        const auto begin = *reinterpret_cast<const uint8_t* const*>(0xAAD3A4);
        const auto end = *reinterpret_cast<const uint8_t* const*>(0xAAD3A8);
        constexpr size_t kRecord = 0x174;
        if (begin && end > begin && !((end - begin) % kRecord) && (end - begin) / kRecord <= 512)
        {
            for (const uint8_t* r = begin; r < end; r += kRecord)
            {
                const int32_t state = *reinterpret_cast<const int32_t*>(r + 4);
                const int32_t tx = *reinterpret_cast<const int32_t*>(r + 0x18), ty = *reinterpret_cast<const int32_t*>(r + 0x1C);
                if ((state != 1 && state != 2) || tx <= 0 || ty <= 0)
                {
                    continue;
                }
                const int32_t wx = static_cast<int32_t>((tx + 0.5) * kTileSize), wy = static_cast<int32_t>((ty + 0.5) * kTileSize);
                marks.push_back({MapMemory::Glyph::Target, goal && wx == gx && wy == gy, 0, wx, wy});
            }
        }
        // Told when what it knows changes: signs within 60 tiles by kind, and the journal's targets.
        {
            int close[3] = {}, yellow = 0, targets = 0;
            for (const MapMemory::QuestMark& q : marks)
            {
                if (q.glyph == MapMemory::Glyph::Target)
                {
                    ++targets;
                }
                else if (std::hypot(static_cast<double>(q.x - heroX), static_cast<double>(q.y - heroY)) < 60 * kTileSize)
                {
                    ++close[static_cast<int>(q.glyph)];
                    yellow += q.yellow;
                }
            }
            static int told = -1;
            const int seen = close[0] | close[1] << 8 | close[2] << 16 | yellow << 24 | targets << 28;
            if (seen != told)
            {
                told = seen;
                LOG("AutoAttack: quest signs within 60 tiles: {} ?!, {} !, {} ? ({} yellow); {} quests under way; {} "
                    "merchants known",
                    close[0], close[1], close[2], yellow, targets, g_merchants.size());
            }
        }
        chooseFarm(manager ? *reinterpret_cast<const uint8_t* const*>(manager) : nullptr, heroLevel, heroX, heroY);
        g_chestId = g_chestBest < 150.0 * kTileSize ? g_chestBuilding : 0;
        judgeZone(manager ? *reinterpret_cast<const uint8_t* const*>(manager) : nullptr, heroLevel, heroX, heroY, now);
        MapMemory::setQuestMarks(std::move(marks));
        // A stable within 60 tiles selling a horse clearly better than the hero's (two levels or more): Gear goes to
        // buy it (the player, 2026-11-10: compare before changing horses).
        {
            bool better = false;
            cObjectManager* om = cObjectManager::instance();
            const cCreature* hero = om ? om->hero() : nullptr;
            const uint32_t ownId = hero ? *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x570) : 0;
            const cCreature* own = ownId ? om->creature(ownId) : nullptr;
            if (own)
            {
                const int ownWorth = Gear::horseWorth(own);
                for (const Merchant& m : g_stables)
                {
                    const auto* man = reinterpret_cast<const uint8_t*>(om->object(m.id));
                    const uint32_t sale = man ? *reinterpret_cast<const uint32_t*>(man + 0x570) : 0;
                    // Only a horse still for sale: bound to the man both ways (its +0x570 the man, as buyHorse checks)
                    // and not the hero's own (A8, 2026-11-16: «a better horse there» every 30 min, then the hero's
                    // own a7 shown at the stable and nothing bought).
                    const cCreature* h = sale && sale != ownId ? om->creature(sale) : nullptr;
                    if (h && *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(h) + 0x570) != m.id)
                    {
                        h = nullptr;
                    }
                    if (h && std::hypot(static_cast<double>(m.x - heroX), static_cast<double>(m.y - heroY)) < 60.0 * kTileSize &&
                        wayLength(heroX, heroY, m.x, m.y) < 60.0 * kTileSize && Gear::horseWorth(h) >= ownWorth + 2000)
                    {
                        if (!better)
                        {
                            static uint32_t s_toldSale = 0;
                            if (s_toldSale != sale)
                            {
                                s_toldSale = sale;
                                LOG("Gear: the stable man {:x} sells horse {:x} (worth {}) against the hero's {:x} (worth {})",
                                    m.id, sale, Gear::horseWorth(h), ownId, ownWorth);
                            }
                        }
                        better = true;
                    }
                }
            }
            Gear::setHorseUpgrade(better);
        }
    }

    DWORD g_questAskAt = 0;
    // The merchant trip (Gear::wantsShop): the merchant gone to, when the walk and the click were last asked for.
    uint32_t g_shopId = 0;
    DWORD g_shopAskAt = 0, g_shopClickAt = 0;
    int g_shopTries = 0;
    bool g_shopTold = false;
    std::unordered_map<uint32_t, DWORD> g_shopFailedAt;     // merchants that would not open: left 5 min
    std::unordered_map<uint32_t, DWORD> g_shopUselessAt;    // merchants that took nothing of the backpack: left 30 min
    // The trip to a merchant must get nearer: not 15 tiles nearer in 150 s and the merchant is left 30 min (the stuck
    // solver, 2026-11-16, A6 on a landmass its map shows shut in by water: the choice flipped between merchants 114 and
    // 114 tiles off, or 2883,2889 and 2771,2608 at 245 and 245, every 5-15 s, each flip a new goal for `travel`, whose
    // 20 s «no nearer» clock then never ran: 40 min of «off to the merchant»).
    struct ShopWatch
    {
        uint64_t key = 0;
        DWORD since = 0;
        double startWay = 0.0;
    };
    bool shopNoProgress(ShopWatch& w, uint64_t key, double way, DWORD now)
    {
        if (w.key != key)
        {
            w.key = key;
            w.since = now;
            w.startWay = way;
            return false;
        }
        if (way < w.startWay - 15.0 * kTileSize)
        {
            w.since = now;
            w.startWay = way;
            return false;
        }
        return now - w.since > 150000;
    }
    // Two merchants given up as «no nearer in 150 s» within 15 min: the rest lie across the same barrier (the stuck solver,
    // 2026-11-17, A3: a Battle Mage of level 21, no potion, loaded on a shore at 1599,3064 with the lake between it and
    // seven remembered merchants 205-244 tiles east; each tried 150 s and left 30 min, one after the other, for 22+ min,
    // the stuck guard walking about the shore between them; the quest order's 20 min never ran, the hero never on the
    // quest branch). The trip is left 10 min (the farming zone 132 tiles west was fine) and the places beyond are tried
    // again then, with whatever the hero has seen of the way round.
    bool shopStalledTwice(DWORD now)
    {
        static DWORD s_first = 0;
        static int s_count = 0;
        if (!s_first || now - s_first > 900000)
        {
            s_first = now;
            s_count = 0;
        }
        if (++s_count < 2)
        {
            return false;
        }
        s_first = 0;
        return true;
    }

    // No merchant to be reached: the nearest way in or out the map knows (a portal, a door, a cave) within 400 tiles, each
    // tried once in 20 min, walked to for 3 min.
    DWORD g_exitUntil = 0;
    int32_t g_exitX = 0, g_exitY = 0;
    std::unordered_map<uint64_t, DWORD> g_exitTriedAt;
    void armExit(DWORD now, const cCreature* self, int layer)
    {
        const int tx = static_cast<int>(self->x / kTileSize), ty = static_cast<int>(self->y / kTileSize);
        double best = 1e18;
        int bx = 0, by = 0;
        bool found = false;
        for (const auto& [x, y] : MapMemory::waysOut(layer, tx, ty, 400))
        {
            const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(x)) << 32) | static_cast<uint32_t>(y);
            if (const auto t = g_exitTriedAt.find(key); t != g_exitTriedAt.end() && now - t->second < 1200000)
            {
                continue;
            }
            const double d = std::hypot(static_cast<double>(x - tx), static_cast<double>(y - ty));
            // Not across water the map knows (the stuck solver, 2026-11-16, A6: the portal 3180,2672 26 tiles off over a
            // river 7-10 tiles wide, the entrance 3094,2784 over the water band 2677-2683: «no nearer to tile 3180,2672 in
            // 20 s», 40 min on the bank): 40 samples along the straight line, four of them not walkable is a river.
            int wet = 0;
            for (int k = 1; k <= 40 && wet < 4; ++k)
            {
                const double f = k / 41.0;
                wet += ClickWalk::walkable(layer, static_cast<int>(tx + (x - tx) * f), static_cast<int>(ty + (y - ty) * f)) == 0;
            }
            if (wet >= 4)
            {
                continue;
            }
            if (d < best)
            {
                best = d;
                bx = x;
                by = y;
                found = true;
            }
        }
        if (!found)
        {
            return;
        }
        g_exitTriedAt[(static_cast<uint64_t>(static_cast<uint32_t>(bx)) << 32) | static_cast<uint32_t>(by)] = now;
        g_exitX = static_cast<int32_t>((bx + 0.5) * kTileSize);
        g_exitY = static_cast<int32_t>((by + 0.5) * kTileSize);
        g_exitUntil = now + 180000;
        LOG("AutoAttack: no merchant gets nearer in 150 s: out by the way in or out at {},{} ({:.0f} tiles)", bx, by, best);
    }
    int32_t g_questX = 0, g_questY = 0;

    // Speaking to the quest's creature (the quest giver, or whom to report to): a click on it, as the player's, then
    // its dialog answered with the first answer (Enter: accept, go on, report) until it closes. Not again for a
    // while after (the journal moves on to the next target once the script took it).
    // A creature's side (+0x1F0, seen live 2026-11-09): 1 hero, 3 civilians, 4 horses, 7 soldiers are spoken to.
    constexpr size_t kSide = 0x1F0;
    constexpr DWORD kTalkAgainMs = 120000;
    // Creatures that would not speak, and how often: each time four times as long before the next try (2, 8, 32 min,
    // then left for good). Seen live (2026-11-10, the analyst): a hireling for hire taken for the quest creature, 41
    // tries in 24 minutes.
    std::unordered_map<uint32_t, int> g_talkFails;
    uint32_t g_talkId = 0;
    DWORD g_talkAt = 0;
    int g_talkTries = 0;
    std::unordered_map<uint32_t, DWORD> g_talkedAt;

    bool talkable(cObject* object)
    {
        if (!object || !object->asCreature())
        {
            return false;
        }
        const uint32_t side = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(object) + kSide);
        return side == 1 || side == 3 || side == 4 || side == 7;
    }

    // A long walk (to a quest, a farming zone, a merchant) watched for progress: ClickWalk can stay on its route with
    // the hero shaking on one spot (seen live 2026-11-09, 194 tiles to a quest). No 2 tiles nearer in 20 s: the route
    // dropped and a step aside (8 tiles, a random way) before trying again; the third time the goal is left 3 min.
    struct Travel
    {
        int32_t x = 0, y = 0;
        double best = 0.0;
        DWORD bestAt = 0, lastAt = 0, detourUntil = 0;
        int fails = 0;
        int32_t movedX = 0, movedY = 0;     // where the hero last was 3 tiles on along a route
        DWORD aroundSince = 0;              // since when moving along a route with no nearer for it (0: not)
        float bestLeft = -1.0f;             // the fewest tiles left of the route net's trip so far (-1: none)
    };
    Travel g_travel;

    // A way round (a gate, a bridge, a river's bend: the player, 2026-11-11, «el agente continúa con problemas con
    // las puertas»): along a route the straight line may grow before it shrinks. A hero 3 tiles on from where it was,
    // following ClickWalk's route, is making progress, for up to 2 min with the goal no nearer.
    bool goingAround(int32_t& movedX, int32_t& movedY, DWORD& since, const cCreature* self, DWORD now)
    {
        if (!self || !ClickWalk::routing())
        {
            return false;
        }
        if (std::hypot(static_cast<double>(self->x - movedX), static_cast<double>(self->y - movedY)) < 3.0 * kTileSize)
        {
            return false;
        }
        movedX = self->x;
        movedY = self->y;
        if (!since)
        {
            since = now;
        }
        return now - since < 120000;
    }
    std::unordered_map<uint64_t, DWORD> g_travelBlocked;

    bool goalBlocked(int32_t x, int32_t y, DWORD now)
    {
        const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(x / kTileSize)) << 32) |
                             static_cast<uint32_t>(y / kTileSize);
        const auto it = g_travelBlocked.find(key);
        return it != g_travelBlocked.end() && static_cast<int>(now - it->second) < 0;
    }

    // A walk to a near tile that gets no nearer (seen live: 5 min at 24 tiles from a tile the fill reached but the
    // game's path finder does not): true once 20 s pass without a tile of progress; that tile is then left 2 min.
    bool approachStalled(int32_t wx, int32_t wy, double distance, DWORD now)
    {
        static uint64_t s_key = 0;
        static double s_best = 0.0;
        static DWORD s_since = 0;
        static std::unordered_map<uint64_t, DWORD> s_left;
        // C5 (docs/Criterios.md: 87 stucks, A3 11 times at 3320,2679, the same goal 4-6 times): by a cell of 6 tiles,
        // not the exact tile, so the next tile beside it does not start the count again.
        const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(wx / (6 * kTileSize))) << 32) |
                             static_cast<uint32_t>(wy / (6 * kTileSize));
        // Each time again no nearer, left longer (the analyst, 2026-11-11: 333 «no nearer» in 3 h over the 8 copies,
        // ~1.9 h lost, the same tiles again and again, 3174,2794 39 times in one copy): 2, 10, 30 min, then an hour.
        static std::unordered_map<uint64_t, int> s_times;
        static std::unordered_set<uint64_t> s_offFor;     // tiles tried again on foot already
        // Kept on disk beside the game (SacredBild-parked2.txt: key, times), so a restart does not try them all again
        // (the analyst, 2026-11-11: the count of «no nearer» went up with each reinstall).
        static std::wstring s_file;
        if (s_file.empty())
        {
            wchar_t exe[MAX_PATH] = {};
            GetModuleFileNameW(nullptr, exe, MAX_PATH);
            s_file = exe;
            s_file = s_file.substr(0, s_file.find_last_of(L"\\/") + 1) + L"SacredBild-parked2.txt";
            if (FILE* f = _wfopen(s_file.c_str(), L"rb"))
            {
                unsigned long long k = 0;
                int n = 0;
                while (std::fscanf(f, "%llu %d", &k, &n) == 2)
                {
                    s_times[k] = std::min(n, 4);
                    s_left[k] = now;    // parked again from the start, for as long as its count says
                }
                std::fclose(f);
            }
            // What the other copies learnt too (Skiller, 2026-11-11, from «IA que juega»: «lo que aprende una lo usan
            // todas»): their parked tiles from ..\SacredA*\, counted at most twice (10 min), since a gate shut for one
            // hero may stand open for another further on.
            const std::wstring self = s_file.substr(0, s_file.find_last_of(L"\\/"));
            const std::wstring games = self.substr(0, self.find_last_of(L"\\/") + 1);
            WIN32_FIND_DATAW fd{};
            if (HANDLE h = FindFirstFileW((games + L"SacredA*").c_str(), &fd); h != INVALID_HANDLE_VALUE)
            {
                int shared = 0;
                do
                {
                    const std::wstring dir = games + fd.cFileName;
                    if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) || _wcsicmp(dir.c_str(), self.c_str()) == 0)
                    {
                        continue;
                    }
                    if (FILE* f = _wfopen((dir + L"\\SacredBild-parked2.txt").c_str(), L"rb"))
                    {
                        unsigned long long k = 0;
                        int n = 0;
                        while (std::fscanf(f, "%llu %d", &k, &n) == 2)
                        {
                            if (!s_times.count(k) && n > 0)
                            {
                                s_times[k] = std::min(n, 2);
                                s_left[k] = now;
                                ++shared;
                            }
                        }
                        std::fclose(f);
                    }
                } while (FindNextFileW(h, &fd));
                FindClose(h);
                LOG("AutoAttack: {} parked tiles taken from the other copies", shared);
            }
        }
        // C5: 2 min, then 1 h, 6 h and a day (the old 10/30/60 min let the same cell take an hour over and over).
        // An hour at most from the third on (the code reviewer: a quest's goal in a cell marked three times was barred
        // 6-24 h).
        static const DWORD kLeftMs[] = {120000, 3600000, 3600000, 3600000};
        if (const auto it = s_left.find(key);
            it != s_left.end() && now - it->second < kLeftMs[std::min(s_times[key], 4) - 1])
        {
            return true;
        }
        static int32_t s_movedX = 0, s_movedY = 0;
        static DWORD s_aroundSince = 0;
        if (key != s_key || distance < s_best - kTileSize)
        {
            s_key = key;
            s_best = distance;
            s_since = now;
            s_aroundSince = 0;
            return false;
        }
        cObjectManager* om = cObjectManager::instance();
        if (goingAround(s_movedX, s_movedY, s_aroundSince, om ? om->hero() : nullptr, now))
        {
            s_since = now;
            return false;
        }
        if (now - s_since > 20000 && HeroProfile::current().mounted && !s_offFor.count(key))
        {
            s_offFor.insert(key);
            g_onFootUntil = now + 60000;
            s_since = now;
            return false;
        }
        if (now - s_since > 20000)
        {
            const int times = ++s_times[key];
            LOG("AutoAttack: no nearer to tile {},{} in 20 s ({:.0f} tiles, time {}): left {} min, playing on from here",
                static_cast<int>(wx / kTileSize), static_cast<int>(wy / kTileSize), distance / kTileSize, times,
                kLeftMs[std::min(times, 4) - 1] / 60000);
            s_left[key] = now;
            s_key = 0;
            if (FILE* f = _wfopen(s_file.c_str(), L"wb"))
            {
                for (const auto& [k, n] : s_times)
                {
                    std::fprintf(f, "%llu %d\n", static_cast<unsigned long long>(k), n);
                }
                std::fclose(f);
            }
            return true;
        }
        return false;
    }

    bool talkedLately(uint32_t id, DWORD now)
    {
        const auto it = g_talkedAt.find(id);
        return it != g_talkedAt.end() && now - it->second < kTalkAgainMs;
    }

    void forgetTalks()
    {
        g_talkedAt.clear();
        g_talkFails.clear();    // a quest step done: who would not speak may now
    }

    // The companions kept with the hero on a long walk (the player's wish, 2026-11-09: the agent looks after its
    // mercenary): one fallen over 10 tiles behind is waited for, one over 18 tiles off is walked back to; a wait lasts
    // 20 s at most (a companion stuck behind a wall), then the walk goes on for 30 s before waiting again.
    // True while it waits: the caller's walk is held, not failed.
    bool waitForCompanions(DWORD now, const cCreature* self)
    {
        static DWORD s_waitSince = 0, s_goOnUntil = 0;
        static int s_missedInRow = 0;   // waits in a row it never caught up in
        if (s_goOnUntil && static_cast<int>(now - s_goOnUntil) < 0)
        {
            return false;
        }
        cObjectManager* objects = cObjectManager::instance();
        const cCreature* lag = nullptr;
        double farthest = 0.0;
        for (uint32_t id : g_hirelings)
        {
            const cCreature* h = objects ? objects->creature(id) : nullptr;
            if (!h || h->health <= 0)
            {
                continue;
            }
            const double d = std::hypot(static_cast<double>(h->x - self->x), static_cast<double>(h->y - self->y)) / kTileSize;
            if (d > 10.0 && d < 80.0 && d > farthest)
            {
                farthest = d;
                lag = h;
            }
        }
        if (!lag)
        {
            // Caught up: a while on before waiting again (the live verifier, 2026-11-11: A5 47 waits in 19 min,
            // a fight now and then; a player does not stop every few steps for the hireling).
            if (s_waitSince)
            {
                s_goOnUntil = now + 45000;
                s_missedInRow = 0;
            }
            s_waitSince = 0;
            return false;
        }
        if (!s_waitSince)
        {
            s_waitSince = now;
            LOG("AutoAttack: a companion is {:.0f} tiles behind: waiting for it", farthest);
        }
        if (now - s_waitSince > 8000)
        {
            // Each miss in a row a longer while on, up to 5 min (the stuck solver, 2026-11-24: A8 725 waits, A1 236,
            // against 8-44 in the copies that did most quests; a companion that never keeps up is not waited for).
            s_missedInRow = std::min(s_missedInRow + 1, 5);
            LOG("AutoAttack: the companion did not come up in 8 s ({:.0f} tiles): going on for {} min", farthest,
                s_missedInRow);
            s_waitSince = 0;
            s_goOnUntil = now + 60000u * static_cast<DWORD>(s_missedInRow);
            return false;
        }
        if (farthest > 18.0)
        {
            if (!ClickWalk::routing())
            {
                ClickWalk::walkTo(lag->x, lag->y, false);
            }
        }
        else
        {
            ClickWalk::cancel();
        }
        return true;
    }

    // A shut door ahead on a trip: within 6 tiles, toward the goal (the player, 2026-11-10: «al agente aún le cuesta
    // detectar puertas»; before, doors were only used shut in or stuck).
    struct DoorAhead
    {
        int32_t heroX, heroY, goalX, goalY;
    };

    bool acceptDoorAhead(uint32_t id, void* context)
    {
        if (!acceptDoor(id, nullptr))
        {
            return false;
        }
        const auto* a = static_cast<const DoorAhead*>(context);
        cObjectManager* objects = cObjectManager::instance();
        const cObject* o = objects ? objects->object(id) : nullptr;
        if (!o)
        {
            return false;
        }
        const double dx = o->x - a->heroX, dy = o->y - a->heroY;
        const double gx = a->goalX - a->heroX, gy = a->goalY - a->heroY;
        const double dl = std::hypot(dx, dy), gl = std::hypot(gx, gy);
        return dl > 1.0 && gl > 1.0 && (dx * gx + dy * gy) / (dl * gl) > 0.5 && dl < gl + 2.0 * kTileSize;
    }

    bool doorOnTheWay(DWORD now, const cCreature* self, int32_t x, int32_t y)
    {
        static DWORD s_at = 0;
        if (s_at && now - s_at < 3000)
        {
            return false;
        }
        s_at = now;
        DoorAhead ahead{self->x, self->y, x, y};
        const float range = g_doorRange;
        g_doorRange = 6.0f * kTileSize;
        AimAssist::Target door;
        const bool found = AimAssist::findObject(g_doorRange, &acceptDoorAhead, &ahead, door);
        g_doorRange = range;
        if (!found)
        {
            return false;
        }
        if (!Act::allowed(Act::Kind::Doors, "open a shut door on the way"))
        {
            return false;
        }
        g_doorTried[door.id] = now;
        LOG("AutoAttack: a shut door on the way ({:x}): opened", door.id);
        remember("abre una puerta cerrada en el camino");
        attack(door.id);
        return true;
    }

    // A shut door or gate near the goal, whichever way it lies from the hero (Manolito, block AB, 2026-11-11: the yard
    // at 3049,2711 has its gate DOOR_GATE01_A in the south wall, and the agent walked straight into the east wall; the
    // door on the way looks only ahead). Used when the walk got no nearer: the door within 8 tiles of the goal and 30
    // of the hero.
    struct DoorNearGoal
    {
        int32_t goalX, goalY;
        double tiles;
    };

    bool acceptDoorNearGoal(uint32_t id, void* context)
    {
        if (!acceptDoor(id, nullptr))
        {
            return false;
        }
        const auto* g = static_cast<const DoorNearGoal*>(context);
        cObjectManager* objects = cObjectManager::instance();
        const cObject* o = objects ? objects->object(id) : nullptr;
        return o && std::hypot(static_cast<double>(o->x - g->goalX), static_cast<double>(o->y - g->goalY)) <= g->tiles * kTileSize;
    }

    bool doorNearGoal(DWORD now, int32_t x, int32_t y)
    {
        // Within 8 tiles of the goal first; then 30, a castle's gate far from the one inside (the quests' session,
        // 2026-11-16, docs/Misiones-tope-40.md: Baron DeMordrey at 1676,2352, the castle's way in 29 tiles off).
        DoorNearGoal goal{x, y, 8.0};
        const float range = g_doorRange;
        g_doorRange = 30.0f * kTileSize;
        AimAssist::Target door;
        bool found = AimAssist::findObject(g_doorRange, &acceptDoorNearGoal, &goal, door);
        if (!found)
        {
            goal.tiles = 30.0;
            found = AimAssist::findObject(g_doorRange, &acceptDoorNearGoal, &goal, door);
        }
        g_doorRange = range;
        if (!found)
        {
            return false;
        }
        if (!Act::allowed(Act::Kind::Doors, "use the shut door near the goal"))
        {
            return false;
        }
        // From the outside, on the side away from the goal (Manolito, block BV, 2026-11-17: A4 stood at 1949,3263, behind the
        // house whose only way in is the gate ed1 at 1950,3270, on its south side, the item at 1948,3266 inside; the click
        // on a gate sends the hero to its front or back use point and from the north it had none to reach): 3 tiles
        // beyond the door along the line from the goal through it, walked to before the click, for 40 s at most.
        {
            cObjectManager* om = cObjectManager::instance();
            const cCreature* hero = om ? om->hero() : nullptr;
            const cObject* d = om ? om->object(door.id) : nullptr;
            static uint32_t s_approachId = 0;
            static DWORD s_approachSince = 0;
            if (hero && d && !*(reinterpret_cast<const uint8_t*>(hero) + 0x24))
            {
                const double gx = static_cast<double>(d->x - x), gy = static_cast<double>(d->y - y);
                const double gl = std::hypot(gx, gy);
                if (gl > 1.0 * kTileSize)
                {
                    const int32_t px = static_cast<int32_t>(d->x + gx / gl * 3.0 * kTileSize);
                    const int32_t py = static_cast<int32_t>(d->y + gy / gl * 3.0 * kTileSize);
                    if (s_approachId != door.id)
                    {
                        s_approachId = door.id;
                        s_approachSince = now;
                    }
                    const double toP = std::hypot(static_cast<double>(px - hero->x), static_cast<double>(py - hero->y));
                    if (toP > 3.5 * kTileSize && now - s_approachSince < 40000)
                    {
                        static DWORD s_toldAt = 0;
                        if (now - s_toldAt > 20000)
                        {
                            s_toldAt = now;
                            LOG("AutoAttack: the shut door {:x} near tile {},{}: to its outside at {},{} first ({:.0f} tiles)", door.id,
                                static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize), static_cast<int>(px / kTileSize),
                                static_cast<int>(py / kTileSize), toP / kTileSize);
                        }
                        ClickWalk::walkTo(px, py, false);
                        g_doorHoldUntil = now + 3000;
                        return true;
                    }
                }
            }
        }
        g_doorTried[door.id] = now;
        g_doorHoldUntil = now + 1500;
        LOG("AutoAttack: no nearer to tile {},{}: the shut door {:x} near it used", static_cast<int>(x / kTileSize),
            static_cast<int>(y / kTileSize), door.id);
        remember("usa la puerta cerca del destino");
        attack(door.id);
        return true;
    }

    // A goal no walk gets nearer to and no shut door beside it: a way into another layer near it (stairs, a house's
    // door, a cave: what MapMemory marked where the hero once changed layer, or a house's landing from the world
    // files) walked onto, each tried once in 3 min. The solver, 2026-11-12: A3 and A8 «no way found (8 tiles)» to a
    // goal inside a house at 3174,2794; A8 had been inside (layer 1) through the marks at 3171,2796..2797.
    bool entranceNearGoal(DWORD now, const cCreature* self, int32_t x, int32_t y)
    {
        static std::unordered_map<uint64_t, DWORD> s_tried;
        const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
        const int gx = static_cast<int>(x / kTileSize), gy = static_cast<int>(y / kTileSize);
        const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
        // Only from near the goal (the stuck solver, 2026-11-13: fired 50 tiles off and on horseback, A1).
        // From the surface up to 40 (the quests' session, 2026-11-16: the baron's castle, its way in 29 tiles from him).
        if (std::hypot(gx - htx, gy - hty) > (layer == 0 ? 40.0 : 25.0))
        {
            return false;
        }
        // Inside already (a layer other than the surface) with the goal at hand: the way in under the hero's feet is
        // the way out, and «a step off to step on again» put him back in the street (A1, 16:16:56).
        if (layer != 0 && std::hypot(gx - htx, gy - hty) <= 20.0)
        {
            return false;
        }
        std::vector<std::pair<int, int>> ways = MapMemory::waysOut(layer, gx, gy, 10, true);
        // None within 10 tiles from the surface: a building's way in may be far from what is inside (docs/Misiones-
        // tope-40.md, fix A.1: 35 tiles).
        const int reach = layer == 0 && ways.empty() ? 35 : 10;
        if (reach > 10)
        {
            ways = MapMemory::waysOut(layer, gx, gy, reach, true);
        }
        for (const Teleports::Interior& in : Teleports::interiors())
        {
            if (!in.start && layer == 0 && std::abs(in.outX - gx) <= reach && std::abs(in.outY - gy) <= reach)
            {
                // A cave's way in is the script's zone beside the landing (Manolito, block BE: cave 2.3, landing
                // 3042,2892, zone 3047,2892), the one the agent goes for.
                if (int cx = 0, cy = 0; Teleports::caveTriggerNear(in.outX, in.outY, 8, cx, cy))
                {
                    ways.emplace_back(cx, cy);
                    continue;
                }
                ways.emplace_back(in.outX, in.outY);
            }
        }
        int bx = 0, by = 0;
        double best = 1e18;
        for (const auto& [ex, ey] : ways)
        {
            const uint64_t k = (static_cast<uint64_t>(static_cast<uint32_t>(ex)) << 32) | static_cast<uint32_t>(ey);
            if (const auto t = s_tried.find(k); t != s_tried.end() && now - t->second < 180000)
            {
                continue;
            }
            const double d = std::hypot(ex - gx, ey - gy);
            if (d < best)
            {
                best = d;
                bx = ex;
                by = ey;
            }
        }
        if (best > 1e17)
        {
            return false;
        }
        s_tried[(static_cast<uint64_t>(static_cast<uint32_t>(bx)) << 32) | static_cast<uint32_t>(by)] = now;
        // Into a house on foot, as a player gets off at its door (A5 2026-11-12 01:20: on horseback by the way in at
        // 3095,2784, 3-tile walks every 4 s that never moved it, until the 90 s rule).
        const cObjectManager* om = cObjectManager::instance();
        if (const cCreature* hero = om ? const_cast<cObjectManager*>(om)->hero() : nullptr;
            hero && *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x1EC))
        {
            g_onFootUntil = now + 60000;
        }
        // The landing the game names for a cave (tprausz) lies beside its mouth, not on it (A1, 2026-11-16: the mouth of
        // cave 2.3, landing 3042,2892, the goal 3046,2892 four tiles on along a one-tile corridor; the hero reached
        // the landing, sat out the 20 s hold with no order and the position watch left the goal 3 min). On the landing
        // with the goal within 6 tiles: on to the goal itself, the hold short.
        if (std::hypot(bx - htx, by - hty) <= 1.5 && best <= 6.0 && std::hypot(gx - htx, gy - hty) > 1.5)
        {
            LOG("AutoAttack: no nearer to tile {},{}: on the landing at {},{}: on to the goal ({:.0f} tiles)", gx, gy, bx, by,
                std::hypot(gx - htx, gy - hty));
            ClickWalk::walkTo(static_cast<int32_t>((gx + 0.5) * kTileSize), static_cast<int32_t>((gy + 0.5) * kTileSize), false);
            g_doorHoldUntil = now + 3000;
            g_entranceHoldUntil = now + 3000;
            return true;
        }
        if (std::hypot(bx - htx, by - hty) <= 1.5)
        {
            // On it already: a step off, the next try walks back onto it (a way in fires on stepping on).
            const double a = now * 0.001;
            ClickWalk::walkTo(static_cast<int32_t>(self->x + std::cos(a) * 3 * kTileSize),
                              static_cast<int32_t>(self->y + std::sin(a) * 3 * kTileSize), false);
            s_tried.erase((static_cast<uint64_t>(static_cast<uint32_t>(bx)) << 32) | static_cast<uint32_t>(by));
            LOG("AutoAttack: no nearer to tile {},{}: on the way in at {},{}: a step off to step on again", gx, gy, bx, by);
            return true;
        }
        LOG("AutoAttack: no nearer to tile {},{}: to the way in at {},{} ({:.0f} tiles from the goal)", gx, gy, bx, by, best);
        Findings::note("door", self->x, self->y, "goal {},{}: to the way in at {},{}", gx, gy, bx, by);
        remember("usa la entrada cerca del destino");
        ClickWalk::walkTo(static_cast<int32_t>((bx + 0.5) * kTileSize), static_cast<int32_t>((by + 0.5) * kTileSize), false);
        // The order held 20 s: the roam's travel to the goal took it over within 10 s and the hero never reached the
        // way in (the solver's fix L, 2026-11-12: A2, A3, A4).
        g_doorHoldUntil = now + 20000;
        g_entranceHoldUntil = now + 20000;
        return true;
    }

    // The ways out of where the hero is shut in: those MapMemory saw it jump through, plus the game's own (a tpstart
    // tile at hand, the stairs anchors beside an interior's landing inside, a house's door in the yard).
    // The game's own first (`gameCount` of them): MapMemory's can be wrong (a save loaded looked like a jump, A5
    // 2026-11-12, two «portals» inside a cave tried for 10 min while the stairs anchor sat by its landing).
    std::vector<std::pair<int, int>> waysOutAround(int layer, int htx, int hty, size_t* gameCount = nullptr)
    {
        std::vector<std::pair<int, int>> ways;
        // The game's own: a tpstart tile at hand, or the stairs anchors beside an interior's landing inside (its
        // way out is there; Manolito, block L).
        for (const Teleports::Interior& in : Teleports::interiors())
        {
            if (in.start && std::abs(in.outX - htx) <= Whereabouts::kRadius && std::abs(in.outY - hty) <= Whereabouts::kRadius)
            {
                ways.emplace_back(in.outX, in.outY);
            }
            else if (!in.start && std::abs(in.inX - htx) <= Whereabouts::kRadius && std::abs(in.inY - hty) <= Whereabouts::kRadius)
            {
                // A cave's way out is the script's zone beside the landing (Manolito, block BE: A5 stood on the
                // landing 5368,338 of cave 5.2 with no jump; the zone is 5372,338), first.
                if (int cx = 0, cy = 0; Teleports::caveTriggerNear(in.inX, in.inY, 8, cx, cy))
                {
                    ways.emplace_back(cx, cy);
                }
                for (const auto& a : Teleports::anchorsNear(layer, in.inX, in.inY, 6))
                {
                    ways.push_back(a);
                }
            }
            else if (!in.start && layer == 0 && std::abs(in.outX - htx) <= Whereabouts::kRadius &&
                     std::abs(in.outY - hty) <= Whereabouts::kRadius)
            {
                // A house's door in the yard (HQ_HE_3_3_1's tprausz tiles, Manolito): the landing itself and the
                // stairs anchors beside it; a cave's way in (the script's zone beside the landing, block BE) first.
                if (int cx = 0, cy = 0; Teleports::caveTriggerNear(in.outX, in.outY, 8, cx, cy))
                {
                    ways.emplace_back(cx, cy);
                }
                ways.emplace_back(in.outX, in.outY);
                for (const auto& a : Teleports::anchorsNear(layer, in.outX, in.outY, 6))
                {
                    ways.push_back(a);
                }
            }
        }
        if (gameCount)
        {
            *gameCount = ways.size();
        }
        for (const auto& w : MapMemory::waysOut(layer, htx, hty, Whereabouts::kRadius))
        {
            if (std::find(ways.begin(), ways.end(), w) == ways.end())
            {
                ways.push_back(w);
            }
        }
        return ways;
    }

    // Where to order a walk to step into a way out's tile (ex, ey) from the hero's (htx, hty): within 3 tiles, 1.5 tiles
    // past its centre, away from the hero; else its centre. A walk ordered onto the tile itself stood 1.3 tiles short and
    // never stepped in (Manolito's live samples, A4 2026-11-24: y 1423.8 for the cave 16.1's exit 5741,1422; the game's
    // own walk, our hook passes short ones unchanged); ordered past it, the hero went through and the trigger jumped.
    void aimThrough(int htx, int hty, int ex, int ey, int32_t& wx, int32_t& wy)
    {
        double tx = ex + 0.5, ty = ey + 0.5;
        if (std::abs(ex - htx) <= 3 && std::abs(ey - hty) <= 3)
        {
            tx += 1.5 * ((ex > htx) - (ex < htx));
            ty += 1.5 * ((ey > hty) - (ey < hty));
        }
        wx = static_cast<int32_t>(tx * kTileSize);
        wy = static_cast<int32_t>(ty * kTileSize);
    }

    // The tile 3 beyond a way out, toward the other end of the same door on layer 0 (the stuck solver, 2026-11-17, A4: shut in
    // 8 min in a merchant's house, layer 1, standing again and again on the doorway 3198,2799 whose outside end
    // 3199,2799 MapMemory had marked on layer 0; the layer flips only one step on, and the guard took «on the way out»
    // for done, stepped off in a circle's random direction and went on to other houses' doors). False for layer 0 or no
    // other end marked within 2 tiles.
    bool beyondWay(int layer, int ex, int ey, int& bx, int& by)
    {
        if (layer < 1)
        {
            return false;
        }
        int bestD = 1 << 30;
        for (const auto& [ox, oy] : MapMemory::waysOut(0, ex, ey, 2))
        {
            const int d = std::max(std::abs(ox - ex), std::abs(oy - ey));
            if (d >= 1 && d < bestD)
            {
                bestD = d;
                bx = ex + 3 * ((ox > ex) - (ox < ex));
                by = ey + 3 * ((oy > ey) - (oy < ey));
            }
        }
        return bestD < (1 << 30);
    }

    // Shut in with a goal outside (a farming zone, a shop, the quest): the way out first, the game's own ahead, each
    // tried once in 2 min (A5 2026-11-12: farming sent it 3199 tiles off from inside a cave, between the quest's
    // tries of its way out, so it never got there).
    bool towardWayOut(DWORD now, const cCreature* self, int32_t x, int32_t y)
    {
        const int gtx = static_cast<int>(x / kTileSize), gty = static_cast<int>(y / kTileSize);
        if (!Whereabouts::area().shutIn || Whereabouts::reachable(gtx, gty) == 1)
        {
            return false;
        }
        // At the pocket's edge (within 4 tiles of its reachable ground, as the shut-in check for the quest's goal takes
        // it): a house's shut door is no reachable ground, and its tile counted as outside (Estudio-atascos row 3: quest
        // 1405's goal 5851,3113 indoors, «in by the door at 5855,3122» then «shut in, the goal at 5855,3122 outside: to
        // the way out … first», A4 2 h 20 min between them). The walk and the door handling take it from here.
        if (int nx = 0, ny = 0; Whereabouts::nearestReachable(gtx, gty, nx, ny) &&
                                std::max(std::abs(nx - gtx), std::abs(ny - gty)) <= 4)
        {
            return false;
        }
        static std::unordered_map<uint64_t, DWORD> s_tried;
        static DWORD s_askAt = 0;
        static uint64_t s_told = 0;
        const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
        const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
        size_t gameWays = 0, wi = 0;
        for (const auto& [ex, ey] : waysOutAround(layer, htx, hty, &gameWays))
        {
            const bool gameWay = wi++ < gameWays;
            const uint64_t wk = (static_cast<uint64_t>(static_cast<uint32_t>(ex)) << 32) | static_cast<uint32_t>(ey);
            if (const auto t = s_tried.find(wk); t != s_tried.end() && now - t->second < 120000)
            {
                continue;
            }
            if (std::abs(ex - htx) <= 1 && std::abs(ey - hty) <= 1)
            {
                // On it: through, three tiles beyond toward the door's other end (up to 3 tries), not on to the next way.
                static std::unordered_map<uint64_t, int> s_through;
                int tx = 0, ty = 0;
                if (s_through[wk] < 3 && beyondWay(layer, ex, ey, tx, ty))
                {
                    if (now - s_askAt > 2500)
                    {
                        s_askAt = now;
                        ++s_through[wk];
                        LOG("AutoAttack: on the way out at {},{}: through it, to {},{} (try {})", ex, ey, tx, ty, s_through[wk]);
                        ClickWalk::walkTo(static_cast<int32_t>((tx + 0.5) * kTileSize), static_cast<int32_t>((ty + 0.5) * kTileSize),
                                          false);
                    }
                    return true;
                }
                s_through.erase(wk);
                s_tried[wk] = now;
                continue;
            }
            const int32_t wx = static_cast<int32_t>((ex + 0.5) * kTileSize);
            const int32_t wy = static_cast<int32_t>((ey + 0.5) * kTileSize);
            if (!gameWay &&
                approachStalled(wx, wy, std::hypot(static_cast<double>(wx - self->x), static_cast<double>(wy - self->y)), now))
            {
                s_tried[wk] = now;
                continue;
            }
            if (wk != s_told)
            {
                s_told = wk;
                LOG("AutoAttack: shut in, the goal at {},{} outside: to the way out at {},{} first",
                    static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize), ex, ey);
            }
            if (!ClickWalk::routing() && now - s_askAt > 4000)
            {
                s_askAt = now;
                int32_t ax = 0, ay = 0;
                aimThrough(static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize), ex, ey, ax, ay);
                ClickWalk::walkTo(ax, ay, false);
            }
            return true;
        }
        return false;
    }

    bool travelTo(DWORD now, const cCreature* self, int32_t x, int32_t y, DWORD& askAt)
    {
        if (doorOnTheWay(now, self, x, y))
        {
            g_travel.lastAt = now;
            return true;
        }
        if (waitForCompanions(now, self))
        {
            g_travel.lastAt = now;
            g_travel.bestAt = now;      // the wait is no lack of progress
            return true;
        }
        // The far route is being planned (up to two minutes): no «no nearer», no goal given up meanwhile (the stuck
        // solver, 2026-11-16: A1's goals 1785,3050 and 1676,2352 started 28 times and given up 30 times, A3's and A4's
        // alike).
        if (ClickWalk::planning())
        {
            g_travel.lastAt = now;
            g_travel.bestAt = now;
            return true;
        }
        if (towardWayOut(now, self, x, y))
        {
            g_travel.lastAt = now;
            g_travel.bestAt = now;      // going out first is no lack of progress
            return true;
        }
        const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(x / kTileSize)) << 32) |
                             static_cast<uint32_t>(y / kTileSize);
        if (const auto it = g_travelBlocked.find(key); it != g_travelBlocked.end())
        {
            if (static_cast<int>(now - it->second) < 0)
            {
                return false;
            }
            g_travelBlocked.erase(it);
        }
        const double d = std::hypot(static_cast<double>(x - self->x), static_cast<double>(y - self->y));
        Travel& t = g_travel;
        // A new goal, or back from a fight or a collect (the time away is no lack of progress).
        if (std::abs(x - t.x) > 3 * kTileSize || std::abs(y - t.y) > 3 * kTileSize)
        {
            t = Travel{x, y, d, now, now, 0, 0, self->x, self->y};
        }
        if (now - t.lastAt > 2000)
        {
            t.bestAt = now;
        }
        t.lastAt = now;
        if (d < t.best - 2.0 * kTileSize)
        {
            t.best = d;
            t.bestAt = now;
            t.fails = 0;
            t.aroundSince = 0;
        }
        else if (goingAround(t.movedX, t.movedY, t.aroundSince, self, now))
        {
            t.bestAt = now;
        }
        // On the route net's trip, progress is the walk left, not the straight line (the stuck solver, 2026-11-16, A6 at
        // 3141,2655 by the river: the trip 1276-1324 tiles for 385-478 as the crow flies, the hero first away from the goal;
        // three «no nearer in 20 s» and «no way found … left 3 min» for the portal and for the quest at 3242,2864; and
        // goingAround gives a detour 2 min at most). A new trip worked out again, longer, starts the count again.
        const float left = RouteNet::tilesLeft(*(reinterpret_cast<const uint8_t*>(self) + 0x24), static_cast<int>(self->x / kTileSize),
                                               static_cast<int>(self->y / kTileSize), static_cast<int>(x / kTileSize),
                                               static_cast<int>(y / kTileSize));
        if (left < 0.0f)
        {
            t.bestLeft = -1.0f;
        }
        else if (t.bestLeft < 0.0f || left > t.bestLeft + 40.0f)
        {
            t.bestLeft = left;
        }
        else if (left < t.bestLeft - 2.0f)
        {
            t.bestLeft = left;
            t.bestAt = now;
            t.fails = 0;
            t.aroundSince = 0;
        }
        if (t.detourUntil && static_cast<int>(now - t.detourUntil) < 0)
        {
            return true;
        }
        t.detourUntil = 0;
        if (now - t.bestAt > 20000 && HeroProfile::current().mounted &&
            !(g_onFootUntil && static_cast<int>(now - (g_onFootUntil - 60000)) < 300000))
        {
            g_onFootUntil = now + 60000;    // on foot before a step aside (once in 5 min)
            t.bestAt = now;
            return true;
        }
        if (now - t.bestAt > 20000)
        {
            ClickWalk::cancel();
            if (doorNearGoal(now, x, y))
            {
                t.detourUntil = now + 8000;
                t.bestAt = now;
                return true;
            }
            if (entranceNearGoal(now, self, x, y))
            {
                t.detourUntil = now + 10000;
                t.bestAt = now;
                return true;
            }
            if (++t.fails >= 3)
            {
                // Each time again no way, left longer (the player, 2026-11-11: the Daemon «no está teniendo mucha
                // eficiencia», 40 s lost every 3 min on a quest goal with no way to it): 3, 15, 45 min, then 2 h.
                static std::unordered_map<uint64_t, int> s_noWay;
                static const DWORD kNoWayMs[] = {180000, 900000, 2700000, 7200000};
                const int times = std::min(++s_noWay[key], 4);
                LOG("AutoAttack: no way found to tile {},{} ({:.0f} tiles, time {}): left {} min", static_cast<int>(x / kTileSize),
                    static_cast<int>(y / kTileSize), d / kTileSize, times, kNoWayMs[times - 1] / 60000);
                g_travelBlocked[key] = now + kNoWayMs[times - 1];
                t = Travel{};
                return false;
            }
            const double angle = (std::rand() % 360) * 3.14159265358979 / 180.0;
            const int32_t sx = self->x + static_cast<int32_t>(std::cos(angle) * 8.0 * kTileSize);
            const int32_t sy = self->y + static_cast<int32_t>(std::sin(angle) * 8.0 * kTileSize);
            LOG("AutoAttack: no nearer to tile {},{} in 20 s (try {}): a step aside first", static_cast<int>(x / kTileSize),
                static_cast<int>(y / kTileSize), t.fails);
            ClickWalk::walkTo(sx, sy, false);
            t.detourUntil = now + 6000;
            t.bestAt = now;
            return true;
        }
        if (!ClickWalk::routing() && now - askAt > 4000)
        {
            askAt = now;
            ClickWalk::walkTo(x, y, false);
        }
        return true;
    }

    // The game's portals on the way (Portals; the player, 2026-11-16: «todo lo que un jugador puede hacer está
    // permitido, portales incluidos»; the agents walked 400+ tiles to quest 44). Before a long walk on the surface the
    // agent weighs walking against walking to a joined portal, picking a joined one near the goal in its box and
    // walking on from there, and takes the shorter. A portal not joined yet within 30 tiles is stepped onto on the way
    // (its box opens and joins it; the watcher closes it). The pick in the box is a click on its row, by the watcher's
    // thread (the box holds the game in its modal loop). Never a position written.
    struct PortalTrip
    {
        uint64_t goal = ~0ull;      // the goal (in 4-tile squares) the choice was made for
        DWORD since = 0;            // armed at
        DWORD onTileSince = 0;      // on the portal's tile since (0: not)
        DWORD farAt = 0;            // the hero last more than 60 tiles from the portal (the 10 min count from there)
        DWORD offWaySince = 0;      // a portal to join out of the way of the goals travelled to since (0: on the way)
    };
    PortalTrip g_portalTrip;
    std::unordered_map<int, DWORD> g_portalLeftUntil;   // portal id -> not used again before this tick
    // Times each portal was gone out of the way for to join it, this game: two at most (the coordinator, 2026-11-16:
    // a try that failed is left 30 min, then may be made once more).
    uint8_t g_portalJoinTries[Portals::kCount] = {};

    uint32_t portalsTriedOut()
    {
        uint32_t mask = 0;
        for (int id = 0; id < Portals::kCount; ++id)
        {
            if (g_portalJoinTries[id] >= 2)
            {
                mask |= 1u << id;
            }
        }
        return mask;
    }
    uintptr_t g_portalJoinHero = 0;     // ... for this hero object (another: a game loaded, all may be tried again)

    uint32_t portalsLeft(DWORD now)
    {
        uint32_t skip = 0;
        for (const auto& [id, until] : g_portalLeftUntil)
        {
            if (static_cast<int>(now - until) < 0)
            {
                skip |= 1u << id;
            }
        }
        return skip;
    }

    void portalGiveUp(DWORD now, const char* why)
    {
        const int from = Portals::armedFrom(), to = Portals::armedTo();
        if (from < 0)
        {
            return;
        }
        LOG("AutoAttack: portal {}{}: {}; portal {} left 30 min, on foot", from, to >= 0 ? std::format(" -> {}", to) : "",
            why, from);
        g_portalLeftUntil[from] = now + 1800000;
        Portals::disarm();
        g_portalTrip.onTileSince = 0;
    }

    int32_t tileMiddle(int t)
    {
        return static_cast<int32_t>((t + 0.5) * kTileSize);
    }

    // A walk's length on the surface by the route net, else over what the map knows: -1 while worked out, -2 none.
    float walkTilesBetween(int ax, int ay, int bx, int by)
    {
        const float net = RouteNet::walkTiles(ax, ay, bx, by);
        return net == -2.0f ? MapMemory::routeTiles(0, ax, ay, bx, by) : net;
    }

    // The tile to walk to instead of the goal while a portal is on the way: true with it in (px, py) (world).
    bool portalLeg(DWORD now, const cCreature* self, int32_t x, int32_t y, int32_t& px, int32_t& py)
    {
        const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
        const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
        const int gtx = static_cast<int>(x / kTileSize), gty = static_cast<int>(y / kTileSize);
        const uint64_t goal = (static_cast<uint64_t>(static_cast<uint32_t>(gtx / 4)) << 32) | static_cast<uint32_t>(gty / 4);
        int ftx = 0, fty = 0;
        if (const int from = Portals::armedFrom(); from >= 0)
        {
            const int to = Portals::armedTo();
            Portals::tile(from, ftx, fty);
            if (to >= 0)
            {
                int ttx, tty;
                Portals::tile(to, ttx, tty);
                if (layer == 0 && std::hypot(htx - ttx, hty - tty) < 30.0)
                {
                    LOG("AutoAttack: portal {} -> {}: arrived at {},{} ({:.0f} s), {:.0f} tiles on to the goal {},{}", from,
                        to, htx, hty, (now - g_portalTrip.since) / 1000.0, std::hypot(htx - gtx, hty - gty), gtx, gty);
                    remember("viaja por un portal");
                    ClickWalk::cancel();
                    Portals::disarm();
                    g_portalTrip.onTileSince = 0;
                    return false;
                }
                if (goal != g_portalTrip.goal)
                {
                    LOG("AutoAttack: portal {} -> {}: dropped, the goal is now {},{}", from, to, gtx, gty);
                    Portals::disarm();
                    g_portalTrip.onTileSince = 0;
                }
            }
            else if (Portals::joined() & (1u << from))
            {
                LOG("AutoAttack: portal {} joined at {},{} (the hero's portals {:x})", from, htx, hty, Portals::joined());
                remember("activa un portal");
                Portals::disarm();
                g_portalTrip.onTileSince = 0;
                g_portalTrip.goal = ~0ull;  // the goal weighed again with this portal
            }
            else if (const double more = std::hypot(htx - ftx, hty - fty) + std::hypot(ftx - gtx, fty - gty) -
                                         std::hypot(htx - gtx, hty - gty);
                     more <= 90.0)
            {
                g_portalTrip.offWaySince = 0;
            }
            else if (!g_portalTrip.offWaySince)
            {
                g_portalTrip.offWaySince = now;     // another errand's goal for a moment (A3: two goals in turn each look)
            }
            else if (now - g_portalTrip.offWaySince > 15000)
            {
                // The goal changed for good and the portal is no longer on the way: left for another time (tried again).
                LOG("AutoAttack: portal {}: not joined, {:.0f} tiles out of the way to the goal now at {},{}", from, more,
                    gtx, gty);
                if (g_portalJoinTries[from])
                {
                    --g_portalJoinTries[from];
                }
                g_portalLeftUntil[from] = now + 300000;     // not straight back to it (5 min; no try counted)
                Portals::disarm();
                g_portalTrip.onTileSince = 0;
            }
            if (Portals::armedFrom() >= 0)
            {
                const DWORD clicked = Portals::clickedAt();
                if (std::hypot(htx - ftx, hty - fty) > 60.0)
                {
                    g_portalTrip.farAt = now;
                }
                if (now - std::max(g_portalTrip.since, g_portalTrip.farAt) > 600000)
                {
                    portalGiveUp(now, "not there in 10 min");
                    return false;
                }
                if (clicked && now - clicked > 20000)
                {
                    portalGiveUp(now, "its row clicked 20 s ago and the hero not at the other portal");
                    return false;
                }
                // The portal is a script zone of one tile that fires on stepping onto it (Manolito, block BM): a hero
                // already on it (it arrived there by the portal, or a save) steps 4 tiles off after 6 s and back.
                if (!g_portalTrip.onTileSince && layer == 0 && std::hypot(htx - ftx, hty - fty) <= 2.0)
                {
                    g_portalTrip.onTileSince = now;
                    LOG("AutoAttack: portal {}: on its tile {},{} (the hero at {},{}), waiting for its box", from, ftx, fty,
                        htx, hty);
                }
                const DWORD waited = g_portalTrip.onTileSince ? now - g_portalTrip.onTileSince : 0;
                if (!clicked && waited > 30000)
                {
                    portalGiveUp(now, "no box in 30 s at its tile (stepped off and on once)");
                    return false;
                }
                const bool stepOff = !clicked && waited > 6000 && waited < 12000;
                static DWORD s_stepToldFor = 0;
                if (stepOff && s_stepToldFor != g_portalTrip.onTileSince)
                {
                    s_stepToldFor = g_portalTrip.onTileSince;
                    LOG("AutoAttack: portal {}: no box yet: stepping off its tile and back", from);
                }
                px = tileMiddle(ftx + (stepOff ? 4 : 0));
                py = tileMiddle(fty);
                return true;
            }
        }
        if (layer != 0 || !Act::may(Act::Kind::Portals) || !Act::may(Act::Kind::Windows))
        {
            return false;
        }
        const uint32_t skip = portalsLeft(now);
        // A portal not joined yet on the way, gone out of the way for as a player does (the coordinator, 2026-11-16):
        // twice at most per portal and game (the second after the first failed and its 30 min), at most 60 tiles more than the way to the goal, never with a quest's time running
        // nor in a fight (an enemy taken or a blow in the last 10 s).
        if (const uintptr_t hero = Teleports::hero(); hero != g_portalJoinHero)
        {
            g_portalJoinHero = hero;
            std::fill(std::begin(g_portalJoinTries), std::end(g_portalJoinTries), uint8_t{0});
        }
        const bool timed = std::any_of(g_questBook.begin(), g_questBook.end(),
                                       [](const QuestGoal& g) { return g.minutesLeft > 0; });
        const bool fighting = (g_lastTargetAt && now - g_lastTargetAt < 10000) || (g_lastHurtAt && now - g_lastHurtAt < 10000);
        double extra = 0.0;
        if (const int joinId = timed || fighting ? -1
                                                 : Portals::unjoinedOnTheWay(htx, hty, gtx, gty, 60.0,
                                                                             skip | portalsTriedOut(), extra);
            joinId >= 0)
        {
            Portals::tile(joinId, ftx, fty);
            // Only with a walk there (A7, 2026-11-16: in a cave whose floor lies at 4890,4315 on layer 0, portal 6 looked
            // «6 tiles out of the way» as the crow flies; armed, dropped on the way out, armed again at each way in).
            if (walkTilesBetween(htx, hty, ftx, fty) >= 0.0f &&
                Act::allowed(Act::Kind::Portals, "go out of the way to a portal to join it"))
            {
                ++g_portalJoinTries[joinId];
                LOG("AutoAttack: portal {} at {},{} ({:.0f} tiles, {:.0f} more on the way to {},{}) not joined yet (the "
                    "hero's portals {:x}): stepping onto it (try {} of 2)",
                    joinId, ftx, fty, std::hypot(htx - ftx, hty - fty), extra, gtx, gty, Portals::joined(),
                    g_portalJoinTries[joinId]);
                g_portalTrip.since = now;
                g_portalTrip.onTileSince = 0;
                g_portalTrip.farAt = 0;
                g_portalTrip.offWaySince = 0;
                Portals::arm(joinId, -1);
                px = tileMiddle(ftx);
                py = tileMiddle(fty);
                return true;
            }
        }
        if (goal == g_portalTrip.goal)
        {
            return false;   // decided for this goal already: on foot
        }
        // Not from a shut-in place (a cave, a yard: layer 0 holds the caves too, far off the surface's ground).
        if (Whereabouts::area().shutIn)
        {
            return false;
        }
        // The walk itself by the route net (round mountains and rivers it is longer than the straight line); the
        // straight line without the net. Asked again while it is worked out.
        if (std::hypot(gtx - htx, gty - hty) < Portals::kMinWalkTiles)
        {
            return false;
        }
        const float walkNet = RouteNet::walkTiles(htx, hty, gtx, gty);
        if (walkNet == -1.0f)
        {
            return false;
        }
        Portals::Plan plan;
        const bool through = Portals::plan(htx, hty, gtx, gty, skip, walkNet > 0.0f ? walkNet : 0.0, plan);
        if (!through)
        {
            g_portalTrip.goal = goal;
            LOG("AutoAttack: to {},{}: on foot, {:.0f} tiles (through portals {:.0f}{}; the hero's portals {:x})", gtx, gty,
                plan.walk, plan.through, plan.from >= 0 ? std::format(", {} -> {}", plan.from, plan.to) : "",
                Portals::joined());
            return false;
        }
        // Both walks by the route net, else over what the map knows (a goal inside a cave, or across the sea, has
        // neither): their lengths for the as-the-crow-flies ones, worked out on their threads (on foot meanwhile;
        // asked again).
        int ttx, tty;
        Portals::tile(plan.from, ftx, fty);
        Portals::tile(plan.to, ttx, tty);
        const auto leg = &walkTilesBetween;
        const float toPortal = leg(htx, hty, ftx, fty);
        if (toPortal == -1.0f)
        {
            return false;
        }
        const float fromPortal = leg(ttx, tty, gtx, gty);
        if (toPortal == -1.0f || fromPortal == -1.0f)
        {
            return false;
        }
        g_portalTrip.goal = goal;
        const double routed = (toPortal >= 0.0f ? toPortal : 0.0) + Portals::kBoxTiles + (fromPortal >= 0.0f ? fromPortal : 0.0);
        if (toPortal < 0.0f || fromPortal < 0.0f || routed > plan.walk * Portals::kShare ||
            plan.walk - routed < Portals::kMinSavedTiles)
        {
            LOG("AutoAttack: to {},{}: on foot, {:.0f} tiles: portals {} -> {} routed {} + {} tiles", gtx, gty, plan.walk,
                plan.from, plan.to, toPortal < 0.0f ? std::string("none") : std::format("{:.0f}", toPortal),
                fromPortal < 0.0f ? std::string("none") : std::format("{:.0f}", fromPortal));
            return false;
        }
        plan.through = routed;
        if (!Act::allowed(Act::Kind::Portals, "take a portal: shorter than the walk"))
        {
            g_portalTrip.goal = ~0ull;  // asked again on the next look (Suggest)
            return false;
        }
        LOG("AutoAttack: to {},{}: through portals {} ({},{}) -> {}, {:.0f} tiles ({:.0f} + {:.0f} walked) instead of {:.0f} on "
            "foot{} ({} hirelings)", gtx, gty, plan.from, ftx, fty, plan.to, plan.through, toPortal, fromPortal, plan.walk,
            walkNet > 0.0f ? " by the net" : " as the crow flies", g_hirelings.size());
        g_portalTrip.since = now;
        g_portalTrip.onTileSince = 0;
        g_portalTrip.farAt = 0;
        Portals::arm(plan.from, plan.to);
        px = tileMiddle(ftx);
        py = tileMiddle(fty);
        return true;
    }

    bool travel(DWORD now, const cCreature* self, int32_t x, int32_t y, DWORD& askAt)
    {
        int32_t px, py;
        if (portalLeg(now, self, x, y, px, py))
        {
            if (travelTo(now, self, px, py, askAt))
            {
                return true;
            }
            portalGiveUp(now, "no way to it");
        }
        return travelTo(now, self, x, y, askAt);
    }

    // The stuck guard (the player's wish, 2026-11-09: no stall ever): out of the fights, a hero that has not got
    // 8 tiles away from where it stood for 60 s is stuck, whatever the reason (a talk waited out, a goal unreachable,
    // a yard with no way on). Step by step, 30 s apart: first all «left for now» marks are forgotten (who was spoken
    // to, goals travel gave up on), then a walk of 15 tiles each time a new way round (the tile reachable nearest it).
    // Fights and collects (no roam for 3 s) and any jump (a portal, a teleport) start the watch again.
    bool stuckGuard(DWORD now, const cCreature* self)
    {
        // Where the hero stood every 2 s: stuck while all of the last 60 s (or more) fit in a box of 16 tiles. Seen
        // live (2026-11-09): back and forth between a chest and the quest, never 8 tiles from one spot for long.
        struct Spot
        {
            DWORD at;
            int32_t x, y;
        };
        static std::vector<Spot> s_spots;
        static DWORD s_lastCall = 0, s_anchorAt = 0, s_sampleAt = 0;
        static int s_stage = 0;
        // Backing out: leg by leg to the trail's points, a few tiles each, until 20 tiles from where it was stuck.
        static size_t s_backIdx = 0;
        static int32_t s_backFromX = 0, s_backFromY = 0;
        static DWORD s_backSince = 0, s_backOrderAt = 0;
        if (g_backing && now - s_lastCall > 3000)
        {
            // Roaming left off meanwhile (a fight, a collect): the backing out is stale, the trail noted again.
            g_backing = false;
            LOG("AutoAttack: stuck guard: backing out left off (the agent busy with something else)");
        }
        if (g_backing)
        {
            const double away = std::hypot(static_cast<double>(self->x - s_backFromX), static_cast<double>(self->y - s_backFromY));
            if (away > 20.0 * kTileSize || now - s_backSince > 60000 || s_backIdx >= g_trail.size())
            {
                g_backing = false;
                LOG("AutoAttack: stuck guard: backed out {:.0f} tiles the way it came ({} s)", away / kTileSize,
                    (now - s_backSince) / 1000);
                Findings::note("stuck", self->x, self->y, "backed out {:.0f} tiles along its trail", away / kTileSize);
                g_trail.resize(std::min(g_trail.size(), s_backIdx + 1));
                s_spots.clear();
                s_anchorAt = now;
                g_homeX = self->x;
                g_homeY = self->y;
                g_roamStuck = 0;
                g_roamAt = 0;
                return false;
            }
            // The leg: the point furthest back along the trail still within 4 tiles of the hero.
            while (s_backIdx > 0 && std::hypot(static_cast<double>(self->x - g_trail[s_backIdx - 1].x),
                                               static_cast<double>(self->y - g_trail[s_backIdx - 1].y)) < 4.0 * kTileSize)
            {
                --s_backIdx;
            }
            const Crumb& c = g_trail[s_backIdx];
            if (std::hypot(static_cast<double>(self->x - c.x), static_cast<double>(self->y - c.y)) < kTileSize && s_backIdx == 0)
            {
                s_backIdx = g_trail.size();     // the trail's start reached: done on the next call
                return true;
            }
            if (now - s_backOrderAt > 700)
            {
                s_backOrderAt = now;
                ClickWalk::walkTo(c.x, c.y, false);
            }
            s_lastCall = now;
            return true;
        }
        const bool jumped = !s_spots.empty() && std::hypot(static_cast<double>(self->x - s_spots.back().x),
                                                           static_cast<double>(self->y - s_spots.back().y)) > 40.0 * kTileSize;
        if (!s_lastCall || now - s_lastCall > 3000 || jumped)
        {
            s_spots.clear();
            s_anchorAt = now;
            s_stage = 0;
        }
        s_lastCall = now;
        if (now - s_sampleAt >= 2000)
        {
            s_sampleAt = now;
            s_spots.push_back({now, self->x, self->y});
        }
        int32_t minX = self->x, maxX = self->x, minY = self->y, maxY = self->y;
        for (const Spot& sp : s_spots)
        {
            if (now - sp.at <= 60000)
            {
                minX = std::min(minX, sp.x);
                maxX = std::max(maxX, sp.x);
                minY = std::min(minY, sp.y);
                maxY = std::max(maxY, sp.y);
            }
        }
        while (s_spots.size() > 40)
        {
            s_spots.erase(s_spots.begin());
        }
        if (std::max(maxX - minX, maxY - minY) > 16.0 * kTileSize)
        {
            // Getting somewhere: the watch starts over.
            s_anchorAt = now;
            s_stage = 0;
            return false;
        }
        if (now - s_anchorAt < 60000u + 30000u * static_cast<DWORD>(s_stage))
        {
            return false;
        }
        ++s_stage;
        // A door near (the player, 2026-11-10: «el agente no abre puertas», a Seraphim stuck before a gate in a
        // dungeon): used first, a try of this stage.
        {
            AimAssist::Target door;
            if (AimAssist::findObject(g_doorRange, &acceptDoor, nullptr, door))
            {
                g_doorTried[door.id] = now;
                LOG("AutoAttack: stuck guard: a door near ({:x}): used, as a click on it", door.id);
                Findings::note("door", self->x, self->y, "stuck: door {:x} used", door.id);
                attack(door.id);
                g_doorHoldUntil = now + 6000;
                return true;
            }
        }
        // Shut in (Whereabouts): the ways out MapMemory saw (a portal end, the arrival of a cave's entry) walked onto,
        // each tried once in 3 minutes; standing on one already, a step off first (a teleport fires on stepping on).
        // Seen twice (2026-11-10, a Gladiator 3 h, a Seraphim 16 min): into a cave from 3180,2670, shut in at
        // 4819..4828 x 367..387, the stuck guard only walking about inside.
        if (Whereabouts::area().shutIn)
        {
            static std::unordered_map<uint64_t, DWORD> s_wayTried;
            const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
            const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
            int bx = 0, by = 0;
            double best = 1e18;
            size_t gameWays = 0;
            std::vector<std::pair<int, int>> ways = waysOutAround(layer, htx, hty, &gameWays);
            for (size_t wi = 0; wi < ways.size(); ++wi)
            {
                const auto [ex, ey] = ways[wi];
                const uint64_t wk = (static_cast<uint64_t>(static_cast<uint32_t>(ex)) << 32) | static_cast<uint32_t>(ey);
                if (const auto t = s_wayTried.find(wk); t != s_wayTried.end() && now - t->second < 180000)
                {
                    continue;
                }
                // The game's own ways ahead of those MapMemory remembers, however near.
                const double d = std::hypot(ex - htx, ey - hty) + (wi < gameWays ? 0.0 : 10000.0);
                if (d < best)
                {
                    best = d;
                    bx = ex;
                    by = ey;
                }
            }
            if (best < 1e17)
            {
                best = std::fmod(best, 10000.0);
                if (best <= 1.5)
                {
                    // On it: through it when the door's other end is marked (the layer flips one step on); else a step off,
                    // the next stage walks back onto it.
                    const double a = now * 0.001;
                    int tx = 0, ty = 0;
                    if (beyondWay(layer, bx, by, tx, ty))
                    {
                        ClickWalk::walkTo(static_cast<int32_t>((tx + 0.5) * kTileSize), static_cast<int32_t>((ty + 0.5) * kTileSize),
                                          false);
                        LOG("AutoAttack: stuck guard: shut in, on the way out at {},{}: through it, to {},{}", bx, by, tx, ty);
                        return true;
                    }
                    ClickWalk::walkTo(static_cast<int32_t>(self->x + std::cos(a) * 3 * kTileSize),
                                      static_cast<int32_t>(self->y + std::sin(a) * 3 * kTileSize), false);
                    LOG("AutoAttack: stuck guard: shut in, on the way out at {},{}: a step off to step on again", bx, by);
                    return true;
                }
                s_wayTried[(static_cast<uint64_t>(static_cast<uint32_t>(bx)) << 32) | static_cast<uint32_t>(by)] = now;
                LOG("AutoAttack: stuck guard: shut in: to the way out at {},{} ({:.0f} tiles)", bx, by, best);
                Findings::note("stuck", self->x, self->y, "shut in: to the way out at {},{}", bx, by);
                {
                    int32_t ax = 0, ay = 0;
                    aimThrough(static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize), bx, by, ax, ay);
                    ClickWalk::walkTo(ax, ay, false);
                }
                g_wayOutX = static_cast<int32_t>((bx + 0.5) * kTileSize);
                g_wayOutY = static_cast<int32_t>((by + 0.5) * kTileSize);
                g_wayOutUntil = now + static_cast<DWORD>(std::min(45.0, 10.0 + best * 0.7) * 1000.0);
                return true;
            }
        }
        if (s_stage == 1)
        {
            // Stuck again near where the marks were last forgotten (seen live 2026-11-11, A3: 20 min looping at 24 tiles
            // from a quest creature behind a fence): forgetting would send it back to the same goal, so the goal it
            // was going for is left 10 min instead.
            static DWORD s_forgotAt = 0;
            static int32_t s_forgotX = 0, s_forgotY = 0;
            if (s_forgotAt && now - s_forgotAt < 600000 &&
                std::hypot(static_cast<double>(self->x - s_forgotX), static_cast<double>(self->y - s_forgotY)) <
                    30.0 * kTileSize)
            {
                const auto leave = [&](int32_t gx, int32_t gy) {
                    if (!gx && !gy)
                    {
                        return;
                    }
                    const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(gx / kTileSize)) << 32) |
                                         static_cast<uint32_t>(gy / kTileSize);
                    g_travelBlocked[key] = now + 600000;
                };
                leave(g_questX, g_questY);
                leave(g_travel.x, g_travel.y);
                LOG("AutoAttack: stuck guard: stuck again where it was {} s ago: the goal at tile {},{} left 10 min (the "
                    "travel's goal {},{})",
                    (now - s_forgotAt) / 1000, static_cast<int>(g_questX / kTileSize),
                    static_cast<int>(g_questY / kTileSize), static_cast<int>(g_travel.x / kTileSize),
                    static_cast<int>(g_travel.y / kTileSize));
                Findings::note("stuck", self->x, self->y, "stuck again: the goal at tile {},{} left 10 min",
                               static_cast<int>(g_questX / kTileSize), static_cast<int>(g_questY / kTileSize));
                g_questX = g_questY = 0;
                g_travel = Travel{};
                s_forgotAt = 0;
                return false;
            }
            s_forgotAt = now;
            s_forgotX = self->x;
            s_forgotY = self->y;
            LOG("AutoAttack: stuck guard: 60 s within 16 tiles out of the fights: the marks «left for now» forgotten");
            Findings::note("stuck", self->x, self->y, "60 s within a box of 16 tiles out of the fights: marks forgotten");
            forgetTalks();
            // Only the short marks (10 min or less left): the long ones (a goal with no way found three or four times,
            // 45 min to 2 h) are what the failures taught, and clearing them here sent the hero back to the same goal
            // just when it was stuck (the study, 2026-11-18, card 11 of Decisiones-agente).
            size_t kept = 0;
            for (auto it = g_travelBlocked.begin(); it != g_travelBlocked.end();)
            {
                if (static_cast<int>(it->second - now) > 600000)
                {
                    ++kept;
                    ++it;
                }
                else
                {
                    it = g_travelBlocked.erase(it);
                }
            }
            if (kept)
            {
                LOG("AutoAttack: stuck guard: {} long-held goals kept held", kept);
            }
            return false;
        }
        // First the way it came: points of the trail more than 20 tiles back from here, if it has them.
        if (s_stage == 2 && g_trail.size() > 3)
        {
            g_backing = true;
            s_backIdx = g_trail.size() - 1;
            s_backFromX = self->x;
            s_backFromY = self->y;
            s_backSince = now;
            s_backOrderAt = 0;
            LOG("AutoAttack: stuck guard: backing out the way it came ({} points of trail)", g_trail.size());
            Findings::note("stuck", self->x, self->y, "backing out along its trail ({} points)", g_trail.size());
            return true;
        }
        const double angle = s_stage * 2.39996;     // the golden angle: each try a new way round
        const int tx = static_cast<int>((self->x + std::cos(angle) * 15.0 * kTileSize) / kTileSize);
        const int ty = static_cast<int>((self->y + std::sin(angle) * 15.0 * kTileSize) / kTileSize);
        int nx = tx, ny = ty;
        Whereabouts::nearestReachable(tx, ty, nx, ny);
        const int32_t wx = static_cast<int32_t>((nx + 0.5) * kTileSize), wy = static_cast<int32_t>((ny + 0.5) * kTileSize);
        LOG("AutoAttack: stuck guard: still nowhere after {} s: a walk to tile {},{} (try {})", (now - s_anchorAt) / 1000,
            nx, ny, s_stage - 1);
        Findings::note("stuck", self->x, self->y, "still nowhere after {} s: walk to tile {},{} (try {})",
                       (now - s_anchorAt) / 1000, nx, ny, s_stage - 1);
        ClickWalk::walkTo(wx, wy, false);
        MapMemory::setRoute(true, wx, wy);
        g_homeX = wx;
        g_homeY = wy;
        g_roamStuck = 0;
        g_roamAt = now;
        g_walkX = wx;
        g_walkY = wy;
        return true;
    }

    void roam(DWORD now)
    {
        if ((!Config::autoAttack.roam && !Config::autoAttack.quests) || g_retreatUntil)
        {
            g_quietSince = 0;
            return;
        }
        if (!g_quietSince)
        {
            g_quietSince = now;
        }
        cObjectManager* objects = cObjectManager::instance();
        cEngine* engine = FrameHooks::engine();
        cCreature* self = objects && engine ? objects->creature(engine->controlled) : nullptr;
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (self && hero && stuckGuard(now, self))
        {
            return;
        }
        // On the way to the way out the stuck guard ordered (see g_wayOutUntil): no farm zone, quest, companion wait or
        // loot takes the walk over; the order is given again if something cut it short. Ends there, at the time limit
        // or once the area is no longer shut in.
        if (self && hero && g_wayOutUntil)
        {
            if (Whereabouts::area().shutIn && static_cast<int>(now - g_wayOutUntil) < 0 &&
                std::hypot(static_cast<double>(g_wayOutX - self->x), static_cast<double>(g_wayOutY - self->y)) > 1.2 * kTileSize)
            {
                static DWORD s_wayOutAskAt = 0;
                if (!ClickWalk::routing() && now - s_wayOutAskAt > 3000)
                {
                    s_wayOutAskAt = now;
                    ClickWalk::walkTo(g_wayOutX, g_wayOutY, false);
                }
                return;
            }
            g_wayOutUntil = 0;
        }
        if (static_cast<int>(now - g_doorHoldUntil) < 0 || static_cast<int>(now - g_craftHoldUntil) < 0)
        {
            return;     // on the way to the door just clicked, or by a craftsman whose window is being worked
        }
        // By an open shop: nothing new until Gear's trip is through (the player, 2026-11-16: «no les da tiempo a
        // comercializar todo antes de irse»; A2 opened 85e's shop at 03:08:40, chose to farm that same second and
        // walked off 131 tiles, the shop closing on «its merchant is not near» after 4 sales). Up to 3 min, as a
        // trade flag left set by a death in the shop must not hold the agent for ever.
        {
            static DWORD s_shopHoldSince = 0;
            if (Gear::shopOpen())
            {
                s_shopHoldSince = s_shopHoldSince ? s_shopHoldSince : now;
                if (now - s_shopHoldSince < 180000)
                {
                    return;
                }
            }
            else
            {
                s_shopHoldSince = 0;
            }
        }
        // Shut in with a door that opens near (the player, 2026-11-10: «la cueva tiene puertas que el agente no sabe
        // abrir»; the cave was worth staying in, only the way on was shut): opened at once, the way on before the way
        // out, every 8 s at most, each door once in 2 minutes.
        static DWORD s_doorAt = 0;
        if (self && hero && (!s_doorAt || now - s_doorAt > 8000) && Whereabouts::area().shutIn)
        {
            s_doorAt = now;
            const float range = g_doorRange;
            g_doorRange = 20.0f * kTileSize;
            AimAssist::Target door;
            const bool found = AimAssist::findObject(g_doorRange, &acceptDoor, nullptr, door);
            g_doorRange = range;
            if (found)
            {
                g_doorTried[door.id] = now;
                setIntent(Intent::Escape, "shut in: the doors first, the way on");
                LOG("AutoAttack: shut in, a door that opens near ({:x}): opened, the way on", door.id);
                Findings::note("door", self->x, self->y, "shut in: door {:x} opened", door.id);
                attack(door.id);
                g_doorHoldUntil = now + 6000;
                return;
            }
        }
        if (!self || !hero || now - g_quietSince < kRoamQuietMs || (g_roamAt && now - g_roamAt < kRoamStepMs) ||
            hero->health * 100 < hero->maxHealth * 60)
        {
            return;
        }
        // The step under way: the next one once it is there, or has stopped walking (the hero is slow: a tile a
        // second or so), or after a while at most.
        if (g_roamAt)
        {
            const double tx = g_walkX - self->x, ty = g_walkY - self->y;
            const bool there = tx * tx + ty * ty < 0.36 * kTileSize * kTileSize;
            const bool walking = CombatState::action(self) == CombatState::Walking;
            if (!there && walking && now - g_roamAt < kRoamStepMaxMs)
            {
                return;
            }
        }
        const int layer = *(reinterpret_cast<const uint8_t*>(self) + kLayer);
        // A new home: the first roam, or the hero far from where the last step left it (a teleport, a portal, stairs
        // to another layer).
        const double jx = self->x - g_roamFromX, jy = self->y - g_roamFromY;
        if (!g_homeSet || layer != g_roamLayer || ((g_roamFromX || g_roamFromY) && jx * jx + jy * jy > (40 * kTileSize) * (40 * kTileSize)))
        {
            g_homeX = self->x;
            g_homeY = self->y;
            g_homeSet = true;
            g_roamLayer = layer;
            g_roamAt = 0;
            g_roamStuck = 0;
            g_roamAngle = jitter(0, 628) / 100.0;
        }
        // Where the hero is going, for Gear's pieces by zone: the quest goal's region, or the hero's own.
        {
            const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40);
            const uint8_t* world = holder ? *reinterpret_cast<const uint8_t* const*>(holder) : nullptr;
            const bool goal = g_questX || g_questY;
            g_destRegion = sectorRegion(world, static_cast<int>((goal ? g_questX : self->x) / kTileSize),
                                        static_cast<int>((goal ? g_questY : self->y) / kTileSize));
            // The next goal in another region: a town stop first (Gear: the merchant, then the storage chest).
            const int here = sectorRegion(world, static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize));
            const int dest = g_destRegion.load();
            // Not while a quest's time runs (the quests study, 2026-11-23: A7 took 1202, «Hierbas curativas», 4320 game
            // min, then a town stop and four other quests first; failed at the deadline), unless the potions are low.
            const bool timed = std::any_of(g_questBook.begin(), g_questBook.end(),
                                           [](const QuestGoal& g) { return g.minutesLeft > 0; });
            const bool potionsLow = Gear::healingLeft() >= 0 && Gear::healingLeft() <= 2;
            Gear::prepareFor(goal && here >= 0 && dest >= 0 && dest != here && (!timed || potionsLow) ? dest : -1, here);
        }
        // The storage chest (the player, 2026-11-16: «consciencia del almacén [...] deberá contener equipamiento con
        // resistencia a la zona donde van»): pieces to keep for other zones, or one to take out for where the hero is
        // going (Gear::wantsStorage), and a storage chest seen within 40 tiles: gone to and used as a player does (a
        // click on it); Gear moves the pieces while its window is open and closes it. Not before the merchant.
        static DWORD s_storageFailedAt = 0, s_storageAskAt = 0, s_storageClickAt = 0;
        static int s_storageTries = 0;
        {
            double nearest = 0.0;
            StorageSeen pick;
            for (const auto& [id, st] : g_storages)
            {
                const double d = std::hypot(static_cast<double>(st.x - self->x), static_cast<double>(st.y - self->y));
                if (st.layer == layer && (!pick.id || d < nearest))
                {
                    pick = st;
                    nearest = d;
                }
            }
            if (pick.id != g_storage.id)
            {
                s_storageTries = 0;
            }
            g_storage = pick;
        }
        // 40 tiles; the town stop's visit 120 (the chest of the town the hero is in or near).
        const double storageReach = (Gear::prepStorage() ? 120.0 : 40.0) * kTileSize;
        g_storageNear = g_storage.id && g_storage.layer == layer &&
                        (!s_storageFailedAt || now - s_storageFailedAt > 600000) &&
                        std::hypot(static_cast<double>(g_storage.x - self->x), static_cast<double>(g_storage.y - self->y)) <=
                            storageReach;
        // The hero stays at the chest while the visit's work goes on (A4, 2026-11-16 20:37: a piece taken out, then
        // off to the combo master with the chest's window half done: it closed behind him, the chest still marked in
        // use). Gear ends the visit (closed, or 20 s with the window gone).
        if (Gear::storageOpen() && !Gear::storagePending() && Act::may(Act::Kind::Storage))
        {
            setIntent(Intent::Shop, "at the storage chest: its work under way");
            g_roamAt = 0;
            return;
        }
        // Held from the click until the chest's window opens (A5, 2026-11-16: the quest took the hero away the next
        // tick, «its window never opened»); Gear gives the visit up after 20 s.
        if ((Gear::wantsStorage() || Gear::storagePending()) && (!Gear::storageOpen() || Gear::storagePending()) &&
            (!Gear::wantsShop() || Gear::storageFirst()) && g_storage.id && g_storage.layer == layer &&
            Act::may(Act::Kind::Storage) && (!s_storageFailedAt || now - s_storageFailedAt > 600000))
        {
            const double d = std::hypot(static_cast<double>(g_storage.x - self->x), static_cast<double>(g_storage.y - self->y));
            if (d <= storageReach)
            {
                setIntent(Intent::Shop, "pieces for the storage chest: to it");
                if (d > 4.0 * kTileSize)
                {
                    if (!travel(now, self, g_storage.x, g_storage.y, s_storageAskAt))
                    {
                        LOG("AutoAttack: no way to the storage chest {:x}: left 10 min", g_storage.id);
                        s_storageFailedAt = now;
                    }
                }
                else if (!s_storageClickAt || now - s_storageClickAt > 3000)
                {
                    if (++s_storageTries > 5)
                    {
                        LOG("AutoAttack: the storage chest {:x} would not open: left 10 min", g_storage.id);
                        s_storageFailedAt = now;
                        s_storageTries = 0;
                    }
                    else if (Act::allowed(Act::Kind::Storage, "open the storage chest to keep or take pieces for a zone"))
                    {
                        LOG("AutoAttack: opening the storage chest {:x} (try {})", g_storage.id, s_storageTries);
                        s_storageClickAt = now;
                        Gear::storageUsed(g_storage.id);
                        attack(g_storage.id);
                    }
                }
                MapMemory::setRoute(true, g_storage.x, g_storage.y);
                g_roamAt = 0;
                return;
            }
        }
        else if (!Gear::wantsStorage())
        {
            s_storageTries = 0;
        }
        // The backpack full: off to the nearest merchant (however far, as to a quest), the shop opened with a click on
        // him as the player's; Gear sells and puts on the upgrades, then the agent closes it (onFrame).
        if (Gear::wantsShop() && !Gear::shopOpen())
        {
            if (g_exitUntil)
            {
                if (static_cast<int>(now - g_exitUntil) < 0 &&
                    std::hypot(static_cast<double>(g_exitX - self->x), static_cast<double>(g_exitY - self->y)) > 3.0 * kTileSize)
                {
                    g_questTravel = true;
                    setIntent(Intent::Shop, "no merchant can be reached: out by the nearest way in or out");
                    if (!travel(now, self, g_exitX, g_exitY, g_shopAskAt))
                    {
                        g_exitUntil = 0;
                    }
                    MapMemory::setRoute(true, g_exitX, g_exitY);
                    g_roamAt = 0;
                    return;
                }
                g_exitUntil = 0;
            }
            // A hero too weak to fight its way (level 3 or under, one potion or none): a group of three or more within 25 tiles
            // is not walked into, and a merchant over 200 tiles off by a way that crosses where it died lately or met a group
            // is not gone to (the stuck solver, 2026-11-16, A7): the experience first, on single enemies, and the trip again
            // after 5 min; the trip and the places are told once.
            const bool fragile = fragileHero();
            bool shutByDeath = false;
            if (fragile)
            {
                double gx = 0.0, gy = 0.0;
                if (groupWithin(self, 25.0, now, gx, gy) >= 3)
                {
                    g_dangerSpots.push_back({static_cast<int>(gx / kTileSize), static_cast<int>(gy / kTileSize), now});
                    LOG("AutoAttack: three or more enemies within 25 tiles on the way to a merchant ({} potions, hero too weak): "
                        "not walked into, around {},{} shunned 10 min; no trip for 5 min", Gear::healingLeft(),
                        static_cast<int>(gx / kTileSize), static_cast<int>(gy / kTileSize));
                    Gear::noTripFor(300000);
                    g_shopId = 0;
                    g_roamAt = 0;
                    return;
                }
            }
            auto deadlyWay = [&](int32_t mx, int32_t my, double walk) {
                if (fragile && walk > 200.0 * kTileSize && deathOnTheWay(self, mx, my, layer))
                {
                    shutByDeath = true;
                    return true;
                }
                return false;
            };
            const Merchant* best = nullptr;
            double bestDistance = 0.0, bestRank = 0.0;
            // The merchant being gone to, kept: the game's list holds only the creatures it has loaded about the hero, and
            // the one gone for leaves it as the hero walks (the stuck solver, 2026-11-16, A2 and A7: «off to merchant» 348,
            // 1f67, 1cf, 1f70, 1a1f, 1fbe, 1cf, 1cca in 9 minutes, 128-310 tiles each, the backpack never emptied; the
            // trip began again at each change).
            static Merchant s_sticky{};
            static DWORD s_stickySince = 0;
            for (const Merchant& m : g_merchants)
            {
                const auto failed = g_shopFailedAt.find(m.id);
                double d = std::hypot(static_cast<double>(m.x - self->x), static_cast<double>(m.y - self->y));
                // With no healing potion left a merchant is worth a long walk (the stuck solver, 2026-11-14: A8's
                // Daemon died 10 times in 29 min, «no merchant known within 150 tiles» at each load, 13 325 gold).
                // The merchant already gone for keeps twice the reach: the walk's length (wayLength) rises and falls
                // around the limit as the hero fights its way there, and the choice flipped quest/shop every 10-50 s
                // (the stuck solver, 2026-11-16, A2: «off to merchant 85e (400 tiles)», six flips in 5 minutes).
                // Pieces taken out of a crowded storage to sell count as a full backpack (a near full one stays at 150:
                // the quests first).
                const double shopReach = (Gear::needsLongTrip() ? 700.0 : 150.0) *
                                         (m.id == g_shopId ? 2.0 : 1.0) * kTileSize;
                if (m.layer == layer && d <= shopReach)
                {
                    d = wayLength(self->x, self->y, m.x, m.y);    // the walk, not the straight line
                }
                // One the route net cannot reach (the stuck solver, 2026-11-17, A2 and A8: merchant 1cf at 3242,2864, the
                // multiplayer start's enclave, 620 and 217 tiles off, «the net has no way between the nodes near either end»
                // at each try: the hero walked its crude straight orders 150 s, «no nearer», left it 30 min, and went on to
                // the next one beyond the same gap, an hour in all with the potions at 0): left 30 min at once.
                if (layer == 0 && m.layer == 0 && d <= shopReach &&
                    !(g_shopUselessAt.count(m.id) && now - g_shopUselessAt[m.id] < 1800000))
                {
                    const int ftx = static_cast<int>(self->x / kTileSize), fty = static_cast<int>(self->y / kTileSize);
                    const int mtx = static_cast<int>(m.x / kTileSize), mty = static_cast<int>(m.y / kTileSize);
                    if (std::max(std::abs(ftx - mtx), std::abs(fty - mty)) > 100)
                    {
                        RouteNet::walkTiles(ftx, fty, mtx, mty);    // asked (worked out on a low thread); the answer next pass
                        if (RouteNet::knownNoWay(ftx, fty, mtx, mty))
                        {
                            g_shopUselessAt[m.id] = now;
                            LOG("AutoAttack: merchant {:x} at {},{} ({:.0f} tiles): the route net has no way to it: left 30 min",
                                m.id, mtx, mty, d / kTileSize);
                            continue;
                        }
                    }
                }
                // One in a house (its floor another layer) only near: a click on him sends the hero there by the game's
                // own path finder, which opens the doors on the way (the player: «algunos comerciantes se encuentran
                // dentro de casas»).
                // Nor one across the world (the player, 2026-11-10: the Daemon, level 3, set off for a merchant 427
                // tiles off through higher grounds and got stuck on the way): 150 tiles at most.
                if ((m.layer != layer && d > 30.0 * kTileSize) || d > shopReach ||
                    (failed != g_shopFailedAt.end() && now - failed->second < 300000) ||
                    (g_shopUselessAt.count(m.id) && now - g_shopUselessAt[m.id] < 1800000) || deadlyWay(m.x, m.y, d))
                {
                    continue;
                }
                const double rank = m.id == g_shopId ? d * 0.75 : d;
                if (!best || rank < bestRank)
                {
                    best = &m;
                    bestDistance = d;
                    bestRank = rank;
                }
            }
            // Kept to the end: the merchant gone for stays the one unless another is under 40 % of its walk, until 10 min
            // after the choice, a failure or the shop opening (a fight cuts nothing: the roam comes back to it).
            if (g_shopId)
            {
                for (const Merchant& m : g_merchants)
                {
                    if (m.id == g_shopId)
                    {
                        s_sticky = m;       // its place as the game gives it now
                    }
                }
                const auto failedMine = g_shopFailedAt.find(g_shopId);
                if (s_sticky.id == g_shopId && now - s_stickySince < 600000 &&
                    !(failedMine != g_shopFailedAt.end() && now - failedMine->second < 300000) &&
                    !(g_shopUselessAt.count(g_shopId) && now - g_shopUselessAt[g_shopId] < 1800000))
                {
                    const double walkMine = wayLength(self->x, self->y, s_sticky.x, s_sticky.y);
                    if (!(s_sticky.layer != layer && walkMine > 30.0 * kTileSize) && !deadlyWay(s_sticky.x, s_sticky.y, walkMine) &&
                        (!best || best->id == g_shopId || bestDistance > walkMine * 0.4))
                    {
                        best = &s_sticky;
                        bestDistance = walkMine;
                    }
                }
            }
            if (best)
            {
                g_questTravel = true;
                setIntent(Intent::Shop, "the backpack full or no healing potion: to a merchant");
                if (best->id != g_shopId)
                {
                    LOG("AutoAttack: backpack full, off to merchant {:x} ({:.0f} tiles)", best->id, bestDistance / kTileSize);
                    g_shopId = best->id;
                    s_sticky = *best;
                    s_stickySince = now;
                    g_shopTries = 0;
                    g_shopClickAt = 0;
                }
                // Far: the agent's travel; near (15 tiles) or in a house: clicks on him, the game's own path through
                // the doors, more tries for the walk.
                const bool closeBy = bestDistance <= 15.0 * kTileSize || best->layer != layer;
                if (!closeBy)
                {
                    static ShopWatch s_listWatch;
                    if (shopNoProgress(s_listWatch, best->id, bestDistance, now))
                    {
                        LOG("AutoAttack: merchant {:x} no nearer in 150 s ({:.0f} tiles): left 30 min", best->id,
                            bestDistance / kTileSize);
                        g_shopUselessAt[best->id] = now;
                        g_shopId = 0;
                        s_listWatch = ShopWatch{};
                        if (shopStalledTwice(now))
                        {
                            LOG("AutoAttack: two merchants in a row not reached: no trip for 10 min, the experience first");
                            Gear::noTripFor(600000);
                        }
                        armExit(now, self, layer);
                        g_roamAt = 0;
                        return;
                    }
                    if (!travel(now, self, best->x, best->y, g_shopAskAt))
                    {
                        g_shopFailedAt[best->id] = now;
                        g_shopId = 0;
                    }
                }
                else if (!g_shopClickAt || now - g_shopClickAt > 3000)
                {
                    if (++g_shopTries > (bestDistance > 3.0 * kTileSize ? 10 : 5))
                    {
                        LOG("AutoAttack: merchant {:x} would not trade, left 5 min", best->id);
                        g_shopFailedAt[best->id] = now;
                        g_shopId = 0;
                    }
                    else
                    {
                        LOG("AutoAttack: opening the shop of {:x} (try {})", best->id, g_shopTries);
                        g_shopClickAt = now;
                        attack(best->id);
                    }
                }
                MapMemory::setRoute(true, best->x, best->y);
                g_roamAt = 0;
                return;
            }
            // Only the town stop's merchant and none in reach: the stop goes on without him (no long walk for it).
            if (Gear::prepShopOnly())
            {
                Gear::prepShopSkip("none within reach");
                g_roamAt = 0;
                return;
            }
            // With two healing potions or fewer the merchants the map remembers count too (the stuck solver, 2026-11-16:
            // A8 sat 67 min at 0 potions with 999 753 gold, died 22 times and logged «no merchant known» after each load
            // with «5 merchants known» in the list on all 16 lines: five listed, none chosen (reach, route, failed or
            // layer: the lines below say which), while its map kept three merchants 300 tiles off). It walks to the tile
            // where a shop once opened; the merchant is in the list by then and the trip goes on as always.
            // The same for a full backpack or pieces taken out to sell (not a near full one: the quests first).
            if (Gear::needsLongTrip())
            {
                static std::unordered_map<uint64_t, DWORD> s_remFailedAt;
                static uint64_t s_remKey = 0;
                const int remTx = static_cast<int>(self->x / kTileSize), remTy = static_cast<int>(self->y / kTileSize);
                double remWay = 0.0, remRank = 0.0;
                int remX = 0, remY = 0;
                bool remFound = false;
                for (const auto& [mx, my] : MapMemory::merchantsNear(layer, remTx, remTy, 700))
                {
                    const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(mx)) << 32) | static_cast<uint32_t>(my);
                    // A merchant left is his town left (the agent study, 2026-11-24: A6's eight remembered merchants were
                    // mostly one town 600 tiles off, each tried 150 s and left in turn, the same unreachable way each time).
                    const int cx = mx, cy = my;
                    if (std::any_of(s_remFailedAt.begin(), s_remFailedAt.end(), [&](const auto& f) {
                            const int fx = static_cast<int>(static_cast<uint32_t>(f.first >> 32));
                            const int fy = static_cast<int>(static_cast<uint32_t>(f.first));
                            return now - f.second < 1800000 && std::abs(fx - cx) <= 40 && std::abs(fy - cy) <= 40;
                        }))
                    {
                        continue;
                    }
                    const double way = wayLength(self->x, self->y, static_cast<int32_t>((mx + 0.5) * kTileSize),
                                                 static_cast<int32_t>((my + 0.5) * kTileSize));
                    if (layer == 0 && std::max(std::abs(remTx - mx), std::abs(remTy - my)) > 100)
                    {
                        RouteNet::walkTiles(remTx, remTy, mx, my);
                        if (RouteNet::knownNoWay(remTx, remTy, mx, my))
                        {
                            s_remFailedAt[key] = now;
                            LOG("AutoAttack: the remembered merchant {},{} ({:.0f} tiles): the route net has no way to it: left 30 min",
                                mx, my, way / kTileSize);
                            continue;
                        }
                    }
                    const double rank = key == s_remKey ? way * 0.75 : way;
                    if (way <= 900.0 * kTileSize && (!remFound || rank < remRank) &&
                        !deadlyWay(static_cast<int32_t>((mx + 0.5) * kTileSize), static_cast<int32_t>((my + 0.5) * kTileSize), way))
                    {
                        remFound = true;
                        remWay = way;
                        remRank = rank;
                        remX = mx;
                        remY = my;
                    }
                }
                if (remFound)
                {
                    const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(remX)) << 32) | static_cast<uint32_t>(remY);
                    if (remWay < 12.0 * kTileSize)
                    {
                        // There and the list still has no merchant: not this one (the guess about the list was wrong here).
                        s_remFailedAt[key] = now;
                        s_remKey = 0;
                        LOG("AutoAttack: at the remembered merchant {},{} and none in the game's list: left 30 min", remX, remY);
                    }
                    else
                    {
                        if (key != s_remKey)
                        {
                            s_remKey = key;
                            LOG("AutoAttack: no merchant in the game's list and {} healing potions: off to the one the map "
                                "remembers at {},{} ({:.0f} tiles)", Gear::healingLeft(), remX, remY, remWay / kTileSize);
                        }
                        static ShopWatch s_remWatch;
                        if (shopNoProgress(s_remWatch, key, remWay, now))
                        {
                            LOG("AutoAttack: the remembered merchant {},{} no nearer in 150 s ({:.0f} tiles): left 30 min", remX,
                                remY, remWay / kTileSize);
                            s_remFailedAt[key] = now;
                            s_remKey = 0;
                            s_remWatch = ShopWatch{};
                            if (shopStalledTwice(now))
                            {
                                LOG("AutoAttack: two merchants in a row not reached: no trip for 10 min, the experience first");
                                Gear::noTripFor(600000);
                            }
                            armExit(now, self, layer);
                            g_roamAt = 0;
                            return;
                        }
                        g_questTravel = true;
                        setIntent(Intent::Shop, "no healing potion: to the merchant the map remembers");
                        const int32_t remWx = static_cast<int32_t>((remX + 0.5) * kTileSize);
                        const int32_t remWy = static_cast<int32_t>((remY + 0.5) * kTileSize);
                        if (!travel(now, self, remWx, remWy, g_shopAskAt))
                        {
                            s_remFailedAt[key] = now;
                            s_remKey = 0;
                        }
                        MapMemory::setRoute(true, remWx, remWy);
                        g_roamAt = 0;
                        return;
                    }
                }
            }
            // Every way crossed a place of death or a group: the experience first, the trip again after 5 min.
            if (shutByDeath)
            {
                LOG("AutoAttack: every way to a merchant crosses where the hero died lately or met a group ({} potions, hero "
                    "too weak): no trip for 5 min, the experience first", Gear::healingLeft());
                Gear::noTripFor(300000);
                g_shopId = 0;
                g_roamAt = 0;
                return;
            }
            // Only nearly full, potions in stock and no merchant within reach: no trip for 10 min (the trip's want would hold
            // back the seek meanwhile).
            if (!Gear::packFull() && !(Gear::healingLeft() >= 0 && Gear::healingLeft() <= 2))
            {
                Gear::noTripFor(600000);
            }
            if (!g_shopTold)
            {
                g_shopTold = true;
                LOG("AutoAttack: backpack full and no merchant known within 150 tiles on this layer ({} potions, {} in the "
                    "game's list)", Gear::healingLeft(), g_merchants.size());
                int shown = 0;
                for (const Merchant& m : g_merchants)
                {
                    if (shown++ >= 4)
                    {
                        break;
                    }
                    const auto failed = g_shopFailedAt.find(m.id);
                    const double straight = std::hypot(static_cast<double>(m.x - self->x), static_cast<double>(m.y - self->y));
                    const double byRoute = m.layer == layer && straight <= 1000.0 * kTileSize
                                               ? wayLength(self->x, self->y, m.x, m.y) : straight;
                    const double reach = ((Gear::healingLeft() >= 0 && Gear::healingLeft() <= 2) || Gear::packFull() ? 700.0 : 150.0) *
                                         (m.id == g_shopId ? 2.0 : 1.0);
                    LOG("AutoAttack: merchant {:x}: layer {} (hero {}), {:.0f} tiles straight, {:.0f} by the map's route, "
                        "reach {:.0f}, failed {}, useless {}", m.id, m.layer, layer, straight / kTileSize,
                        byRoute / kTileSize, reach, failed != g_shopFailedAt.end() && now - failed->second < 300000,
                        g_shopUselessAt.count(m.id) && now - g_shopUselessAt[m.id] < 1800000);
                }
            }
        }
        // Runes of other classes (Gear::wantsRuneSwap): off to the nearest combo master as to a merchant, a click on
        // him opens his window. The swap itself waits for Manolito's block S; meanwhile the window's UI objects are
        // logged once it opens and the trip is left 30 min.
        {
            static uint32_t s_masterId = 0;
            static DWORD s_leftAt = 0, s_clickAt = 0, s_askAt = 0;
            static int s_tries = 0;
            const uint8_t mode = *(reinterpret_cast<const uint8_t*>(self) + 0xFC);
            const uint32_t npc = *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x100);
            if (s_masterId && mode == 0xA && npc == s_masterId)
            {
                LOG("AutoAttack: at craftsman {:x} ({} runes of other classes): his window open", s_masterId,
                    Gear::foreignRunes());
                // The hero stays by him while Gear works his window (the live verifier, 2026-11-10: four stable
                // visits, the hero back on its quest 6 s after the window opened and no «Gear: horse» line).
                g_craftHoldUntil = now + 25000;     // a forge of 12 steps takes longer than 15 s (the code reviewer)
                static bool s_windowsLogged = false;
                if (const uint8_t* ui = !s_windowsLogged ? *reinterpret_cast<const uint8_t* const*>(0x17EEBBC) : nullptr;
                    ui && (s_windowsLogged = true))
                {
                    for (int i = 0; i < 48; ++i)
                    {
                        const auto* w = *reinterpret_cast<const uint8_t* const*>(ui + 0x80 + 4 * i);
                        if (w && !IsBadReadPtr(w, 0x14))
                        {
                            LOG("AutoAttack: ui window {} at +{:x}: vtable {:x}, +0x10 {:x}", i, 0x80 + 4 * i,
                                *reinterpret_cast<const uint32_t*>(w), *reinterpret_cast<const uint32_t*>(w + 0x10));
                        }
                    }
                }
                // A minute's pause only: each want backs off by itself once tried (Gear), and a 30 min bar here
                // kept the next craftsman away (the live verifier, 2026-11-10: the stable's visit barred the combo
                // master's).
                s_leftAt = now - 1800000 + 60000;
                s_masterId = 0;
            }
            const bool toMaster = Gear::wantsRuneSwap() || Gear::wantsCombo();
            const bool toSmith = !toMaster && Gear::wantsSocket();
            if ((toMaster || toSmith || Gear::wantsHorse()) && !Gear::wantsShop() && (!s_leftAt || now - s_leftAt > 1800000))
            {
                const Merchant* best = nullptr;
                double bestDistance = 0.0;
                for (const Merchant& m : toMaster ? g_masters : toSmith ? g_smiths : g_stables)
                {
                    double d = std::hypot(static_cast<double>(m.x - self->x), static_cast<double>(m.y - self->y));
                    if (m.layer == layer && d <= 300.0 * kTileSize)
                    {
                        d = wayLength(self->x, self->y, m.x, m.y);    // the walk, not the straight line
                    }
                    if ((m.layer == layer || d < 30.0 * kTileSize) && (!best || d < bestDistance))
                    {
                        best = &m;
                        bestDistance = d;
                    }
                }
                // The quests are the game's progress (the player, 2026-11-10: «el objetivo principal del agente siempre
                // tiene que ser las misiones»): a combo, a rune swap, a socket or a horse is no trip away from one,
                // only when the craftsman is at hand (40 tiles) or no quest is open.
                int32_t qx = 0, qy = 0;
                double qr = 0.0;
                uint32_t qwho = 0;
                const bool questOpen = Config::autoAttack.quests && questTarget(self->x, self->y, qx, qy, qr, qwho);
                // Runes of other classes worth more swaps reach a master farther off (A5 2026-11-12: 11 runes, three
                // new arts, the masters 65-137 tiles off, never gone to): 40 tiles and 60 more for each swap past the
                // first, up to 200; the master already gone for, twice that (A2: off at 40 tiles, back to the quest
                // at 158 without reaching him).
                double reach = 40.0;
                if (toMaster && !Gear::wantsCombo())
                {
                    reach = std::min(200.0, 40.0 + 60.0 * std::max(0, Gear::foreignRunes() / 3 - 1));
                }
                if (best && best->id == s_masterId)
                {
                    reach *= 2.0;
                }
                if (best && questOpen && bestDistance > reach * kTileSize)
                {
                    static DWORD s_toldAt = 0;
                    if (!s_toldAt || now - s_toldAt > 300000)
                    {
                        s_toldAt = now;
                        LOG("AutoAttack: a craftsman {:.0f} tiles off: the quest first, he waits till one is near",
                            bestDistance / kTileSize);
                    }
                    best = nullptr;
                }
                if (best)
                {
                    g_questTravel = true;
                    setIntent(Intent::Shop, !toMaster && !toSmith ? "no horse: to a stable"
                                            : !toMaster            ? "something to socket: to a smith"
                                            : Gear::wantsCombo() ? "a combo to learn: to a combo master"
                                                               : "runes of other classes: to a combo master to swap them");
                    if (best->id != s_masterId)
                    {
                        LOG("AutoAttack: {} runes of other classes; off to the craftsman {:x} ({:.0f} tiles)",
                            Gear::foreignRunes(), best->id, bestDistance / kTileSize);
                        s_masterId = best->id;
                        s_tries = 0;
                        s_clickAt = 0;
                    }
                    if (bestDistance > 15.0 * kTileSize && best->layer == layer)
                    {
                        if (!travel(now, self, best->x, best->y, s_askAt))
                        {
                            LOG("AutoAttack: craftsman {:x} out of reach: left 30 min", best->id);
                            s_leftAt = now;
                            s_masterId = 0;
                        }
                    }
                    else if (!s_clickAt || now - s_clickAt > 3000)
                    {
                        if (++s_tries > 10)
                        {
                            LOG("AutoAttack: craftsman {:x} would not open his window: left 30 min", best->id);
                            s_leftAt = now;
                            s_masterId = 0;
                        }
                        else
                        {
                            LOG("AutoAttack: speaking to the craftsman {:x} (try {})", best->id, s_tries);
                            s_clickAt = now;
                            attack(best->id);
                        }
                    }
                    MapMemory::setRoute(true, best->x, best->y);
                    g_roamAt = 0;
                    return;
                }
            }
        }
        // Held by the game: talking or trading with an NPC (the hero's +0xFC 0xA, the NPC at +0x100; Manolito, block
        // M): no walk that would break the talk; a minute at most (a talk the agent left open).
        {
            static DWORD s_talkSince = 0;
            const uint8_t mode = *(reinterpret_cast<const uint8_t*>(self) + 0xFC);
            if (mode == 0xA)
            {
                if (!s_talkSince)
                {
                    s_talkSince = now;
                    LOG("AutoAttack: the hero talks or trades (NPC {:x}): standing", *reinterpret_cast<const uint32_t*>(
                                                                                   reinterpret_cast<const uint8_t*>(self) + 0x100));
                }
                if (now - s_talkSince < 60000)
                {
                    return;
                }
            }
            else
            {
                s_talkSince = 0;
            }
        }
        // Quests: off to the quest's target (however far: ClickWalk routes it over the map memory), fighting only
        // what attacks on the way; there, the roaming looks around it.
        int32_t qx = 0, qy = 0;
        double qr = 0.0;
        uint32_t who = 0;
        g_questTravel = false;
        bool questHere = false;
        Whereabouts::update(layer, static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize));
        // A position watch of its own (the solver, case A7, 2026-11-12 06:52: 190 «going to look» on one spot 8 tiles
        // from the quest's goal, the Dwarf boxed in by a bench and a fence): every quest return zeroes g_roamAt, so the
        // roam's own progress test never ran. 25 s per step on one spot (3 tiles), no dialog and no collect: the walk
        // cancelled, the book's goal parked 3 min per step, a walk back along the trail to a point 8+ tiles off.
        {
            static int32_t s_px = 0, s_py = 0;
            static DWORD s_since = 0;
            static int s_step = 0;
            // Busy (collecting, talking, at a shop or a craftsman): the clock starts again (the solver, 2026-11-12: 2 of 8
            // watch trips came right after a collection, the time spent picking up counted as standing still).
            const bool busy = UiNav::npcDialogOpen() || g_collecting || Gear::shopOpen() || Gear::craftsmanOpen() ||
                              ClickWalk::planning();
            if (!s_since || busy ||
                std::hypot(static_cast<double>(self->x - s_px), static_cast<double>(self->y - s_py)) > 3.0 * kTileSize)
            {
                s_px = self->x;
                s_py = self->y;
                s_since = now;
                s_step = 0;
            }
            // Inside a house the rooms are 3 tiles across: 90 s there, not 25, before it is taken for a jam (A1,
            // 16:17:01: «no progress for 25 s» three seconds after going in, the goal left and a walk out).
            else if (now - s_since > (layer != 0 ? 90000u : 25000u) * static_cast<DWORD>(s_step + 1))
            {
                ++s_step;
                LOG("AutoAttack: no progress for {} s on this spot (step {}): the goal left {} min, a walk out [intent {}, "
                    "routing {}, mounted {}, fighting {}]",
                    (now - s_since) / 1000, s_step, 3 * s_step, static_cast<int>(g_intent), ClickWalk::routing(),
                    *reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(self) + 0x1EC) != 0,
                    CombatState::action(self) == CombatState::Fighting);
                Findings::note("stuck", self->x, self->y, "no progress for {} s (step {})", (now - s_since) / 1000, s_step);
                ClickWalk::cancel();
                if (!g_questBook.empty() &&
                    std::hypot(static_cast<double>(g_questBook.front().x - self->x),
                               static_cast<double>(g_questBook.front().y - self->y)) > 300.0 * kTileSize)
                {
                    g_farFails = g_farFailAt && now - g_farFailAt < 600000 ? g_farFails + 1 : 1;
                    g_farFailAt = now;
                }
                // A jam within 30 tiles of the last one in 10 min is the place's, not the goal's: the goal followed is
                // kept and the walk out and the stuck guard see to the place (the coordinator, 2026-11-17: A3 at
                // 2972,2205 gave up 501, 203 and 402 in turn on the one spot, 25 s each, and would have skipped all three
                // by the 3 give-ups rule). A jam somewhere new parks the goal as before (its way may be the fault).
                static DWORD s_lastJamAt = 0;
                static int32_t s_lastJamX = 0, s_lastJamY = 0;
                const bool samePlace = s_lastJamAt && now - s_lastJamAt < 600000 &&
                                       std::hypot(static_cast<double>(self->x - s_lastJamX),
                                                  static_cast<double>(self->y - s_lastJamY)) < 30.0 * kTileSize;
                s_lastJamAt = now;
                s_lastJamX = self->x;
                s_lastJamY = self->y;
                if (!g_questBook.empty() && !samePlace)
                {
                    // The goal walked to: one on the way if so (the order's goal is not the one jammed for)
                    const int32_t gx = g_detouring ? g_detourX : g_questBook.front().x;
                    const int32_t gy = g_detouring ? g_detourY : g_questBook.front().y;
                    g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(gx / kTileSize)) << 32) |
                                    static_cast<uint32_t>(gy / kTileSize)] = now + 180000u * static_cast<DWORD>(s_step);
                }
                else if (samePlace)
                {
                    LOG("AutoAttack: the jam is the place's (another within 30 tiles lately): the goal kept, a walk out");
                }
                for (auto it = g_trail.rbegin(); it != g_trail.rend(); ++it)
                {
                    if (it->layer == layer &&
                        std::hypot(static_cast<double>(it->x - self->x), static_cast<double>(it->y - self->y)) > 8.0 * kTileSize)
                    {
                        ClickWalk::walkTo(it->x, it->y, false);
                        break;
                    }
                }
                s_since = now;
                g_roamAt = 0;
                return;
            }
        }
        // On another layer (a house's floor, a cellar) only a goal near at hand: the journal's tiles are the
        // overworld's, but seen live (2026-11-09) the Vampiress starts in her house on layer 2 with the main quest 3
        // tiles off, and left it alone (no quest off layer 0) to roam against the walls for 20 minutes.
        const int heroLevel = *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x3FE);
        // A quest whose ground is more than 2 levels above the hero: farming first, where the enemies fit, until the
        // hero has the levels (the player: «si pretende farmear, el foco no es ir a la quest»).
        auto questTooHard = [&](int32_t x, int32_t y) {
            // Where the hero died lately, the goal waits too, however near (the analyst, 2026-11-11: A3, a level 4
            // Battle Mage, loaded beside an archers' camp at 3148,2722 on its quest's way and died there 5 times in
            // 32 min, out of potions each time): farming elsewhere first, as long as the place stays shunned (30 min
            // after one death, longer after more).
            // Held 2 min once decided (the solver, 2026-11-12: A5 flipped farm/quest 19 times, A2 6, as the hero walked
            // in and out of the shunned place's edge).
            static DWORD s_shunUntil = 0;
            const DWORD tick = GetTickCount();
            if (static_cast<int>(tick - s_shunUntil) < 0 ||
                nearDeathSpot(static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize)) ||
                // The hero's own place: a fight lost only (one loaded beside the place it stuck in is to leave it).
                AgentSave::nearDeathSpot(static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize),
                                         false) ||
                nearDangerGroup(static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize)))
            {
                if (static_cast<int>(tick - s_shunUntil) >= 0)
                {
                    s_shunUntil = tick + 120000;
                }
                setIntent(Intent::Farm, "the quest's way is where the hero died lately: farming elsewhere first");
                return true;
            }
            // Two far walks in 10 min that got nowhere (the stuck solver, 2026-11-16: A4 26 min and not one fight, its
            // goals 566, 649, 652 and 699 tiles out in turn, each left after 25 s on the same spot): the experience
            // first, near; the far goals are tried again after the 10 min.
            // (Not while the quests come first, the owner 2026-11-17: farming only for the next quest's level or for
            // safety; a far goal that gets nowhere is skipped by the quest order instead.)
            if (false && g_farFails >= 2 && g_farFailAt && tick - g_farFailAt < 600000 &&
                std::hypot(static_cast<double>(x - self->x), static_cast<double>(y - self->y)) > 300.0 * kTileSize)
            {
                setIntent(Intent::Farm, "far goals got nowhere twice lately: farming near first");
                return true;
            }
            if (nearHopelessSpot(static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize), tick))
            {
                setIntent(Intent::Farm, "the quest's goal is by a fight given up as hopeless lately: farming elsewhere first");
                return true;
            }
            // Outmatched lately (two hopeless fights in 10 min): every quest but one at hand waits while the hero farms
            // where it can win (A3 2026-11-12: a quest of a 1-4 region still taken, its way by an archers' camp,
            // 4 deaths in 20 min there).
            // For 20 min at most at a time (the stuck solver, 2026-11-17, A1, a Seraphim of level 27: 117 «hopeless fights» in 2 h,
            // 110 of them under 90 % of its health in packs of 4-9, the farming that the hold sends it to being where they
            // are, so two in any 10 min for good; the five givers of quests 23-24 it was to go for 400-900 tiles off were held
            // 13 h): after 20 min held with five healing potions or more, one try of 15 min, the retreats going on as ever;
            // the hold is back at its end.
            static DWORD s_heldSince = 0, s_tryUntil = 0;
            if (outmatched(tick) &&
                std::hypot(static_cast<double>(x - self->x), static_cast<double>(y - self->y)) > 15.0 * kTileSize)
            {
                bool held = true;
                if (s_tryUntil && static_cast<int>(tick - s_tryUntil) < 0)
                {
                    held = false;
                }
                else
                {
                    s_heldSince = s_heldSince ? s_heldSince : tick;
                    if (tick - s_heldSince > 1200000 && Gear::healingLeft() >= 5)
                    {
                        s_tryUntil = tick + 900000;
                        s_heldSince = 0;
                        held = false;
                        LOG("AutoAttack: outmatched for 20 min with {} potions: the quests are tried for 15 min", Gear::healingLeft());
                    }
                }
                if (held)
                {
                    setIntent(Intent::Farm, "outmatched here: farming where the enemies are not above the hero first");
                    return true;
                }
            }
            else
            {
                s_heldSince = 0;    // not outmatched (or the goal at hand): the 20 min begin anew at the next episode
            }
            // A goal at hand is no trip into hard ground: the Daemon's start (a tutorial yard, region 59 marked
            // levels 45-80, its main quest 8 tiles off behind a script's blocker) farmed instead, shut in, 14 min.
            if (std::hypot(static_cast<double>(x - self->x), static_cast<double>(y - self->y)) < 60.0 * kTileSize)
            {
                return false;
            }
            const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40);
            const uint8_t* world = holder ? *reinterpret_cast<const uint8_t* const*>(holder) : nullptr;
            int lo = 0, hi = 0;
            if (!world || !sectorLevels(world, static_cast<int>(x / kTileSize), static_cast<int>(y / kTileSize), lo, hi) ||
                lo <= heroLevel + Mind::now().questLevelSlack)
            {
                return false;
            }
            setIntent(Intent::Farm, std::format("the quest's ground is levels {}-{}, the hero {}: farming first", lo, hi,
                                                heroLevel));
            return true;
        };
        // A quest with its time running: never failed for a detour (the player, 2026-11-11: «prohíbe al agente
        // fracasar misiones, el fracaso cuenta como muerte»): no farming pause, no «farming first» for its ground.
        // Only a time running short (under a game day) counts (the coordinator, 2026-11-12: A3's side quest 152 with
        // 3952 game min left let every quest of the book past «farming first» and the outmatched hold, and the Battle
        // Mage at level 4 walked on to the archers' camp and died there 3 times in 17 min).
        const bool deadline = std::any_of(g_questBook.begin(), g_questBook.end(),
                                          [](const QuestGoal& g) { return g.minutesLeft > 0 && g.minutesLeft <= 1440; });
        if (deadline && g_questPauseUntil)
        {
            g_questPauseUntil = 0;
            LOG("AutoAttack: a quest's time is running: the farming pause dropped");
        }
        // Neither a fight nor a quest done in 8 min while seeing to quests (the analyst, 2026-11-11: A5 «looking around»
        // its goals with 16 under way, 3 fights in 19 min, 8 of 9 half hours under 1600 experience): farming 10 min
        // first, a player gains levels before going on.
        // (Off: farming only for the next quest's level or for safety, the owner 2026-11-17; a quest that gets nowhere
        // is skipped by the quest order.)
        if (false && !deadline && g_intent == Intent::Quest && g_farmKnown && Config::autoAttack.farm && g_lastTargetAt &&
            now - g_lastTargetAt > 480000 && (!g_questsDoneAt || now - g_questsDoneAt > 480000) &&
            (!g_questPauseUntil || static_cast<int>(now - g_questPauseUntil) >= 0))
        {
            g_questPauseUntil = now + 600000;
            LOG("AutoAttack: 8 min with neither a fight nor a quest done: the quests left 10 min, farming");
        }
        if (Config::autoAttack.quests && !(g_questPauseUntil && static_cast<int>(now - g_questPauseUntil) < 0) &&
            !(g_questNoWayUntil && static_cast<int>(now - g_questNoWayUntil) < 0) &&
            questTarget(self->x, self->y, qx, qy, qr, who) &&
            (layer == 0 || std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y)) < 60.0 * kTileSize) &&
            !(!deadline && Config::autoAttack.farm && g_farmKnown && questTooHard(qx, qy)))
        {
            questHere = true;
            setIntent(Intent::Quest, who && who != 0xFFFFFFFFu ? "a quest creature to speak to" : "a quest's goal");
            orderFollowTick(now);
            // A kill quest whose goal is a cave's mouth, the hero inside that cave: the goal is the cave itself, its
            // reachable tile nearest the box's centre (A5, 2026-11-17 21:48-21:50 under 2f614be9: quest 502, the
            // thieves' lair, goal 2004,3627 at cave 5.2's door; inside, the walk to the goal went out by the net's door
            // and, outside, the goal tile was the way back in: in and out every 4 s for 2 min, the quest skipped).
            if (layer == 0 && Lore::questKind() == Lore::QuestKind::Kill)
            {
                const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
                const int gtx = static_cast<int>(qx / kTileSize), gty = static_cast<int>(qy / kTileSize);
                int cx = 0, cy = 0, nx = htx, ny = hty;
                if (RouteNet::insideAtDoor(htx, hty, gtx, gty, &cx, &cy))
                {
                    if (!Whereabouts::nearestReachable(cx, cy, nx, ny))
                    {
                        nx = htx;
                        ny = hty;
                    }
                    static uint64_t s_toldCave = 0;
                    const uint64_t ck = (static_cast<uint64_t>(static_cast<uint32_t>(gtx)) << 32) | static_cast<uint32_t>(gty);
                    if (ck != s_toldCave)
                    {
                        s_toldCave = ck;
                        LOG("AutoAttack: inside the cave whose door is the kill quest's goal {},{}: the fights sought "
                            "inside, from {},{}",
                            gtx, gty, nx, ny);
                    }
                    qx = static_cast<int32_t>((nx + 0.5) * kTileSize);
                    qy = static_cast<int32_t>((ny + 0.5) * kTileSize);
                }
            }
            // A goal inside a house or cave: its interior lies far off on the map (HQ_HE_3_3_1's at 5859..5863,
            // 3851..3886, its doors 3433,2697 and 3436,2735; Manolito): the hero outside goes to the door whose inside
            // landing is nearest the goal, and steps on it (the game's own jump), not to the goal's tile.
            static DWORD s_onDoorSince = 0;
            if (layer == 0)
            {
                const int gtx = static_cast<int>(qx / kTileSize), gty = static_cast<int>(qy / kTileSize);
                const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
                const Teleports::Interior* door = nullptr;
                double bestIn = 40.0;
                for (const Teleports::Interior& in : Teleports::interiors())
                {
                    // Only a door nearer than the goal itself (a house's inside placed far off on the map): one 2893
                    // tiles off for a goal 37 tiles away swapped with it every second (the player saw it looping,
                    // 2026-11-10: «quiere abrir puertas a km de distancia»).
                    // The goal inside the interior this door lands in (the net's box of it, by the world files): that
                    // door, however far the goal from the landing (A5, 2026-11-17: quest 701's goal 4101,624, 74 tiles
                    // from cave 17.2's landing 4037,662; at 40 the hero stood at the door, 3176,1930, and never went in).
                    const bool inBox = RouteNet::insideOf(in.inX, in.inY, gtx, gty) && !RouteNet::insideOf(in.inX, in.inY, htx, hty);
                    const double d = inBox ? 0.0 : std::hypot(in.inX - gtx, in.inY - gty);
                    const double toDoor = std::hypot(in.outX - htx, in.outY - hty);
                    const double toGoal = std::hypot(gtx - htx, gty - hty);
                    if (d < bestIn && (inBox || std::hypot(in.inX - htx, in.inY - hty) > 60.0) && toDoor < toGoal * 0.8 &&
                        toDoor < 300.0)
                    {
                        bestIn = d;
                        door = &in;
                    }
                }
                if (door)
                {
                    int dx = door->outX, dy = door->outY;
                    if (!door->start)
                    {
                        // A cave's script zone beside the landing first, then the stairs anchor (A5, 2026-11-17 21:04:
                        // cave 5.1's landing 2000,3434, the anchor 2000,3436 stood on 30 s with no jump, «hemmed in»,
                        // quest 501 left; cave 5.2 went in at once from its zone, 2004,3627).
                        RouteNet::doorStep(0, door->outX, door->outY, htx, hty, dx, dy);
                    }
                    static int s_doorToldX = -1;
                    if (s_doorToldX != dx)
                    {
                        s_doorToldX = dx;
                        LOG("AutoAttack: the quest's goal {},{} lies inside (its landing {},{}): to its door at {},{}", gtx,
                            gty, door->inX, door->inY, dx, dy);
                    }
                    setIntent(Intent::Quest, "the quest's goal inside a house: to its door");
                    noteDoor(dx, dy);
                    qx = static_cast<int32_t>((dx + 0.5) * kTileSize);
                    qy = static_cast<int32_t>((dy + 0.5) * kTileSize);
                    qr = 0.0;
                    if (std::hypot(dx - htx, dy - hty) <= 1.0)
                    {
                        // On it and nothing yet: a step off, the next look steps on again.
                        if (!s_onDoorSince)
                        {
                            s_onDoorSince = now;
                        }
                        else if (now - s_onDoorSince > 4000)
                        {
                            s_onDoorSince = 0;
                            ClickWalk::walkTo(self->x + static_cast<int32_t>(2 * kTileSize), self->y, false);
                            g_roamAt = 0;
                            return;
                        }
                    }
                    else
                    {
                        s_onDoorSince = 0;
                    }
                }
                else
                {
                    // A goal inside a house on this layer, shut in by its walls (the game's tile data): in by the
                    // door on the hero's side, not at the wall nearest the goal. Once at the door (or inside), the
                    // goal again: the door handling opens it on the way.
                    int dx = 0, dy = 0;
                    const bool indoors = std::hypot(gtx - htx, gty - hty) > 2.0 &&
                                         MapMemory::doorInto(layer, gtx, gty, htx, hty, dx, dy);
                    if (indoors && std::hypot(dx - htx, dy - hty) <= 1.5)
                    {
                        // At the door: used if shut (each 3 s), and through it, a tile on toward the goal (a house's
                        // inside is entered by stepping in; the walk to the goal's own tile, a wall, went nowhere).
                        static DWORD s_usedAt = 0;
                        if (now - s_usedAt > 3000)
                        {
                            s_usedAt = now;
                            doorNearGoal(now, static_cast<int32_t>((dx + 0.5) * kTileSize),
                                         static_cast<int32_t>((dy + 0.5) * kTileSize));
                        }
                        const double gl = std::max(1.0, std::hypot(gtx - dx, gty - dy));
                        const int ix = dx + static_cast<int>(std::lround((gtx - dx) / gl)),
                                  iy = dy + static_cast<int>(std::lround((gty - dy) / gl));
                        setIntent(Intent::Quest, "the goal indoors: in through the door");
                        // Interiors are entered on foot (the player, 2026-11-14: «el caballo no entra en interiores y
                        // el agente lo vive intentando»): off the horse from 12 tiles before the door, and not back up
                        // while the goal is inside.
                        if (hero && std::hypot(static_cast<double>(hero->x) / kTileSize - dx,
                                               static_cast<double>(hero->y) / kTileSize - dy) < 12.0)
                        {
                            g_onFootUntil = now + 30000;
                        }
                        noteDoor(dx, dy);
                        qx = static_cast<int32_t>((ix + 0.5) * kTileSize);
                        qy = static_cast<int32_t>((iy + 0.5) * kTileSize);
                        qr = 0.0;
                    }
                    else if (indoors)
                    {
                        static int s_inToldX = -1, s_inToldY = -1;
                        if (s_inToldX != dx || s_inToldY != dy)
                        {
                            s_inToldX = dx;
                            s_inToldY = dy;
                            LOG("AutoAttack: the goal {},{} lies indoors: in by the door at {},{}", gtx, gty, dx, dy);
                        }
                        setIntent(Intent::Quest, "the goal indoors: to the house's door");
                        // Interiors are entered on foot (the player, 2026-11-14: «el caballo no entra en interiores y
                        // el agente lo vive intentando»): off the horse from 12 tiles before the door, and not back up
                        // while the goal is inside.
                        if (hero && std::hypot(static_cast<double>(hero->x) / kTileSize - dx,
                                               static_cast<double>(hero->y) / kTileSize - dy) < 12.0)
                        {
                            g_onFootUntil = now + 30000;
                        }
                        noteDoor(dx, dy);
                        qx = static_cast<int32_t>((dx + 0.5) * kTileSize);
                        qy = static_cast<int32_t>((dy + 0.5) * kTileSize);
                        qr = 0.0;
                    }
                }
            }
            // A quest zone (a wide radius, e.g. the arena's 22 tiles) is reached on its edge too: its centre can be
            // a wall (seen live: the arena's 3786,330), so travel there fails while the hero already stands in it.
            // A creature to speak to that is not loaded yet: its spot is gone to (3 tiles), not the zone's edge (the
            // stuck solver, 2026-11-11: «hablar con X» goals ringed at 29-35 tiles from the journal's centre, 1450 of
            // 1586 «going to look», the creature at 3091,2783 never spoken to by any copy). Once loaded, the talk below.
            // Loaded within 60 tiles, the creature itself is the goal (the stuck solver's check at 21:15: 90 % of «going
            // to look» still in the 29-35 tile ring, the creatures loaded, so the zone's edge counted as there).
            // A fixed goal with someone under a quest sign beside it: he is the one to speak to (the Messenger,
            // R01NQ02: the journal gives a spot in the tavern, «the contact will reveal himself»: a creature with «!»
            // two steps off; A1 stood on the spot, looked around and walked out, 2026-11-13). Within 10 tiles of the
            // goal and of the hero, not spoken to lately.
            // From 25 tiles too for a sign on the goal itself (within 3 tiles of it): a goal that cannot be stood on is
            // «taken as there» from up to 22 tiles (the quests' session, 2026-11-16: The Merchant's Message DQ_10258,
            // A8 01:56:34 «3382,3300 cannot be stood on … (22 tiles): taken as there», the «!» creature 6fd on that
            // very tile, never spoken to by any copy).
            const double toSpot = std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y));
            if (who == 0xFFFFFFFFu && toSpot < 25.0 * kTileSize)
            {
                double nearest = toSpot < 10.0 * kTileSize ? 10.0 * kTileSize : 3.0 * kTileSize;
                for (const Sign& sign : g_signs)
                {
                    const double toGoal = std::hypot(static_cast<double>(sign.x - qx), static_cast<double>(sign.y - qy));
                    if (toGoal < nearest && !talkedLately(sign.id, now) && !isPlainHireling(sign.id))
                    {
                        nearest = toGoal;
                        who = sign.id;
                    }
                }
                if (who != 0xFFFFFFFFu)
                {
                    static uint32_t s_toldSign = 0;
                    if (s_toldSign != who)
                    {
                        s_toldSign = who;
                        LOG("AutoAttack: at the quest's spot {},{}: {:x} under a quest sign {:.0f} tiles from it: spoken to",
                            static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize), who, nearest / kTileSize);
                    }
                }
            }
            // A quest item named as the goal's «creature» is fetched, not spoken to: the walk keeps the way in by the
            // door (doorInto) and the collect takes it on the spot.
            const bool fetch = who && who != 0xFFFFFFFFu && objects && questThing(objects->object(who));
            const bool speakTo = who && who != 0xFFFFFFFFu && !fetch;
            const cObject* speaker = speakTo && objects ? objects->object(who) : nullptr;
            // Loaded within 60 tiles the creature is the goal and stays so until 90 (the stuck solver, 2026-11-16: A8
            // at 60 tiles on one axis, the goal flipped between the creature's tile 2916,3290 and the journal's
            // 2907,3295 100 times in 14 min, each flip a new route and the progress watches back to zero).
            static uint32_t s_speakerGoal = 0;
            const double speakerFar = speaker ? std::max(std::abs(static_cast<double>(speaker->x - self->x)),
                                                         std::abs(static_cast<double>(speaker->y - self->y)))
                                              : 1e18;
            if (speaker && speakerFar < (s_speakerGoal == who ? 90.0 : 60.0) * kTileSize)
            {
                s_speakerGoal = who;
                qx = speaker->x;
                qy = speaker->y;
            }
            else if (s_speakerGoal == who && speakerFar >= 90.0 * kTileSize)
            {
                s_speakerGoal = 0;
            }
            // A fixed goal is gone to at the standable tile nearest it, not its centre (the stuck solver, 2026-11-11:
            // 3174,2794 lies inside a house's solid block, its yard 3 tiles off; walks to the blocked centre stopped
            // 32-38 tiles out, A7 and A8 for hours), and reached within 2 tiles of it. The zone's wide edge only shut
            // in (the arena behind its gate).
            bool fixedGoal = false;
            // On the surface only: inside a house the tile test does not know the floor, the one tile it calls
            // reachable is the way in itself, and the hero walked back onto it and out (the player, 2026-11-13: «llegan
            // a entrar pero salen al momento»; A7 in and out 69 times in half an hour, 2 s inside each).
            const int32_t askedX = qx, askedY = qy;     // the goal as the journal gives it, before the reachable tile
            // Only a goal within the box the reachable test covers (64 tiles about the hero): for one beyond it the
            // nearest reachable tile is a spot on the box's edge that leads nowhere, and the goal crept along with the
            // hero (the quests' session, 2026-11-16: A8's 10258 at 529 tiles became «off to the quest at tile
            // 2877,3230 (25 tiles)»; A2's 1103 at 454 tiles became 1797,2339 at 67; «no way» to those, the quest left).
            if (!speakTo && !Whereabouts::area().shutIn && layer == 0 &&
                Whereabouts::reachable(static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize)) != -1)
            {
                int nx = 0, ny = 0;
                if (Whereabouts::nearestReachable(static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize), nx, ny))
                {
                    qx = static_cast<int32_t>((nx + 0.5) * kTileSize);
                    qy = static_cast<int32_t>((ny + 0.5) * kTileSize);
                    fixedGoal = true;
                }
            }
            const double qd = std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y));
            const bool zone = qr >= 8.0 * kTileSize && !speakTo && !fixedGoal;
            // How near counts as there. A creature to speak to: 6 tiles, the click on it does the rest (the stuck
            // solver, 2026-11-13: a merchant behind his counter 3 tiles off, the hero sent to his tile every 0.7 s for
            // 30 s; goals inside houses in 15004, 9005, 152). A fixed goal: 2 tiles to arrive, then 25 for 4 min, so the
            // look around it reaches what the quest wants (Wolf's Eyes' boss in the clearing beside the goal, the bear
            // by the graveyard: the hero was called back each time it stepped 2 tiles off, «going to look (1 tiles
            // from where it began)» for hours).
            static uint64_t s_arrivedKey = 0;
            static DWORD s_arrivedAt = 0;
            const uint64_t goalKey = (static_cast<uint64_t>(static_cast<uint32_t>(qx / kTileSize)) << 32) |
                                     static_cast<uint32_t>(qy / kTileSize);
            double there = zone ? qr + 10.0 * kTileSize
                                // Inside a house or cave (another layer) from 15 tiles: the room is small, and the
                                // walk to the creature's tile led back out by the door (A1 2026-11-13, the Messenger's
                                // contact 6 tiles off inside: in, a walk, out, in again every 10 s for an hour).
                                // The creature on another layer than the hero (a giver inside a house, the hero in the
                                // street): 15 tiles too, the click on it takes the hero in by the game's own path through
                                // the door (A3, 2026-11-24: 15052's giver behind a wall at 7 tiles, «there» at 6, walked
                                // to 7 tiles every 4 s and never clicked, the offer gone to 3 times).
                                : speakTo ? (layer != 0 || (speaker && *(reinterpret_cast<const uint8_t*>(speaker) + 0x24) !=
                                                                           static_cast<uint8_t>(layer))
                                                 ? 15.0
                                                 : 6.0) * kTileSize
                                          : fixedGoal ? std::min(qr, 2.0 * kTileSize) : qr;
            // Inside a house (a layer other than the surface) the goal is walked up to, 1.5 tiles: «there» by the
            // journal's wide radius, the hero looked around from the doorway and the first step of the look took him
            // out (A7, 18:12: in at 3171,2796, «going to look», out at 3175,2800 one second on, 25 times).
            if (layer != 0 && !speakTo)
            {
                there = 1.5 * kTileSize;
            }
            else if (!speakTo && !zone)
            {
                if (qd <= there && (s_arrivedKey != goalKey || now - s_arrivedAt > 600000))
                {
                    s_arrivedKey = goalKey;
                    s_arrivedAt = now;
                }
                if (s_arrivedKey == goalKey && now - s_arrivedAt < 240000)
                {
                    there = std::max(there, 25.0 * kTileSize);
                }
            }
            // The goal itself cannot be stood on (the nearest reachable tile is 3+ tiles from it) and the hero is
            // already within the journal's radius of it: there (the stuck solver, 2026-11-14: A3 and A7 at 3046,2892,
            // a thicket and a camp, «no nearer … no way found» 3-10 tiles off for hours).
            if (fixedGoal && layer == 0 && qr > 0.0 &&
                std::hypot(static_cast<double>(qx - askedX), static_cast<double>(qy - askedY)) >= 3.0 * kTileSize &&
                std::hypot(static_cast<double>(self->x - askedX), static_cast<double>(self->y - askedY)) <= qr)
            {
                static uint64_t s_toldKey = 0;
                if (goalKey != s_toldKey)
                {
                    s_toldKey = goalKey;
                    LOG("AutoAttack: the goal {},{} cannot be stood on (nearest reachable {},{}), the hero within the "
                        "journal's radius ({:.0f} tiles): taken as there",
                        static_cast<int>(askedX / kTileSize), static_cast<int>(askedY / kTileSize),
                        static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize), qr / kTileSize);
                }
                there = std::max(there, qd);
            }
            if (qd > there)
            {
                g_questTravel = true;
                if (qx != g_questX || qy != g_questY)
                {
                    LOG("AutoAttack: off to the quest at tile {},{} ({:.0f} tiles)", static_cast<int>(qx / kTileSize),
                        static_cast<int>(qy / kTileSize),
                        std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y)) / kTileSize);
                    g_questX = qx;
                    g_questY = qy;
                }
                // An escort (read from the quest's objective): the one escorted walks slower; the hero goes in
                // stretches of 5 s and waits 2.5 s for them.
                static DWORD s_escortWalkSince = 0, s_escortWaitUntil = 0;
                if (Lore::questKind() == Lore::QuestKind::Escort)
                {
                    // An escort is walked, never ridden (the web researcher, 2026-11-13, CobaltBlu's guide: Adelina,
                    // 210 health and no fight in her, is set upon at once when her horse is mounted; the one escorted
                    // walks anyway).
                    g_onFootUntil = now + 15000;
                    if (s_escortWaitUntil && static_cast<int>(now - s_escortWaitUntil) < 0)
                    {
                        MapMemory::setRoute(true, qx, qy);
                        g_roamAt = 0;
                        return;
                    }
                    s_escortWaitUntil = 0;
                    if (!s_escortWalkSince || now - s_escortWalkSince > 15000)
                    {
                        s_escortWalkSince = now;
                    }
                    else if (now - s_escortWalkSince > 5000)
                    {
                        ClickWalk::cancel();
                        s_escortWaitUntil = now + 2500;
                        s_escortWalkSince = 0;
                        return;
                    }
                }
                // Shut in (a closed yard, the arena behind its portcullis) with the target outside: no travel, which
                // only shuffles; the reachable tile nearest the target (by the gate, where a script may open the
                // way), and the rest of the agent's play inside (chests, fights) from there.
                bool waitShut = false;
                // Not inside a house with the goal at hand (within 20 tiles on a layer other than the surface): there
                // the goal is in the room, and the «way out» is the door the hero came in by.
                const bool goalInRoom = layer != 0 && std::hypot(static_cast<double>(qx - self->x),
                                                                 static_cast<double>(qy - self->y)) <= 20.0 * kTileSize;
                if (const Whereabouts::Area& where = Whereabouts::area(); where.shutIn && !goalInRoom)
                {
                    const int gtx = static_cast<int>(qx / kTileSize), gty = static_cast<int>(qy / kTileSize);
                    int nx = 0, ny = 0;
                    // The goal inside the very pocket the hero is shut in (within 4 tiles of its reachable ground):
                    // not outside, nothing to get out for (the quests' session, 2026-11-16: the Tree of Life's inside,
                    // R08NQ01, is a pocket of the surface at 5064..5096 x 344..370; A3 got in at 19:06:01 with the
                    // goal 5087,358 inside it and was led out by the way it came 18 s later, «the quest outside»).
                    // Or both in one interior by the net's box of it (A5, 2026-11-17 21:20:38: in cave 5.1 at 5064,366,
                    // the goal 5087,358 in a house inside it behind a shut door, the nearest reachable tile over 4
                    // off, and the hero led out by the door it had come in by 1 s before).
                    const int hx = static_cast<int>(self->x / kTileSize), hy = static_cast<int>(self->y / kTileSize);
                    const bool goalInPocket = (Whereabouts::reachable(gtx, gty) != 1 &&
                                               Whereabouts::nearestReachable(gtx, gty, nx, ny) &&
                                               std::max(std::abs(nx - gtx), std::abs(ny - gty)) <= 4) ||
                                              (layer == 0 && (RouteNet::sameInterior(hx, hy, gtx, gty) ||
                                                              (Lore::questKind() == Lore::QuestKind::Kill &&
                                                               RouteNet::insideAtDoor(hx, hy, gtx, gty))));
                    if (goalInPocket)
                    {
                        static uint64_t s_toldPocket = 0;
                        const uint64_t pk = (static_cast<uint64_t>(static_cast<uint32_t>(gtx)) << 32) | static_cast<uint32_t>(gty);
                        if (pk != s_toldPocket)
                        {
                            s_toldPocket = pk;
                            LOG("AutoAttack: shut in with the goal {},{} inside the same pocket (its nearest reachable tile "
                                "{},{}): staying in",
                                gtx, gty, nx, ny);
                        }
                    }
                    if (!goalInPocket && Whereabouts::reachable(gtx, gty) != 1 &&
                        Whereabouts::nearestReachable(gtx, gty, nx, ny))
                    {
                        waitShut = true;
                        // A way out found before (a portal end, a door or stairs: MapMemory saw the hero jump there)
                        // within reach: stepped on, each tried once in 2 min; the Gladiator's coliseum is left by
                        // its teleport tiles (tpstart_g_03/04 -> 3293,2717, Manolito), not by a path.
                        static std::unordered_map<uint64_t, DWORD> s_triedWayOut;
                        const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
                        size_t gameWays = 0;
                        const std::vector<std::pair<int, int>> wayList = waysOutAround(layer, htx, hty, &gameWays);
                        for (size_t wi = 0; wi < wayList.size(); ++wi)
                        {
                            const int ex = wayList[wi].first, ey = wayList[wi].second;
                            const uint64_t wk = (static_cast<uint64_t>(static_cast<uint32_t>(ex)) << 32) | static_cast<uint32_t>(ey);
                            if (const auto t = s_triedWayOut.find(wk); t != s_triedWayOut.end() && now - t->second < 120000)
                            {
                                continue;
                            }
                            // The game's own ways out (a teleport pad: the stuck guard walks to them without this test)
                            // are taken as reachable; the stuck solver, 2026-11-14: A3 in the cave 2.3 never logged «trying
                            // the way out» in 2 h and sat at the nearest tile to the quest, 40 tiles from the pad.
                            bool reach = wi < gameWays;
                            for (int dy = -1; dy <= 1 && !reach; ++dy)
                            {
                                for (int dx = -1; dx <= 1 && !reach; ++dx)
                                {
                                    reach = Whereabouts::reachable(ex + dx, ey + dy) == 1;
                                }
                            }
                            if (!reach)
                            {
                                static uint64_t s_toldSkip = 0;
                                if (wk != s_toldSkip)
                                {
                                    s_toldSkip = wk;
                                    LOG("AutoAttack: shut in: the way out at {},{} is not on reachable ground: skipped", ex, ey);
                                }
                                continue;
                            }
                            // The game's triggers fire on stepping INTO their tile, never on standing on it (Manolito,
                            // block BZ: 0x6230C0 from the move tick 0x5941A0 only when the creature's tile changes; the
                            // cave 16.1's exit is the one tile 5741,1422). So a hero beside it steps in (A4, 2026-11-24:
                            // at 5741,1423 it was taken as «on it» and left untried), and a hero on it steps off to a
                            // reachable neighbour and back in; only after that is it left for 2 min.
                            static std::unordered_map<uint64_t, DWORD> s_steppedOff;
                            if (ex == htx && ey == hty)
                            {
                                if (const auto s = s_steppedOff.find(wk); s != s_steppedOff.end() && now - s->second < 120000)
                                {
                                    // The step off still under way (A4 2026-11-24: taken as done 150 ms after it went out).
                                    if (now - s->second < 8000)
                                    {
                                        g_roamAt = 0;
                                        return;
                                    }
                                    LOG("AutoAttack: on the way out at {},{}: stepped off and in, no jump yet, left 2 min",
                                        ex, ey);
                                    s_triedWayOut[wk] = now;
                                    continue;
                                }
                                int ox = 0, oy = 0;
                                bool off = false;
                                for (int dy = -1; dy <= 1 && !off; ++dy)
                                {
                                    for (int dx = -1; dx <= 1 && !off; ++dx)
                                    {
                                        if ((dx || dy) && Whereabouts::reachable(ex + dx, ey + dy) == 1)
                                        {
                                            ox = ex + dx;
                                            oy = ey + dy;
                                            off = true;
                                        }
                                    }
                                }
                                s_steppedOff[wk] = now;
                                if (off)
                                {
                                    LOG("AutoAttack: on the way out at {},{}: a step off to {},{} to step in again", ex, ey,
                                        ox, oy);
                                    g_questTravel = false;
                                    g_questAskAt = now;
                                    ClickWalk::walkTo(static_cast<int32_t>((ox + 0.5) * kTileSize),
                                                      static_cast<int32_t>((oy + 0.5) * kTileSize), false);
                                    g_roamAt = 0;
                                    return;
                                }
                                s_triedWayOut[wk] = now;
                                continue;
                            }
                            const int32_t ewx = static_cast<int32_t>((ex + 0.5) * kTileSize);
                            const int32_t ewy = static_cast<int32_t>((ey + 0.5) * kTileSize);
                            // The game's own ways out are not parked (the stuck solver, 2026-11-16: the cave 5.2's
                            // pad cell 5370,336 parked 60 min on A5 and shared with the other seven copies, so the roam
                            // skipped it silently and only the stuck guard, every 3 min, tried it).
                            if (wi >= gameWays &&
                                approachStalled(ewx, ewy,
                                                std::hypot(static_cast<double>(ewx - self->x), static_cast<double>(ewy - self->y)),
                                                now))
                            {
                                s_triedWayOut[wk] = now;
                                continue;
                            }
                            static uint64_t toldWay = 0;
                            if (wk != toldWay)
                            {
                                toldWay = wk;
                                LOG("AutoAttack: shut in, the quest outside: trying the way out found at {},{}", ex, ey);
                            }
                            g_questTravel = false;
                            if (!ClickWalk::routing() && now - g_questAskAt > 4000)
                            {
                                g_questAskAt = now;
                                int32_t ax = 0, ay = 0;
                                aimThrough(htx, hty, ex, ey, ax, ay);
                                ClickWalk::walkTo(ax, ay, false);
                            }
                            MapMemory::setRoute(true, static_cast<int32_t>((ex + 0.5) * kTileSize),
                                                static_cast<int32_t>((ey + 0.5) * kTileSize));
                            g_roamAt = 0;
                            return;
                        }
                        static uint64_t toldShut = 0;
                        const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(gtx)) << 32) | static_cast<uint32_t>(gty);
                        if (key != toldShut)
                        {
                            toldShut = key;
                            LOG("AutoAttack: shut in ({} tiles) and the quest's target {},{} lies outside: to {},{}, the "
                                "nearest reachable tile, waiting for the way out",
                                where.tiles, gtx, gty, nx, ny);
                        }
                        const int32_t wx = static_cast<int32_t>((nx + 0.5) * kTileSize);
                        const int32_t wy = static_cast<int32_t>((ny + 0.5) * kTileSize);
                        // A chest near holds the walk to the quest's centre only for its first minute (the stuck solver,
                        // 2026-11-11: chests already failed kept the hero ringing the zone's edge, 94 % of «going to look»).
                        const bool chestNear = g_chestId && g_chestBest < 40.0 * kTileSize &&
                                               (g_chestHeading != g_chestId || now - g_chestSince < 60000);
                        const double wd = std::hypot(static_cast<double>(wx - self->x), static_cast<double>(wy - self->y));
                        if (!chestNear && wd > 0.6 * kTileSize && !approachStalled(wx, wy, wd, now))
                        {
                            g_questTravel = false;
                            if (!ClickWalk::routing() && now - g_questAskAt > 4000)
                            {
                                g_questAskAt = now;
                                ClickWalk::walkTo(wx, wy, false);
                            }
                            MapMemory::setRoute(true, wx, wy);
                            g_roamAt = 0;
                            return;
                        }
                        g_homeX = wx;       // there: chests and fights inside meanwhile, roaming from here
                        g_homeY = wy;
                    }
                }
                if (!waitShut && travel(now, self, qx, qy, g_questAskAt))
                {
                    MapMemory::setRoute(true, qx, qy);
                    g_roamAt = 0;
                    return;
                }
                g_questTravel = false;     // no way there for now: the rest of the agent's play meanwhile
                questHere = false;
                // Held 30 s (A2 2026-11-12: the quest chosen again the next frame, quest/farm flipped every 150 ms
                // for minutes, then the 4502AE crash): the farming goes on meanwhile.
                g_questNoWayUntil = now + 30000;
                // The same goal with no way three times in 10 min is left 20 min (the analyst, 2026-11-13: A3 between
                // «quest» to 3259,2889 and «farm» every 30 s for an hour, 44 experience an hour: 30 s is not enough
                // to reach the farming zone, and the same goal was chosen again).
                {
                    static uint64_t s_noWayKey = 0;
                    static int s_noWayTimes = 0;
                    static DWORD s_noWayFirst = 0;
                    const QuestGoal* front = g_questBook.empty() ? nullptr : &goalWalked();
                    const int32_t gx = front ? front->x : qx, gy = front ? front->y : qy;
                    const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(gx / kTileSize)) << 32) |
                                         static_cast<uint32_t>(gy / kTileSize);
                    if (key != s_noWayKey || now - s_noWayFirst > 600000)
                    {
                        s_noWayKey = key;
                        s_noWayTimes = 1;
                        s_noWayFirst = now;
                    }
                    else if (++s_noWayTimes >= 3 && entranceNearGoal(now, self, gx, gy))
                    {
                        // A way in near it (a house's stairs mark): that first (A2 left the Messenger's goal
                        // 3174,2794 20 min with the mark at 3171,2797 never tried).
                        s_noWayTimes = 0;
                        g_roamAt = now;
                        return;
                    }
                    else if (s_noWayTimes >= 3)
                    {
                        g_travelBlocked[key] = now + 1200000;
                        g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(qx / kTileSize)) << 32) |
                                        static_cast<uint32_t>(qy / kTileSize)] = now + 1200000;
                        s_noWayTimes = 0;
                        LOG("AutoAttack: no way to the goal {},{} three times in 10 min: left 20 min",
                            static_cast<int>(gx / kTileSize), static_cast<int>(gy / kTileSize));
                    }
                }
            }
            else
            {
            // At the goal and nothing comes of it (the analyst, 2026-11-11: A5 «looking around it» 25 min, 3 fights
            // in 28 min, the creature not speaking): after 6 min there the goal is left 15 min, a player goes and
            // does something else before coming back.
            static int32_t s_atGoalX = 0, s_atGoalY = 0;
            static DWORD s_atGoalSince = 0;
            // Something does come of it while the hero fights, loots or ends quests there (the stuck solver,
            // 2026-11-14: A7 at «kill 20 goblins», 19 killed and 4000 experience, left after 6 min all the same): the
            // six minutes count from the last of those.
            // A target alone counts for 20 minutes at one goal, no longer (the code reviewer: enemies that keep
            // coming, or cannot be reached, would hold the hero there for ever).
            static DWORD s_goalLoot = 0, s_goalDone = 0, s_goalFirst = 0;
            if (std::abs(qx - s_atGoalX) > 3 * kTileSize || std::abs(qy - s_atGoalY) > 3 * kTileSize ||
                g_lootCount != s_goalLoot || g_questsDoneAt != s_goalDone || !s_goalFirst)
            {
                s_goalFirst = now ? now : 1;
            }
            const bool progress = g_lootCount != s_goalLoot || g_questsDoneAt != s_goalDone ||
                                  (g_lastTargetAt && now - g_lastTargetAt < 60000 && now - s_goalFirst < 1200000);
            s_goalLoot = g_lootCount;
            s_goalDone = g_questsDoneAt;
            if (std::abs(qx - s_atGoalX) > 3 * kTileSize || std::abs(qy - s_atGoalY) > 3 * kTileSize || !s_atGoalSince ||
                now - s_atGoalSince > 900000 || progress)
            {
                s_atGoalX = qx;
                s_atGoalY = qy;
                s_atGoalSince = now;
            }
            else if (now - s_atGoalSince > 360000)
            {
                const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(qx / kTileSize)) << 32) |
                                     static_cast<uint32_t>(qy / kTileSize);
                g_travelBlocked[key] = now + 900000;
                if (!g_questBook.empty())
                {
                    // The book's own goal (qx, qy may be a door or the reachable tile nearest it).
                    const QuestGoal& g = goalWalked();
                    g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(g.x / kTileSize)) << 32) |
                                    static_cast<uint32_t>(g.y / kTileSize)] = now + 900000;
                }
                LOG("AutoAttack: 6 min at the quest's goal {},{} and nothing came of it: left 15 min",
                    static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize));
                s_atGoalSince = 0;
                questHere = false;
                g_roamAt = 0;
                return;
            }
            g_homeX = qx;
            g_homeY = qy;
            // A fixed destination (no creature): the journal's radius is wide (the arena's 22 tiles) but the script
            // may want the hero much nearer its centre (Manolito, FunkCode op 0x3F: the arena fight starts within 10
            // tiles of 3786,330, a wall). To the reachable tile nearest the centre, then the rest of the play there.
            if (who == 0xFFFFFFFFu && layer == 0)
            {
                const int gtx = static_cast<int>(qx / kTileSize), gty = static_cast<int>(qy / kTileSize);
                int nx = 0, ny = 0;
                // Within the reachable test's box only (as the fixed goal above: beyond it the box's edge is no goal).
                if (Whereabouts::reachable(gtx, gty) != -1 && Whereabouts::nearestReachable(gtx, gty, nx, ny))
                {
                    const int32_t wx = static_cast<int32_t>((nx + 0.5) * kTileSize);
                    const int32_t wy = static_cast<int32_t>((ny + 0.5) * kTileSize);
                    g_homeX = wx;
                    g_homeY = wy;
                    const bool chestNear = g_chestId && g_chestBest < 40.0 * kTileSize &&
                                               (g_chestHeading != g_chestId || now - g_chestSince < 60000);
                    const double wd = std::hypot(static_cast<double>(wx - self->x), static_cast<double>(wy - self->y));
                    // Shut in, the nearest tile reached and nothing happening: the script may wait on a trigger
                    // elsewhere in the yard (the arena's barriers open only after the «Equipo» tutorial, fired by the
                    // corner at 3803,345; seen live 2026-11-10: 3 min on the steps at 3794,333, «no way on» every 4.5 s).
                    // After 10 s there, 60 s across the shut-in ground: to its middle, then roaming from it; a new
                    // nearest tile (a barrier opened) ends it.
                    static uint64_t s_pinKey = 0;
                    static DWORD s_pinSince = 0, s_yardUntil = 0;
                    const uint64_t pinKey = (static_cast<uint64_t>(static_cast<uint32_t>(nx)) << 32) | static_cast<uint32_t>(ny);
                    const Whereabouts::Area& where = Whereabouts::area();
                    bool yard = false;
                    if (pinKey != s_pinKey || !where.shutIn)
                    {
                        s_pinKey = pinKey;
                        s_pinSince = s_yardUntil = 0;
                    }
                    else if (s_yardUntil && static_cast<int>(now - s_yardUntil) < 0)
                    {
                        yard = true;
                    }
                    else if (s_yardUntil)
                    {
                        s_yardUntil = s_pinSince = 0;       // over: back to the tile, the yard again in 10 s
                    }
                    else if (!s_pinSince && wd <= 1.5 * kTileSize)
                    {
                        s_pinSince = now;
                    }
                    else if (s_pinSince && now - s_pinSince > 10000)
                    {
                        LOG("AutoAttack: at {},{} by the quest's centre and nothing: 60 s across the shut-in ground", nx, ny);
                        s_yardUntil = now + 60000;
                        yard = true;
                    }
                    int mx = 0, my = 0;
                    if (yard && Whereabouts::nearestReachable((where.minX + where.maxX) / 2, (where.minY + where.maxY) / 2, mx, my))
                    {
                        const int32_t yx = static_cast<int32_t>((mx + 0.5) * kTileSize), yy = static_cast<int32_t>((my + 0.5) * kTileSize);
                        g_homeX = yx;
                        g_homeY = yy;
                        if (static_cast<int>(s_yardUntil - now) > 40000 &&
                            std::hypot(static_cast<double>(yx - self->x), static_cast<double>(yy - self->y)) > 1.5 * kTileSize)
                        {
                            if (!ClickWalk::routing() && now - g_questAskAt > 4000)
                            {
                                g_questAskAt = now;
                                ClickWalk::walkTo(yx, yy, false);
                            }
                            MapMemory::setRoute(true, yx, yy);
                            g_roamAt = 0;
                            return;
                        }
                    }
                    if (!yard && !chestNear && wd > 0.6 * kTileSize && !approachStalled(wx, wy, wd, now))
                    {
                        static uint64_t toldCentre = 0;
                        const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(nx)) << 32) | static_cast<uint32_t>(ny);
                        if (key != toldCentre)
                        {
                            toldCentre = key;
                            LOG("AutoAttack: in the quest's zone: to {},{}, the reachable tile nearest its centre {},{}",
                                nx, ny, gtx, gty);
                        }
                        if (!ClickWalk::routing() && now - g_questAskAt > 4000)
                        {
                            g_questAskAt = now;
                            ClickWalk::walkTo(wx, wy, false);
                        }
                        MapMemory::setRoute(true, wx, wy);
                        g_roamAt = 0;
                        return;
                    }
                }
            }
            // There: the quest's creature, if one, is spoken to.
            cObject* npc = who && who != 0xFFFFFFFFu ? objects->object(who) : nullptr;
            // The quest's thing to fetch (questThing): nobody to speak to; the collect takes it (Loot::Item: the quest
            // item flag lets it through the fixture test).
            if (npc && questThing(npc))
            {
                static uint32_t s_toldFetch = 0;
                if (s_toldFetch != who)
                {
                    s_toldFetch = who;
                    LOG("AutoAttack: the quest's {:x} is a quest item to fetch, not a creature: collected on the spot", who);
                }
                who = 0;
                npc = nullptr;
            }
            // The journal's id may now be another thing (the stuck solver, 2026-11-14: A1's quest named 772, by then a
            // piece of loot: «talkable false», never spoken to, in and out of the house until the goal was left): the
            // one to speak to is then the nearest creature that can be spoken to within 10 tiles of the goal.
            if (npc && !npc->asCreature())
            {
                struct GoalAt
                {
                    int32_t x, y;
                } goalAt{qx, qy};
                AimAssist::Target near1;
                const bool found = AimAssist::findObject(2500.0f, [](uint32_t id, void* context) {
                    cObjectManager* om = cObjectManager::instance();
                    cObject* o = om && !(id & 0x80000000u) ? om->object(id) : nullptr;
                    const auto* g = static_cast<const GoalAt*>(context);
                    return o && talkable(o) && !isPlainHireling(id) && std::abs(o->x - g->x) <= 10 * kTileSize &&
                           std::abs(o->y - g->y) <= 10 * kTileSize;
                }, &goalAt, near1);
                static uint32_t s_toldNot = 0;
                if (s_toldNot != who)
                {
                    s_toldNot = who;
                    LOG("AutoAttack: the quest's creature {:x} is no creature now: {}", who,
                        found ? "the one by the goal spoken to instead" : "none to speak to by the goal");
                }
                who = found ? near1.id : 0;
                npc = found ? objects->object(who) : nullptr;
            }
            // The quest's creature far away (the Gladiator's arena fight names one 5000 tiles off, its opponent
            // only comes when the fight starts): nothing to go for here, the rest of the agent's play meanwhile.
            if (const double away = npc ? std::max(std::abs(static_cast<double>(npc->x - self->x)),
                                                  std::abs(static_cast<double>(npc->y - self->y))) / kTileSize : 0.0;
                away > 60.0)
            {
                static uint32_t farId = 0;
                if (who != farId)
                {
                    farId = who;
                    LOG("AutoAttack: quest creature {:x} is {:.0f} tiles away, not here: playing on", who, away);
                }
                npc = nullptr;
            }
            // A kill quest: the target a living enemy of the hero's, gone for even beyond the fight range.
            // Not one left as too strong for now, nor any with no healing potion left (the live verifier, 2026-11-11:
            // the Dark Elf marked 5dd too strong, went for it as the quest's target 33 s on with no potion and died).
            // With no potion only one not clearly weaker is left (the reviewer: a foe far below the hero would hold
            // the quest forever when there is no gold for potions either).
            cCreature* questFoe = npc ? npc->asCreature() : nullptr;
            const auto levelOf = [](const cCreature* c) { return scaledLevel(c); };
            // Nor into a fight foreseen under 30 % to win (the live verifier, 2026-11-11: attacked at 8 % among six).
            const CombatLearn::Forecast& questFc = CombatLearn::forecast();
            const bool questLost = questFc.foes > 0 && questFc.win < 0.3f;
            if (questFoe && questFoe->health > 0 && hero->isEnemy(questFoe) &&
                (g_unreachable.count(who & 0xFFFF) || g_unreachable.count(who) || questLost ||
                 (Gear::healingLeft() == 0 && levelOf(questFoe) + 3 > levelOf(hero)) ||
                 (AgentSave::deathsSinceSave() >= 2 && levelOf(questFoe) > levelOf(hero))))
            {
                static uint32_t s_toldFoe = 0;
                if (s_toldFoe != who)
                {
                    s_toldFoe = who;
                    LOG("AutoAttack: quest target {:x} is an enemy, but {}: not now", who,
                        questLost ? "the fight is foreseen lost" : Gear::healingLeft() == 0 ? "no healing potion left" : "too strong for now");
                }
                questFoe = nullptr;
                npc = nullptr;
            }
            if (cCreature* foe = questFoe; foe && foe->health > 0 && hero->isEnemy(foe))
            {
                if (now - g_questAskAt > 2000)
                {
                    if (who != g_talkId)
                    {
                        g_talkId = who;
                        LOG("AutoAttack: quest target {:x} is an enemy: attacking it", who);
                    }
                    g_questAskAt = now;
                    attack(who);
                }
                MapMemory::setRoute(true, foe->x, foe->y);
                g_roamAt = 0;
                return;
            }
            const auto talked = g_talkedAt.find(who);
            const auto fails = g_talkFails.find(who);
            const int failed = fails != g_talkFails.end() ? fails->second : 0;
            const DWORD again = failed >= 4 ? 0xFFFFFFFFu : kTalkAgainMs << (2 * std::max(failed - 1, 0));
            // The quest's own creature is spoken to whatever its side (the player, 2026-11-13: the lost sheep Erica,
            // DQ_15005, «!» over it and the agent standing by: an animal's side is none of the townsfolk's, 8 «talkable
            // false» in a morning); an enemy was attacked above.
            // Not the hero's own horse (the stuck solver, 2026-11-16, A5: «Licor de lenteja», side quest 15036, from 08:10:
            // the creature to speak to resolved to 1ab9, the id of the hero's horse («getting off horse 1ab9»): side 4,
            // dialog 0, flags 4008040, health 400; «not spoken to: loaded true, talkable true», six tries and 30 s again,
            // 97 «speaking to» in the day and the experience down 71 %): no dialog and no trade bit, on the horses' side.
            const uint8_t* npcBytes = reinterpret_cast<const uint8_t*>(npc);
            const bool notSomeone = npcBytes && *reinterpret_cast<const uint32_t*>(npcBytes + kSide) == 4 &&
                                    *reinterpret_cast<const uint32_t*>(npcBytes + 0x245) == 0 &&
                                    !(*reinterpret_cast<const uint32_t*>(npcBytes + 0x14) & 0x80000);
            if (speakTo && notSomeone)
            {
                static uint32_t s_toldHorse = 0;
                if (s_toldHorse != who)
                {
                    s_toldHorse = who;
                    LOG("AutoAttack: quest creature {:x} is a horse with no dialog (side 4): not spoken to; the goal is looked "
                        "around instead", who);
                }
            }
            const bool questCreature = speakTo && npc && npc->asCreature() && !notSomeone;
            const bool talkNow = ((talkable(npc) && !notSomeone) || questCreature) && !isPlainHireling(who) && failed < 4 &&
                                 (talked == g_talkedAt.end() || now - talked->second > again);
            if (speakTo && !talkNow)
            {
                // What keeps the talk off, once per creature (the stuck solver: it failed with no word).
                static uint32_t s_whyId = 0;
                if (s_whyId != who)
                {
                    s_whyId = who;
                    LOG("AutoAttack: quest creature {:x} not spoken to: loaded {}, talkable {}, hireling {}, failed {}, "
                        "spoken {} s ago, {:.0f} tiles off",
                        who, npc != nullptr, talkable(npc), isHireling(who), failed,
                        talked == g_talkedAt.end() ? -1 : static_cast<int>((now - talked->second) / 1000),
                        npc ? std::max(std::abs(static_cast<double>(npc->x - self->x)),
                                       std::abs(static_cast<double>(npc->y - self->y))) / kTileSize : -1.0);
                }
            }
            if (talkNow)
            {
                // Spoken to on foot: a rider never got a word out of one (the stuck solver, 2026-11-11: only the Dwarf
                // and the Daemon, who never ride, spoke to quest creatures; the riders ringed them for hours).
                if (std::max(std::abs(static_cast<double>(npc->x - self->x)), std::abs(static_cast<double>(npc->y - self->y))) <
                        12.0 * kTileSize &&
                    HeroProfile::current().mounted)
                {
                    g_onFootUntil = now + 60000;
                }
                if (who != g_talkId)
                {
                    g_talkId = who;
                    g_talkTries = 0;
                    g_talkAt = 0;
                }
                if (!g_talkAt || now - g_talkAt > 4000)
                {
                    // Not a word with enemies about it (the stuck solver, 2026-11-13: the blacksmith of R01NQ04 among
                    // wolves and goblins, six tries again and again while the agent kept clear of them): they first.
                    const AggroFoe* nearFoe = nullptr;
                    // At most 5 times in 3 min for one creature (the code reviewer, 2026-11-13: enemies that cannot be
                    // reached, across water or a fence, kept the tries at zero and the quest was never left).
                    static uint32_t s_redirWho = 0;
                    static int s_redirs = 0;
                    static DWORD s_redirSince = 0;
                    if (s_redirWho != who || now - s_redirSince > 180000)
                    {
                        s_redirWho = who;
                        s_redirs = 0;
                        s_redirSince = now;
                    }
                    if (g_talkTries >= 3 && s_redirs < 5)
                    {
                        for (const AggroFoe& f : g_aggroFoes)
                        {
                            if (std::hypot(static_cast<double>(f.x - npc->x), static_cast<double>(f.y - npc->y)) < 12.0 * kTileSize)
                            {
                                nearFoe = &f;
                                break;
                            }
                        }
                    }
                    if (nearFoe)
                    {
                        static DWORD s_toldAt = 0;
                        if (now - s_toldAt > 30000)
                        {
                            s_toldAt = now;
                            LOG("AutoAttack: quest creature {:x} does not speak with enemies about it: {:x} fought first", who,
                                nearFoe->id);
                        }
                        ++s_redirs;
                        g_talkTries = 0;
                        g_talkAt = now;
                        g_questSeekUntil = now + 30000;
                        attack(nearFoe->id);
                    }
                    else if (++g_talkTries > 6)
                    {
                        const int times = ++g_talkFails[who];
                        LOG("AutoAttack: quest creature {:x} would not speak (time {}), left {}", who, times,
                            times >= 4 ? "for good" : "a while");
                        Findings::note("quest", self->x, self->y, "quest creature {:x} would not speak after 6 tries", who);
                        g_talkedAt[who] = now;
                        g_talkId = 0;
                        // What it is, for the next look (the stuck solver, 2026-11-16, A2: 18 orders at 0 tiles from 9a6,
                        // quest R15NQ02 «Los Planes de la Hermandad», no dialog, and an unspoken-to sign near that the
                        // log never named): its side, its dialog index, its flags and the signs about it.
                        {
                            const uint8_t* nb = reinterpret_cast<const uint8_t*>(npc);
                            LOG("AutoAttack: quest creature {:x} would not speak: side {}, dialog {}, flags {:x}/{:x}, health {}, "
                                "hero mode {:x}",
                                who, *reinterpret_cast<const uint32_t*>(nb + kSide), *reinterpret_cast<const uint32_t*>(nb + 0x245),
                                *reinterpret_cast<const uint32_t*>(nb + 0x14), *reinterpret_cast<const uint32_t*>(nb + 0x200),
                                *reinterpret_cast<const int32_t*>(nb + 0x4D8), *(reinterpret_cast<const uint8_t*>(self) + 0xFC));
                            bool otherSign = false;
                            for (const Sign& sign : g_signs)
                            {
                                const double fromHero = std::hypot(static_cast<double>(sign.x - self->x),
                                                                   static_cast<double>(sign.y - self->y)) / kTileSize;
                                LOG("AutoAttack: sign {:x} ({}) at tile {},{}, {:.0f} tiles from the hero, {:.0f} from {:x}", sign.id,
                                    sign.kind == GoalKind::Offer ? "quest offered" : "report", static_cast<int>(sign.x / kTileSize),
                                    static_cast<int>(sign.y / kTileSize), fromHero,
                                    std::hypot(static_cast<double>(sign.x - npc->x), static_cast<double>(sign.y - npc->y)) / kTileSize,
                                    who);
                                otherSign = otherSign || ((sign.id & 0xFFFF) != (who & 0xFFFF) && fromHero < 60.0 &&
                                                          !talkedLately(sign.id, now) && !isPlainHireling(sign.id));
                            }
                            // Another creature with a sign within reach: this goal waits 5 min and the book moves on to
                            // that one (else 6 min «looking around it» and 15 more parked before the book got there).
                            if (otherSign)
                            {
                                const uint64_t key = (static_cast<uint64_t>(static_cast<uint32_t>(qx / kTileSize)) << 32) |
                                                     static_cast<uint32_t>(qy / kTileSize);
                                g_travelBlocked[key] = now + 300000;
                                if (!g_questBook.empty())
                                {
                                    const QuestGoal& bg = goalWalked();
                                    g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(bg.x / kTileSize)) << 32) |
                                                    static_cast<uint32_t>(bg.y / kTileSize)] = now + 300000;
                                }
                                LOG("AutoAttack: another creature under a quest sign near: the goal at tile {},{} left 5 min",
                                    static_cast<int>(qx / kTileSize), static_cast<int>(qy / kTileSize));
                                questHere = false;
                                g_roamAt = 0;
                            }
                        }
                    }
                    else
                    {
                        LOG("AutoAttack: speaking to the quest creature {:x} (try {})", who, g_talkTries);
                        g_talkAt = now;
                        attack(who);
                    }
                }
                MapMemory::setRoute(true, npc->x, npc->y);
                g_roamAt = 0;
                return;
            }
            }
        }
        // A chest not yet opened within 150 tiles: there (the collect opens it once it is near). Given up after 90 s
        // on the way to one (behind a wall, across water).
        if (Config::autoAttack.pickup && Config::autoAttack.chests && layer == 0 && g_chestId &&
            static_cast<int>(now - g_entranceHoldUntil) >= 0 && (!questHere || g_chestBest < 40.0 * kTileSize))
        {
            // The time on one chest adds up across switches: seen live (2026-11-09), the quest and a chest 35 tiles
            // off took turns at the 40-tile line for minutes, each turn starting the 90 s again.
            static std::unordered_map<uint32_t, DWORD> s_chestTime;
            static DWORD s_chestTick = 0;
            if (g_chestId != g_chestHeading)
            {
                g_chestHeading = g_chestId;
                g_chestSince = now;
                LOG("AutoAttack: off to a chest not yet opened ({:x}, {:.0f} tiles)", g_chestId, g_chestBest / kTileSize);
            }
            else if (now - s_chestTick < 5000)
            {
                s_chestTime[g_chestId] += now - s_chestTick;
            }
            s_chestTick = now;
            if (s_chestTime.size() > 256)
            {
                s_chestTime.clear();
            }
            // A chest where the hero was just hurt with no enemy to answer: left like an unreachable one, else its
            // walk takes the hero straight back into the hits (the review of the findings, case 34).
            if (g_unseenSpotAt && now - g_unseenSpotAt < 120000 && std::abs(g_chestX - g_unseenSpotX) < 6 * kTileSize &&
                std::abs(g_chestY - g_unseenSpotY) < 6 * kTileSize)
            {
                LOG("AutoAttack: chest {:x} where the hero is hurt with no enemy seen, left", g_chestId);
                lootFailed(g_chestId, now);
                lootFailed(g_chestId, now);
                g_chestId = 0;
                g_chestHeading = 0;
            }
            else if (s_chestTime[g_chestId] > 90000 || now - g_chestSince > 90000)
            {
                LOG("AutoAttack: chest {:x} not reached in 90 s, left", g_chestId);
                Findings::note("unreachable", self->x, self->y, "chest {:x} not reached in 90 s of walks to it", g_chestId);
                s_chestTime.erase(g_chestId);
                lootFailed(g_chestId, now);
                lootFailed(g_chestId, now);
                g_chestId = 0;
                g_chestHeading = 0;
            }
            else
            {
                if (!ClickWalk::routing() && now - g_questAskAt > 4000)
                {
                    g_questAskAt = now;
                    ClickWalk::walkTo(g_chestX, g_chestY, false);
                }
                MapMemory::setRoute(true, g_chestX, g_chestY);
                g_roamAt = 0;
                return;
            }
        }
        // Nothing worth doing in this zone and another zone's quest known: off there (the farming zone and the
        // roaming come after, for a zone with nothing and no other goal known).
        if (Config::autoAttack.quests && !questHere && layer == 0 && g_zone.valid && !g_zone.worth && g_zone.next)
        {
            static int32_t toldX = 0, toldY = 0;
            if (g_zone.nextX != toldX || g_zone.nextY != toldY)
            {
                toldX = g_zone.nextX;
                toldY = g_zone.nextY;
                LOG("AutoAttack: nothing to do in region {}: off to region {} ({:.0f} tiles)", g_zone.region,
                    g_zone.nextRegion, g_zone.nextDistance / kTileSize);
            }
            if (travel(now, self, g_zone.nextX, g_zone.nextY, g_questAskAt))
            {
                MapMemory::setRoute(true, g_zone.nextX, g_zone.nextY);
                g_roamAt = 0;
                return;
            }
        }
        // No quest to see to: off to the farming zone (many enemies of the hero's level), roaming there.
        if (Config::autoAttack.farm && !questHere && layer == 0 && g_farmKnown)
        {
            // No fights lost: nothing to take here for 10 s (each fight foreseen going bad). Potions first (under half
            // the class's stock), else rest to 90 % (none after the hero), else another farming zone (this one left
            // 15 min). Then 10 s more before the next turn.
            if (Config::autoAttack.noLostFights && g_entryShutAt && now - g_entryShutAt > 10000 && hero)
            {
                const int left = Gear::healingLeft();
                bool chased = false;
                for (const AggroFoe& f : g_aggroFoes)
                {
                    chased = chased || f.onHero;
                }
                std::string what;
                if (left >= 0 && left < Mind::now().potionStock / 2 && !Gear::wantsShop())
                {
                    Gear::askPotions(now + 600000);
                    what = std::format("to the merchant for potions ({} left)", left);
                }
                else if (hero->health * 10 < hero->maxHealth * 9 && !chased)
                {
                    g_quietUntil = now + 30000;
                    what = std::format("resting to 90% ({} of {})", hero->health, hero->maxHealth);
                }
                else
                {
                    g_vetoedCircles.push_back({static_cast<int>(g_farmX / kTileSize), static_cast<int>(g_farmY / kTileSize), now});
                    g_farmKnown = false;
                    what = "another farming zone (this one left 15 min)";
                }
                LOG("AutoAttack: no fight to take for {} s: {}", (now - g_entryShutAt) / 1000, what);
                remember(std::format("sin peleas que ganar aquí: {}", what));
                g_entryShutAt = now;
                if (!g_farmKnown)
                {
                    return;
                }
            }
            if (g_intent != Intent::Farm)
            {
                setIntent(Intent::Farm, "no quest to see to: experience where the enemies fit the hero");
            }
            const double away = std::hypot(static_cast<double>(g_farmX - self->x), static_cast<double>(g_farmY - self->y));
            if (away > 20.0 * kTileSize)
            {
                // The way to farm is farming too: all the loot around is taken (no quest waits).
                if (travel(now, self, g_farmX, g_farmY, g_questAskAt))
                {
                    MapMemory::setRoute(true, g_farmX, g_farmY);
                    g_roamAt = 0;
                    return;
                }
            }
            g_homeX = g_farmX;
            g_homeY = g_farmY;
        }
        if (!Config::autoAttack.roam)
        {
            return;
        }
        if (questHere)
        {
            // At the quest's goal: still the quest, looking around it (not «explore»: the analyst saw the two
            // swapping every second, 172 lines in 10 minutes).
            setIntent(Intent::Quest, "at the quest's goal: looking around it");
            // Inside a house the look around is the way out: 30 s standing at the goal first (a dialog, a pick up, a
            // sign to appear), then the look.
            if (layer != 0)
            {
                static DWORD s_insideSince = 0, s_insideSeen = 0;
                if (now - s_insideSeen > 5000)
                {
                    s_insideSince = now;
                }
                s_insideSeen = now;
                if (now - s_insideSince < 30000)
                {
                    g_roamAt = now;
                    return;
                }
            }
            // By the journal's text, or by the quest's number (docs/QUESTS.md's table, the «matar» rows: the text's
            // kind is often not told, «sin saber»).
            // The «matar» rows renumbered as the journal has them (rq() above, 2026-11-16; the old list was in block X's
            // numbering: 1002 was R18NQ02's and is the journal's R10NQ02, «Planes de la inquisición», no kill). Not
            // 1101 «Hábitos negros» (a rescue).
            static constexpr int32_t kKillQuests[] = {
                151,   301,   303,   401,   403,   501,   502,   602,   703,   803,   902,   903,   1001,  1102,
                1103,  1201,  1203,  1301,  1302,  1402,  1501,  1801,  1802,  1901,  2001,  2003,  2201,  2302,
                2413,  2503,  6001,  10250, 10251, 10252, 10253, 10259, 15003, 15007, 15011, 15012, 15013, 15015, 15018, 15020,
                15024, 15028, 15029, 15030, 15032, 15034, 15038, 15041, 15042, 15043, 15047, 15048, 15050, 15056,
                15057, 15058, 15059, 15063, 15068, 15073, 15074, 15075, 15076, 15078, 15081, 15082};
            const bool killByNumber = !g_questBook.empty() && goalWalked().kind == GoalKind::Journal &&
                                      std::find(std::begin(kKillQuests), std::end(kKillQuests), goalWalked().number) !=
                                          std::end(kKillQuests);
            if (Lore::questKind() == Lore::QuestKind::Kill || killByNumber)
            {
                if (!g_questSeekUntil || static_cast<int>(now - g_questSeekUntil) > 60000)
                {
                    LOG("AutoAttack: the quest asks for a kill: the fights around its goal are sought");
                }
                g_questSeekUntil = now + 8000;
            }
            // A goal that is never met (docs/Estudio-mejoras.md P1: A5 two hours around 3468,2753, 590 «going to
            // look», 40 experience an hour; the stuck guard saw the hero moving): 6 min around one goal with neither
            // a fight nor the journal moving, and it is left for 30 min, the next goal or the farming instead.
            if (!g_questBook.empty())
            {
                static uint64_t s_lookKey = 0;
                static DWORD s_lookSince = 0;
                const QuestGoal& looked = goalWalked();
                const uint64_t lookKey = (static_cast<uint64_t>(static_cast<uint32_t>(looked.x / kTileSize)) << 32) |
                                         static_cast<uint32_t>(looked.y / kTileSize);
                // Counted only with the hero at the goal (within its ring, 30 tiles at least): the quests' session,
                // 2026-11-16, A8 04:00:45 «6 min around the goal 3382,3300 … left 30 min» with the hero 529 tiles off.
                const bool lookFar = std::max(std::abs(static_cast<double>(looked.x - self->x)),
                                              std::abs(static_cast<double>(looked.y - self->y))) >
                                     std::max(looked.radius, 30.0 * kTileSize);
                if (lookFar || lookKey != s_lookKey || !s_lookSince ||
                    (g_lastTargetAt && static_cast<int>(g_lastTargetAt - s_lookSince) > 0) ||
                    (g_questsDoneAt && static_cast<int>(g_questsDoneAt - s_lookSince) > 0))
                {
                    s_lookKey = lookKey;
                    s_lookSince = now;
                }
                else if (now - s_lookSince > 360000)
                {
                    g_travelBlocked[lookKey] = now + 1800000;
                    s_lookSince = 0;
                    LOG("AutoAttack: 6 min around the goal {},{} (quest {}) with neither a fight nor the journal moving: "
                        "left 30 min",
                        static_cast<int>(looked.x / kTileSize), static_cast<int>(looked.y / kTileSize), looked.number);
                    Findings::note("quest", looked.x, looked.y, "a goal never met: 6 min around it, left 30 min");
                    g_roamAt = 0;
                    return;
                }
            }
            // Within the goal's ring but walled off from it (the player, 2026-11-12: A5 behind a house by the grave
            // digger's yard at 3190,2773, asking for the goal every 4 s for minutes): after 30 s still 3 tiles or more
            // off, the way in near the goal, as travel() does when no walk gets nearer.
            static DWORD s_offGoalSince = 0;
            const double offGoal = std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y));
            if ((qx || qy) && offGoal > 3.0 * kTileSize)
            {
                if (!s_offGoalSince)
                {
                    s_offGoalSince = now;
                }
                else if (now - s_offGoalSince > 30000 && entranceNearGoal(now, self, qx, qy))
                {
                    s_offGoalSince = now;
                    g_roamAt = now;
                    return;
                }
            }
            else
            {
                s_offGoalSince = 0;
            }
        }
        else if (g_intent != Intent::Farm || !g_farmKnown)
        {
            // Exploring (the player, 2026-11-10): first the ground unseen, then the loot on it, a fight only in danger
            // (seek off: only those that strike are fought).
            setIntent(Intent::Explore, "nothing to see to around: the ground unseen, its loot, a fight only if attacked");
        }
        // Exploring takes in the caves, cellars and houses near whose inside fits the hero's level (the player: the
        // agent never went into an interior on purpose): to its way in (a stairs anchor by its outside landing, or a
        // tpstart tile), each once a game; in when the hero lands by its inside.
        if (g_intent == Intent::Explore && layer == 0)
        {
            static int s_goingIn = -1;
            static DWORD s_goingSince = 0;
            static std::unordered_set<int> s_doneInteriors;
            const std::vector<Teleports::Interior>& all = Teleports::interiors();
            const int htx = static_cast<int>(self->x / kTileSize), hty = static_cast<int>(self->y / kTileSize);
            if (s_goingIn >= 0)
            {
                const Teleports::Interior& in = all[s_goingIn];
                if (std::abs(htx - in.inX) < 30 && std::abs(hty - in.inY) < 30)
                {
                    LOG("AutoAttack: into the interior at {},{}: exploring it", in.inX, in.inY);
                    s_doneInteriors.insert(s_goingIn);
                    s_goingIn = -1;
                }
                else if (now - s_goingSince > 180000)
                {
                    LOG("AutoAttack: the way into {},{} not found in 3 min, left", in.inX, in.inY);
                    s_doneInteriors.insert(s_goingIn);
                    s_goingIn = -1;
                }
            }
            if (s_goingIn < 0)
            {
                const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xAD5C40);
                const uint8_t* world = holder ? *reinterpret_cast<const uint8_t* const*>(holder) : nullptr;
                double best = 80.0;
                for (int i = 0; i < static_cast<int>(all.size()); ++i)
                {
                    const Teleports::Interior& in = all[i];
                    int lo = 0, hi = 0;
                    const double d = std::hypot(in.outX - htx, in.outY - hty);
                    if (d < best && !s_doneInteriors.count(i) && in.outX < 3900 && world &&
                        sectorLevels(world, in.inX, in.inY, lo, hi) && lo <= heroLevel + 2 && hi + 4 >= heroLevel)
                    {
                        best = d;
                        s_goingIn = i;
                    }
                }
                if (s_goingIn >= 0)
                {
                    s_goingSince = now;
                    const Teleports::Interior& in = all[s_goingIn];
                    LOG("AutoAttack: an interior of the hero's level at {:.0f} tiles (its way in by {},{}; inside {},{})",
                        best, in.outX, in.outY, in.inX, in.inY);
                    setIntent(Intent::Explore, "an interior of its level near: going in to explore it");
                }
            }
            if (s_goingIn >= 0)
            {
                const Teleports::Interior& in = all[s_goingIn];
                std::vector<std::pair<int, int>> doors;
                if (in.start)
                {
                    doors.emplace_back(in.outX, in.outY);
                }
                else
                {
                    doors = Teleports::anchorsNear(0, in.outX, in.outY, 6);
                }
                if (doors.empty())
                {
                    s_doneInteriors.insert(s_goingIn);
                    s_goingIn = -1;
                }
                else
                {
                    auto [dx, dy] = doors.front();
                    for (const auto& d : doors)
                    {
                        if (std::hypot(d.first - htx, d.second - hty) < std::hypot(dx - htx, dy - hty))
                        {
                            dx = d.first;
                            dy = d.second;
                        }
                    }
                    const int32_t wx = static_cast<int32_t>((dx + 0.5) * kTileSize), wy = static_cast<int32_t>((dy + 0.5) * kTileSize);
                    noteDoor(dx, dy);
                    if (std::hypot(dx - htx, dy - hty) > 1.5)
                    {
                        if (travel(now, self, wx, wy, g_questAskAt))
                        {
                            MapMemory::setRoute(true, wx, wy);
                            g_roamAt = 0;
                            return;
                        }
                    }
                    else if (!g_roamAt || now - g_roamAt > 3000)
                    {
                        // On the way in and nothing yet: a step off, the next look steps on again.
                        g_roamAt = now;
                        ClickWalk::walkTo(self->x + static_cast<int32_t>(2 * kTileSize), self->y, false);
                        return;
                    }
                }
            }
        }
        MapMemory::visit(layer, self->x, self->y);
        // No further since the last order: that way is blocked (water, a wall), and the map remembers it.
        if (g_roamAt)
        {
            // Progress along the way it was sent: under half the step is blocked (a pathfinder stopping at the water
            // after a tile, as much as no step at all).
            const double mx = self->x - g_roamFromX, my = self->y - g_roamFromY;
            const double wx = g_walkX - g_roamFromX, wy = g_walkY - g_roamFromY;
            const double way = std::max(std::sqrt(wx * wx + wy * wy), 0.5 * kTileSize);
            const double along = (mx * wx + my * wy) / way;     // toward the step's end
            if (along < 0.5 * std::min(way, Config::autoAttack.roamStep * kTileSize))
            {
                ++g_roamStuck;
                // The square just ahead of where it stopped is what it could not step on.
                MapMemory::blocked(layer, static_cast<int32_t>(self->x + std::cos(g_roamAngle) * kTileSize),
                                   static_cast<int32_t>(self->y + std::sin(g_roamAngle) * kTileSize));
            }
            else
            {
                g_roamStuck = 0;
            }
        }
        if (g_roamStuck >= 8)
        {
            // Hemmed in: a new home here, so the hero roams from where it is.
            LOG("AutoAttack: no way on from here, roaming from this spot on");
            g_homeX = self->x;
            g_homeY = self->y;
            g_roamStuck = 0;
            // Hemmed in again and again on the same spot (the player, 2026-11-11: the Dwarf on the arena's tiers above
            // its fence, «no way on» every 4.5 s for minutes, the quest's goal below): the steps straight out fail, so
            // a routed walk to ground 12 tiles off (stairs found by the route), and the quest's goal left 10 min.
            static int s_hemmed = 0;
            static DWORD s_hemmedAt = 0;
            static int32_t s_hemmedX = 0, s_hemmedY = 0;
            // Not counted by a door's landing (within 8 tiles): its step is a cramped spot by nature, and the walk out
            // of it would be the door itself.
            const bool byDoor = layer == 0 && RouteNet::nearDoorLanding(static_cast<int>(self->x / kTileSize),
                                                                        static_cast<int>(self->y / kTileSize), 8);
            if (byDoor)
            {
                s_hemmed = 0;
            }
            else if (now - s_hemmedAt < 30000 &&
                std::hypot(static_cast<double>(self->x - s_hemmedX), static_cast<double>(self->y - s_hemmedY)) < 6.0 * kTileSize)
            {
                ++s_hemmed;
            }
            else
            {
                s_hemmed = 1;
                s_hemmedX = self->x;
                s_hemmedY = self->y;
            }
            s_hemmedAt = now;
            if (s_hemmed >= 3)
            {
                s_hemmed = 0;
                if (g_questX || g_questY)
                {
                    g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(g_questX / kTileSize)) << 32) |
                                    static_cast<uint32_t>(g_questY / kTileSize)] = now + 600000;
                }
                if (!g_questBook.empty())
                {
                    const QuestGoal& g = goalWalked();
                    g_travelBlocked[(static_cast<uint64_t>(static_cast<uint32_t>(g.x / kTileSize)) << 32) |
                                    static_cast<uint32_t>(g.y / kTileSize)] = now + 600000;
                }
                // Ground 12 tiles off, not by a door's landing (8 tries; A5 in cave 5.2 was sent to its way out).
                int nx = 0, ny = 0;
                for (int t = 0; t < 8; ++t)
                {
                    const double a = (std::rand() % 360) * 3.14159265358979 / 180.0;
                    nx = static_cast<int>((self->x + std::cos(a) * 12.0 * kTileSize) / kTileSize);
                    ny = static_cast<int>((self->y + std::sin(a) * 12.0 * kTileSize) / kTileSize);
                    Whereabouts::nearestReachable(nx, ny, nx, ny);
                    if (layer != 0 || !RouteNet::nearDoorLanding(nx, ny, 8))
                    {
                        break;
                    }
                }
                const int32_t wx = static_cast<int32_t>((nx + 0.5) * kTileSize), wy = static_cast<int32_t>((ny + 0.5) * kTileSize);
                LOG("AutoAttack: hemmed in 3 times here: a routed walk to tile {},{} and the quest's goal left 10 min", nx, ny);
                ClickWalk::walkTo(wx, wy, false);
                MapMemory::setRoute(true, wx, wy);
                g_homeX = wx;
                g_homeY = wy;
                g_roamAt = now;
                return;
            }
        }
        // Of 16 directions, the one toward the ground least seen (a few cells ahead, nearer ones counting more), not
        // known blocked, keeping roughly the way it goes (no back and forth), and back toward home beyond the leash.
        const double hx = g_homeX - self->x, hy = g_homeY - self->y;
        const double homeDistance = std::sqrt(hx * hx + hy * hy);
        double bestAngle = g_roamAngle;
        float bestCost = 1e9f;
        // The way is kept for some steps unless blocked or past the leash: steps that wander back and forth see nothing.
        // A step's end the hero can stand on, by the game's own tile test: the path finder drops a walk to a tree, a
        // rock or water at once (seen live in a forest: walking, then standing, not a pixel moved, step after step).
        // The step's length out (menu), else shorter down to one tile; none: that way is closed (marked so on the
        // map). The tile's middle.
        const bool heroByDoor = layer == 0 && RouteNet::nearDoorLanding(static_cast<int>(self->x / kTileSize),
                                                                         static_cast<int>(self->y / kTileSize), 8);
        const auto stepEnd = [&](double a, int32_t& x, int32_t& y) {
            for (int step = std::clamp(Config::autoAttack.roamStep, 1, 20); step >= 1; --step)
            {
                const double tiles = step;
                const int tx = static_cast<int>(std::floor((self->x + std::cos(a) * tiles * kTileSize) / kTileSize));
                const int ty = static_cast<int>(std::floor((self->y + std::sin(a) * tiles * kTileSize) / kTileSize));
                const int ok = ClickWalk::walkable(layer, tx, ty);
                // Never onto a door's landing (within 8 tiles; within 3 once the hero stands that near, so it can
                // roam off it): a roaming step there goes through the door.
                if (ok != 0 && layer == 0 && RouteNet::nearDoorLanding(tx, ty, heroByDoor ? 3 : 8))
                {
                    continue;
                }
                if (ok != 0)
                {
                    x = static_cast<int32_t>((tx + 0.5) * kTileSize);
                    y = static_cast<int32_t>((ty + 0.5) * kTileSize);
                    return true;
                }
                MapMemory::blocked(layer, static_cast<int32_t>((tx + 0.5) * kTileSize), static_cast<int32_t>((ty + 0.5) * kTileSize));
            }
            return false;
        };
        int32_t keptX = 0, keptY = 0;
        ++g_roamSteps;
        const bool rethink = g_roamStuck > 0 || g_roamSteps >= 6 || homeDistance > kRoamLeash || !g_roamAt ||
                             !stepEnd(g_roamAngle, keptX, keptY);
        if (rethink)
        {
            g_roamSteps = 0;
        }
        bool found = !rethink;
        int32_t bestX = keptX, bestY = keptY;
        const bool avoidAggro = g_intent != Intent::Farm && !Config::autoAttack.seek && !g_aggroFoes.empty() &&
                                !(g_questSeekUntil && static_cast<int>(now - g_questSeekUntil) < 0);
        float aggroCost[16] = {};
        int bestK = -1;
        for (int k = 0; k < 16 && rethink; ++k)
        {
            const double a = k * 3.14159265 / 8.0;
            const double ux = std::cos(a), uy = std::sin(a);
            int32_t endX = 0, endY = 0;
            if (!stepEnd(a, endX, endY))
            {
                continue;
            }
            float cost = 0.0f;
            for (int d = 1; d <= 4; ++d)
            {
                const double reach = d * 3.0 * kTileSize;
                cost += MapMemory::cost(layer, static_cast<int32_t>(self->x + ux * reach),
                                        static_cast<int32_t>(self->y + uy * reach)) / d;
            }
            // Exploring (not farming nor seeking a fight): the ways within reach of foes not after the hero yet cost
            // (the player: «informar al agente el rango de aggro de los enemigos, para no meterse en peleas
            // innecesariamente»); a pack, each of it.
            if (avoidAggro)
            {
                float closeBy = 0.0f;
                for (const AggroFoe& f : g_aggroFoes)
                {
                    if (f.onHero)
                    {
                        continue;
                    }
                    for (int d = 1; d <= 4; ++d)
                    {
                        const double px = self->x + ux * d * 3.0 * kTileSize, py = self->y + uy * d * 3.0 * kTileSize;
                        if (std::hypot(f.x - px, f.y - py) < kAggroTiles * kTileSize)
                        {
                            closeBy += 0.6f / d;
                            break;
                        }
                    }
                }
                cost += std::min(closeBy, 4.0f);
                aggroCost[k] = std::min(closeBy, 4.0f);
            }
            // Turning away from the way it goes costs a little; turning back, more.
            const double turn = std::fabs(std::remainder(a - g_roamAngle, 2.0 * 3.14159265));
            cost += static_cast<float>(turn) * 0.35f;
            // Beyond the leash, away from home costs; toward it is free.
            if (homeDistance > kRoamLeash)
            {
                const double toward = (ux * hx + uy * hy) / homeDistance;   // 1 straight home, -1 straight away
                cost += static_cast<float>((1.0 - toward) * (homeDistance / kRoamLeash) * 2.0);
            }
            cost += jitter(0, 30) / 100.0f;
            if (cost < bestCost)
            {
                bestCost = cost;
                bestAngle = a;
                bestX = endX;
                bestY = endY;
                found = true;
                bestK = k;
            }
        }
        if (avoidAggro && bestK >= 0)
        {
            static DWORD s_aggroToldAt = 0;
            float worst = 0.0f;
            for (float c : aggroCost)
            {
                worst = std::max(worst, c);
            }
            if (worst > 0.0f && now - s_aggroToldAt > 30000)
            {
                s_aggroToldAt = now;
                LOG("AutoAttack: {} hostile near, not after the hero yet: exploring around them (the way taken {:.1f} "
                    "of aggro, the worst {:.1f})", g_aggroFoes.size(), aggroCost[bestK], worst);
                remember(std::format("rodea {} enemigos que aún no le atacan", g_aggroFoes.size()));
            }
        }
        MapMemory::save(now, 300000);
        if (!found)
        {
            // Closed in on every side as far as the tile test tells: wait, as a hit or the player may free it.
            g_roamAt = now;
            g_roamStuck = 0;
            MapMemory::setRoute(false);
            return;
        }
        g_roamAngle = bestAngle;
        g_roamFromX = self->x;
        g_roamFromY = self->y;
        g_walkX = bestX;
        g_walkY = bestY;
        sendWalk();
        MapMemory::setRoute(true, g_walkX, g_walkY);
        static DWORD s_lookToldAt = 0;      // once a minute: each fight and shop set g_roamAt back (224 lines an hour)
        if ((!g_roamAt || now - g_roamAt > 10000) && (!s_lookToldAt || now - s_lookToldAt > 60000) && (s_lookToldAt = now))
        {
            LOG("AutoAttack: nothing around, going to look ({:.0f} tiles from where it began, {} cells of this layer "
                "seen)", homeDistance / kTileSize, MapMemory::cellsOn(layer));
        }
        g_roamAt = now;
    }

    // The agent's own collect: the loot within LootRange (items, chests and other containers, hiding places and
    // wells) taken one by one, each with the order a click on it gives. Never the game's collect (the A key and the
    // taskbar button stay the player's, as in the plain game). The auto attack waits meanwhile; a click of the
    // player's or a hit taken ends it.
    constexpr DWORD kCollectMaxMs = 90000;
    DWORD g_collectStart = 0;
    int g_collectHealth = 0;

    DWORD g_collectEndedAt = 0;    // see autoCollect

    void endCollect(const char* why)
    {
        if (g_collecting)
        {
            LOG("AutoAttack: collect over ({})", why);
            g_collectEndedAt = GetTickCount();
        }
        g_collecting = false;
        g_collectOne = false;
        g_target = 0;
        g_looting = false;
        g_pending = 0;
    }

    void startCollect(DWORD now)
    {
        ClickWalk::cancel();    // the travel's next stretch would cut the stooping short
        g_collecting = true;
        g_collectStart = now;
        g_target = 0;
        g_looting = false;
        g_pending = 0;
        int maximum = 0;
        g_collectHealth = 0;
        AimAssist::heroHealth(g_collectHealth, maximum);
        Tactics::reset();
        LOG("AutoAttack: collect (the agent's own)");
    }

    void collectFrame(DWORD now)
    {
        if (!Controller::worldRunning() || !heroAlive())
        {
            // A window the loot opened (the storage chest in town, a trader): never gone for again. Only with the hero
            // at it: on the way there the window is the player's own (the inventory, Esc, a loading), and the loot is
            // merely left for now.
            if (g_target && g_lootAtSince && heroAlive())
            {
                LOG("AutoAttack: loot {:x} opened a window, left for good", g_target);
                g_lootDone.insert(lootKey(g_target));
                ++g_lootCount;
            }
            endCollect("no hero or world");
            return;
        }
        if (static_cast<int>(now - g_collectStart) > static_cast<int>(g_collectOne ? 8000u : kCollectMaxMs))
        {
            endCollect("time out");
            return;
        }
        int health = 0, maximum = 0;
        if (AimAssist::heroHealth(health, maximum))
        {
            if (g_collectHealth && health < g_collectHealth)
            {
                if (!g_collectOne)
                {
                    endCollect("hit");
                    return;
                }
            }
            g_collectHealth = health;
        }

        // One at a time: no new order while the hero stoops for one.
        if ((g_pickupUntil && static_cast<int>(now - g_pickupUntil) < 0))
        {
            return;
        }
        if (g_target)
        {
            AimAssist::Target current;
            const float reach = static_cast<float>(Config::autoAttack.lootRange) * 1.5f;
            if (!isFixed(g_target) && !AimAssist::findObject(reach, &isCurrent, nullptr, current))
            {
                g_target = 0;           // gone from the ground: being picked up
                g_pickupUntil = now + kPickupMs;
                return;
            }
            if (!lootDone(g_target, now))
            {
                // Again only when the hero stalls and stands idle: a new order during the pick up (the hero stooping)
                // restarts it, cut short again and again; at the loot after a walk there (far loot) the hero stands
                // with no pick up order yet, so it gets one.
                const int sinceSent = static_cast<int>(now - g_sentAt);
                const bool stalled = g_lootAtSince || static_cast<int>(now - g_lootBestAt) > static_cast<int>(kLootNudgeMs);
                cObjectManager* objects = cObjectManager::instance();
                const bool idle = objects && CombatState::action(objects->hero()) == CombatState::Standing;
                // Just arrived after a walk there (the order sent was the walk): the use order now, the hero still
                // walking or not (seen: a well reached, 3 s standing at it, used only on the retry).
                const bool arrivedUnsent = g_lootAtSince && static_cast<int>(g_sentAt - g_lootAtSince) < 0 &&
                                           now - g_lootAtSince > 300;
                if (((idle && stalled) || arrivedUnsent) && sinceSent > static_cast<int>(kLootNudgeMs) && attack(g_target))
                {
                    g_sentAt = now;
                }
                return;
            }
            // Done for good only when the hero stood at it and it is no item still lying there (an opened container,
            // a used well); an item at its feet is tried again soon, one not reached a minute later.
            if (g_lootStale)
            {
                // The id names another thing now: not gone for again at once (a short wait, kept by its place).
                lootFailed(g_target, now, true);
            }
            else if (g_lootAtSince && !g_lootStill)
            {
                if (g_lootDone.size() > 4096)
                {
                    g_lootDone.clear();
                }
                g_lootDone.insert(lootKey(g_target));
                ++g_lootCount;
            }
            else
            {
                lootFailed(g_target, now, g_lootStill);
            }
            g_lootStill = false;
            g_lootStale = false;
            g_target = 0;
            if (g_collectOne)
            {
                endCollect("one piece, back to the fight");
                return;
            }
        }
        uint32_t next = 0;
        if (!findLoot(next))
        {
            endCollect("nothing left");
            return;
        }
        if (attack(next))
        {
            LOG("AutoAttack: collect {:x}", next);
            g_target = next;
            g_looting = true;
            g_sentAt = now;
            g_lootAtSince = 0;
            g_lootStill = false;
            g_lootStale = false;
            g_lootBestAt = now;
            g_lootBest = 1e9f;
        }
        else
        {
            lootFailed(next, now);
        }
    }

    // Collect always ([AutoAttack] AutoCollect): with loot within LootRange and no fight on, the agent's own collect
    // runs. Not while enemies attack the hero, it was hurt lately or the auto attack
    // has an enemy; a while after each collect, so loot it could not take is not gone for again and again.
    constexpr DWORD kAutoCollectLookMs = 500;
    constexpr DWORD kAutoCollectRestMs = 3000;
    constexpr DWORD kAutoCollectHurtMs = 3000;
    DWORD g_autoCollectLookAt = 0;
    DWORD g_autoHurtAt = 0;
    int g_autoLastHealth = 0;
    // Never in the way of the player: only a while after their last click, with the hero standing.
    constexpr DWORD kAutoCollectIdleMs = 2500;
    constexpr DWORD kAutoCollectStillMs = 1000;
    DWORD g_autoMovedAt = 0;
    int32_t g_autoHeroX = 0, g_autoHeroY = 0;

    // An enemy fighting the hero (or what it rides), one of its hirelings, or one the player attacked.
    bool engaged(cObjectManager* objects, uint32_t id, uint32_t self, uint32_t hero)
    {
        if (g_playerTargets.count(id))
        {
            return true;
        }
        cObject* foe = objects->object(id);
        const uint32_t aim = foe ? aimOf(objects, foe) : 0;
        return aim && (aim == hero || aim == self || isHireling(aim));
    }

    bool underAttack()
    {
        cObjectManager* objects = cObjectManager::instance();
        cEngine* engine = FrameHooks::engine();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (!objects || !engine || !hero)
        {
            return true;
        }
        AimAssist::Foe foes[kMaxFoes];
        const int count =
            AimAssist::enemies(static_cast<float>(Config::autoAttack.range) * kEngagedReach, foes, kMaxFoes);
        for (int i = 0; i < count; ++i)
        {
            if (engaged(objects, foes[i].id, engine->controlled, hero->id))
            {
                return true;
            }
        }
        return false;
    }

    void autoCollect(DWORD now)
    {
        int health = 0, maximum = 0;
        if (AimAssist::heroHealth(health, maximum))
        {
            if (g_autoLastHealth && health < g_autoLastHealth)
            {
                g_autoHurtAt = now;
            }
            g_autoLastHealth = health;
        }
        cObjectManager* objects = cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (hero && (hero->x != g_autoHeroX || hero->y != g_autoHeroY))
        {
            g_autoHeroX = hero->x;
            g_autoHeroY = hero->y;
            g_autoMovedAt = now;
        }
        // The hero standing still is the player's play left alone; walking for the agent (roaming, after a fight) it
        // never stands, and loot it passes is taken on the way.
        if ((g_autoCollectLookAt && static_cast<int>(now - g_autoCollectLookAt) < 0) ||
            (g_quietUntil && static_cast<int>(now - g_quietUntil) < static_cast<int>(kAutoCollectIdleMs)) ||
            (!g_on && static_cast<int>(now - g_autoMovedAt) < static_cast<int>(kAutoCollectStillMs)))
        {
            return;
        }
        g_autoCollectLookAt = now + kAutoCollectLookMs;
        if (g_target || g_pending || Tactics::busy(now) || heroCasting() ||
            (g_collectEndedAt && static_cast<int>(now - g_collectEndedAt) < static_cast<int>(kAutoCollectRestMs)) ||
            (g_autoHurtAt && static_cast<int>(now - g_autoHurtAt) < static_cast<int>(kAutoCollectHurtMs)))
        {
            return;
        }
        uint32_t loot = 0;
        if (!findLoot(loot) || underAttack())
        {
            return;
        }
        LOG("AutoAttack: loot about ({:x}), collecting", loot);
        startCollect(now);
    }

    // A game loaded or another hero: ids and tiles are the old game's, and what they say (loot done or failed,
    // enemies the player attacked, hirelings, enemies out of reach) would hold for whatever now has them.
    uint32_t g_gameHero = 0;
    bool g_wasLoading = false;

    void resetGame(const char* why)
    {
        LOG("AutoAttack: {}, per-game state cleared", why);
        MapMemory::forgetHero();
        endCollect(why);
        g_lootDone.clear();
        g_lootFailures.clear();
        g_playerTargets.clear();
        g_followers.clear();
        g_hirelings.clear();
        g_unreachable.clear();
        g_unreachableAt.clear();
        g_unreachableTimes.clear();
        g_farAimLooks.clear();
        g_lastWorld.clear();
        g_lastDistance.clear();
        g_lastHealth = 0;
        g_hurtAt = 0;
        g_autoLastHealth = 0;
        g_autoHurtAt = 0;
        g_retreatUntil = 0;
        g_homeSet = false;
        g_quietSince = 0;
        g_roamAt = 0;
        g_noRetreatUntil = 0;
        g_pickupUntil = 0;
        g_gameHero = 0;     // the hero after the load is adopted without a second clear
        Tactics::reset();
    }

    void checkNewGame()
    {
        cEngine* engine = FrameHooks::engine();
        const bool loading = engine && (engine->flags & cEngine::loading);
        if (loading && !g_wasLoading)
        {
            resetGame("game loading");
        }
        g_wasLoading = loading;
        cObjectManager* objects = loading ? nullptr : cObjectManager::instance();
        cCreature* hero = objects ? objects->hero() : nullptr;
        if (hero && hero->id != g_gameHero)
        {
            if (g_gameHero)
            {
                resetGame("another hero");
            }
            g_gameHero = hero->id;
        }
    }

    // The player's teleport (Home menu): off while the agent plays, so the agent never moves but by the game's own ways.
    void drawTeleport()
    {
        static int s_x = 0, s_y = 0, s_layer = 0, s_pick = -1;
        int hx = 0, hy = 0, hl = 0;
        if (!Teleports::heroAt(hx, hy, hl))
        {
            ImGui::TextDisabled("Sin héroe en el mundo.");
            return;
        }
        ImGui::Text("El héroe está en %d, %d (capa %d)", hx, hy, hl);
        if (g_on)
        {
            ImGui::TextWrapped("Solo para cuando juegas tú: el agente está activo (F11 lo para). El agente nunca se "
                               "teletransporta; usa solo las entradas, escaleras y portales del juego.");
            return;
        }
        ImGui::TextWrapped("En el mapa (tecla M): Alt + clic izquierdo lleva al héroe a ese punto.");
        if (ImGui::Button("Aquí##tp"))
        {
            s_x = hx;
            s_y = hy;
            s_layer = hl;
        }
        ImGui::SameLine();
        ImGui::SetNextItemWidth(220);
        ImGui::InputInt3("Casilla x, y, capa##tp", &s_x);
        const std::vector<Teleports::Interior>& all = Teleports::interiors();
        if (!all.empty())
        {
            char label[96];
            std::snprintf(label, sizeof label, "%s", s_pick >= 0 && s_pick < static_cast<int>(all.size()) ? "elegido" : "un interior conocido");
            ImGui::SetNextItemWidth(260);
            if (ImGui::BeginCombo("Interiores##tp", label))
            {
                for (int i = 0; i < static_cast<int>(all.size()); ++i)
                {
                    const Teleports::Interior& in = all[i];
                    char item[96];
                    std::snprintf(item, sizeof item, "%s %d,%d (fuera %d,%d)##tp%d", in.start ? "salto" : "interior", in.inX,
                                  in.inY, in.outX, in.outY, i);
                    if (ImGui::Selectable(item, s_pick == i))
                    {
                        s_pick = i;
                        s_x = in.inX;
                        s_y = in.inY;
                        s_layer = hl;
                    }
                }
                ImGui::EndCombo();
            }
        }
        if (ImGui::Button("Teletransportar##tp") && !Teleports::playerTeleport(s_x, s_y, s_layer))
        {
            LOG("Teleports: the player's teleport to {},{} (layer {}) refused", s_x, s_y, s_layer);
        }
    }

    // The ModKit menu's section: what changes applies at once.
    void drawMenu()
    {
        Config::AutoAttack& c = Config::autoAttack;
        if (ImGui::Checkbox("Activo ahora", &g_on))
        {
            LOG("AutoAttack: {} (menu)", g_on ? "on" : "off");
        }
        ImGui::SetItemTooltip("Lo mismo que la tecla F11.");
        ImGui::Checkbox("Activo al arrancar", &c.enabled);
        int mode = c.seek ? 1 : 0;
        ImGui::TextUnformatted("Contra quién lucha:");
        ImGui::RadioButton("Solo quien me ataca (y a quien ataco yo)", &mode, 0);
        ImGui::RadioButton("Buscar combate (cualquier enemigo en el radio)", &mode, 1);
        c.seek = mode == 1;
        ImGui::Checkbox("Explorar cuando no hay nadie", &c.roam);
        ImGui::SetItemTooltip("Paso a paso hacia lo que aún no ha visto (el mapa del agente), con la vida por encima del 60 %%.");
        ImGui::SliderInt("Paso al explorar (casillas)", &c.roamStep, 1, 20);
        ImGui::SetItemTooltip("Lo lejos que va en cada paso al explorar: más largo, explora más rápido; "
                              "el buscador de caminos rodea lo que no se puede pisar.");
        ImGui::Checkbox("Usar el cursor del juego, como un jugador", &c.humanCursor);
        ImGui::SetItemTooltip("Cada acción espera a que el cursor del juego llegue a su objetivo, movido como la mano de "
                              "un buen jugador: reacción, movimiento rápido y alguna corrección. El ratón de Windows no "
                              "se mueve.");
        ImGui::Checkbox("Ir a la misión activa", &c.quests);
        ImGui::SetItemTooltip("Sin combate cerca, va al destino de la misión (la principal primero, si no la más "
                              "cercana), sin límite de distancia; allí explora alrededor.");
        ImGui::Checkbox("Ir a por cofres sin abrir", &c.chests);
        ImGui::SetItemTooltip("Sin misión a la que ir ni enemigos cerca, va al cofre sin abrir más cercano (hasta 150 "
                              "casillas); si no llega en 90 s, lo deja.");
        ImGui::Checkbox("Ir a zonas de farmeo", &c.farm);
        ImGui::SetItemTooltip("Sin misión que hacer ni enemigos cerca, va a la zona con más enemigos de su nivel (lo más "
                              "cerca posible) y explora allí.");
        ImGui::Checkbox("Seguir jugando en segundo plano", &c.background);
        ImGui::SetItemTooltip("El agente sigue con la ventana del juego sin foco (no usa tu ratón ni tu teclado).");
        // The same switches as in the tactics section, here with the fight.
        ImGui::Checkbox("Usar habilidades (artes de combate)##fight", &Config::tactics.arts);
        ImGui::Checkbox("Usar consumibles##fight", &Config::tactics.consumables);
        ImGui::Checkbox("El agente recoge el botín", &c.pickup);
        ImGui::SetItemTooltip("Con su propia recogida (no usa la tecla A, que queda como en el juego): objetos del "
                              "suelo, cofres, escondites y pozos del radio, uno a uno, sin combate cerca.");
        ImGui::BeginDisabled(!c.pickup);
        ImGui::Checkbox("Recoger antes que luchar (sin peligro de morir)", &c.lootInFight);
        ImGui::SetItemTooltip("Con el 60 % de vida o más, recoge primero y luego lucha; con menos, solo lo que esté más cerca que el enemigo "
                              "(uno, y vuelve a la pelea).");
        {
            static const char* kGrades[] = {"Todo (desde blanco)", "Desde azul (mágico)", "Desde amarillo (raro)",
                                            "Solo dorado (único)"};
            ImGui::Combo("Equipo que recoge", &c.minRarity, kGrades, 4);
            ImGui::SetItemTooltip("El equipo por debajo de este grado se queda en el suelo; pociones, runas y oro siempre.");
            ImGui::SliderInt("Oro suficiente por nivel", &c.rarityGoldPerLevel, 0, 20000);
            ImGui::SetItemTooltip("El filtro solo actúa con este oro por nivel del héroe; con menos, recoge todo el "
                                  "equipo para equiparse y venderlo.");
            ImGui::Checkbox("Siempre las piezas de set (verde)", &c.keepSets);
        }
        ImGui::Checkbox("También sin el auto ataque activo", &c.autoCollect);
        ImGui::SetItemTooltip("Apagado: solo recoge tras los combates que hace por ti.");
        ImGui::EndDisabled();
        ImGui::SliderInt("Radio de ataque (px)", &c.range, 100, 1500);
        ImGui::SliderInt("Radio de recogida (px)", &c.lootRange, 100, 3000);
        ImGui::SliderInt("Pausa tras tu clic (ms)", &c.pauseMs, 0, 3000);
        ImGui::SliderInt("Repetir orden (ms)", &c.repeatMs, 0, 3000);
        ImGui::SetItemTooltip("Cada cuánto se repite la orden de ataque; 0 = una sola vez por objetivo.");
    }

    void saveMenu(const std::wstring& ini)
    {
        const Config::AutoAttack& c = Config::autoAttack;
        ModkitMenu::write(ini, L"AutoAttack", L"Enabled", c.enabled);
        ModkitMenu::write(ini, L"AutoAttack", L"Seek", c.seek);
        ModkitMenu::write(ini, L"AutoAttack", L"Roam", c.roam);
        ModkitMenu::write(ini, L"AutoAttack", L"RoamStep", c.roamStep);
        ModkitMenu::write(ini, L"AutoAttack", L"Quests", c.quests);
        ModkitMenu::write(ini, L"AutoAttack", L"HumanCursor", c.humanCursor);
        ModkitMenu::write(ini, L"AutoAttack", L"Background", c.background);
        ModkitMenu::write(ini, L"AutoAttack", L"Farm", c.farm);
        ModkitMenu::write(ini, L"AutoAttack", L"Chests", c.chests);
        ModkitMenu::write(ini, L"AutoAttack", L"LootInFight", c.lootInFight);
        ModkitMenu::write(ini, L"AutoAttack", L"MinRarity", c.minRarity);
        ModkitMenu::write(ini, L"AutoAttack", L"KeepSets", c.keepSets);
        ModkitMenu::write(ini, L"AutoAttack", L"RarityGoldPerLevel", c.rarityGoldPerLevel);
        ModkitMenu::write(ini, L"AutoAttack", L"Pickup", c.pickup);
        ModkitMenu::write(ini, L"AutoAttack", L"AutoCollect", c.autoCollect);
        ModkitMenu::write(ini, L"AutoAttack", L"Range", c.range);
        ModkitMenu::write(ini, L"AutoAttack", L"LootRange", c.lootRange);
        ModkitMenu::write(ini, L"AutoAttack", L"Pause", c.pauseMs);
        ModkitMenu::write(ini, L"AutoAttack", L"Repeat", c.repeatMs);
    }
}

namespace
{
    // The portal box opens when the hero steps on a portal (on the way to loot, an enemy, a quest) and holds the
    // whole game in its modal loop: no frames, so onFrame cannot see it. A thread of its own closes it (Escape, the
    // box's Cancel) once it has stood 1.5 s with the agent on; the player's own portal trips are theirs.
    // Read from the watcher's own thread, so guarded (the code reviewer, E4): the UI manager or its window being
    // replaced meanwhile reads as «not open».
    bool escapeMenuVisible()
    {
        __try
        {
            cUI_Manager* ui = cUI_Manager::instance();
            cUI_Window2* menu = ui && (ui->flags & cUI_Manager::inGame) && !(ui->flags & cUI_Manager::inMenus)
                                    ? ui->window(cUI_Manager::Window::escapeMenu)
                                    : nullptr;
            return menu && menu->visible();
        }
        __except (EXCEPTION_EXECUTE_HANDLER)
        {
            return false;
        }
    }

    // The game menu (Escape) open under the agent (A7, 2026-11-15: «el agente entra en el menú de pausa, impidiendo
    // continuar el entrenamiento»): closed with Escape once it has stood 3 s. The player's own is never closed (the
    // code reviewer, E1: clicks alone do not tell it): a menu that came up within 2.5 s of a physical Escape, or
    // that sees a physical key or click of the player's while open, is theirs until it shuts.
    // The player's own keys and buttons, sampled every 50 ms by the watcher's thread (the code reviewer, E9: a press
    // lasts 80-150 ms, a look every 500 ms missed four in five). The physical state is the whole system's: it counts
    // only with this game in front (a copy playing without the focus would otherwise take the player's clicks in
    // another program for theirs). physicallyDown and playerClicks keep no state, so two threads may call them; keep
    // them on the 0x8000 bit (the low bit is shared by every caller).
    std::atomic<DWORD> g_physicalEscAt{0}, g_physicalInputAt{0};

    void sampleInput()
    {
        DWORD frontPid = 0;
        GetWindowThreadProcessId(GetForegroundWindow(), &frontPid);
        if (frontPid != GetCurrentProcessId())
        {
            return;
        }
        const DWORD now = GetTickCount();
        if (physicallyDown(VK_ESCAPE))
        {
            g_physicalEscAt = now;
            g_physicalInputAt = now;
        }
        else if (playerClicks() || physicallyDown(VK_RETURN))
        {
            g_physicalInputAt = now;
        }
    }

    void watchEscapeMenu(DWORD now, bool on, DWORD& since, DWORD& toldAt)
    {
        static bool s_players = false;
        const bool open = on && escapeMenuVisible();
        if (!open)
        {
            since = 0;
            s_players = false;
            return;
        }
        if (!since)
        {
            since = now;
            const DWORD esc = g_physicalEscAt;
            s_players = esc && now - esc < 2500;
        }
        const DWORD input = g_physicalInputAt;
        if (input && static_cast<int>(input - since) >= 0)
        {
            s_players = true;
        }
        if (s_players)
        {
            return;
        }
        if (now - since > 3000 && now - toldAt > 3000 &&
            Act::allowed(Act::Kind::Windows, "close the game menu opened under the agent"))
        {
            toldAt = now;
            LOG("AutoAttack: the game menu is open under the agent: closed (Escape)");
            Inject::key(VK_ESCAPE, true);
            Inject::key(VK_ESCAPE, false);
        }
    }

    // The box read from the watcher's thread, guarded as escapeMenuVisible.
    unsigned portalBoxRows()
    {
        __try
        {
            return UiNav::portalBoxMask();
        }
        __except (EXCEPTION_EXECUTE_HANDLER)
        {
            return 0;
        }
    }

    bool portalRowPoint(int portal, float& x, float& y)
    {
        __try
        {
            return UiNav::portalRow(portal, x, y);
        }
        __except (EXCEPTION_EXECUTE_HANDLER)
        {
            return false;
        }
    }

    void watchPortalBox()
    {
        DWORD since = 0, toldAt = 0, menuSince = 0, menuToldAt = 0;
        for (;;)
        {
            for (int i = 0; i < 10; ++i)
            {
                Sleep(50);
                sampleInput();
            }
            const bool on = *static_cast<volatile bool*>(&g_on);
            watchEscapeMenu(GetTickCount(), on, menuSince, menuToldAt);
            if (!on || !UiNav::portalBoxOpen())
            {
                since = 0;
                continue;
            }
            const DWORD now = GetTickCount();
            const unsigned rows = portalBoxRows();
            if (!since)
            {
                since = now;
                LOG("AutoAttack: the portal box is open (rows {:x}, the hero's portals {:x}, trip {} -> {})", rows,
                    Portals::joined(), Portals::armedFrom(), Portals::armedTo());
                continue;
            }
            // A portal trip: its destination's row clicked once the box has drawn (the row's text placed), as the
            // player clicks it. The box closes and the game sends the hero there.
            const int to = Portals::armedTo();
            const DWORD clicked = Portals::clickedAt();
            if (to >= 0 && !clicked && now - since > 700)
            {
                float cx = 0.0f, cy = 0.0f;
                if ((rows & (1u << to)) && portalRowPoint(to, cx, cy) &&
                    Act::allowed(Act::Kind::Portals, "pick the destination in the portal box"))
                {
                    LOG("AutoAttack: portal box: the row of portal {} clicked at {:.0f},{:.0f} (rows {:x})", to, cx, cy, rows);
                    Portals::clicked(now);
                    Controller::clickAt(static_cast<int>(cx), static_cast<int>(cy));
                    toldAt = now;
                    continue;
                }
                if (now - toldAt > 2000)
                {
                    LOG("AutoAttack: portal box: portal {} cannot be picked (rows {:x}){}", to, rows,
                        rows & (1u << to) ? ", its row not placed" : ", not joined");
                }
            }
            if (clicked && now - clicked < 3000)
            {
                continue;   // the click's turn first
            }
            if (now - since > 1500 && now - toldAt > 2000)
            {
                toldAt = now;
                if (Act::allowed(Act::Kind::Windows, "close the portal box opened under the agent"))
                {
                    LOG("AutoAttack: the portal box opened under the agent (rows {:x}, the hero's portals {:x}): closed",
                        rows, Portals::joined());
                    Inject::key(VK_ESCAPE, true);
                    Inject::key(VK_ESCAPE, false);
                }
            }
        }
    }
}

void AutoAttack::install()
{
    std::thread(&watchPortalBox).detach();
    // The controller installs the world pick hook; without it, we do.
    if (!Config::controller.enabled)
    {
        AimAssist::install();
    }
    g_on = Config::autoAttack.enabled;
    ModkitMenu::add({"Ataque automático", &drawMenu, &saveMenu});
    ModkitMenu::add({"Lo que lee el agente", &Lore::drawMenu, nullptr});
    ModkitMenu::add({"Misiones del agente", &drawQuestBook, nullptr});
    ModkitMenu::add({"Dónde está el héroe", &Whereabouts::drawMenu, nullptr});
    ModkitMenu::add({"Zona del agente", &drawZone, nullptr});
    ModkitMenu::add({"Teletransporte (solo jugador)", &drawTeleport, nullptr});
    AgentOverlay::install();
    Teleports::install();
    GrannyAsync::installModelGuard();
    Tactics::install();
    LOG("AutoAttack: {} (key 0x{:x}, range {} px, pause {} ms, repeat {} ms)", g_on ? "on" : "off",
        Config::autoAttack.key, Config::autoAttack.range, Config::autoAttack.pauseMs, Config::autoAttack.repeatMs);
}

// The intent and its reason in Spanish, for the player's overlay (the log keeps English).
static std::string intentSpanish()
{
    static const char* const names[] = {"Explorar", "Farmear", "Misión", "Tienda", "Recuperarse", "Escapar"};
    static const std::pair<const char*, const char*> reasons[] = {
        {"low on health", "poca vida, sin poción o pelea prevista perdida: retrocede"},
        {"shut in", "encerrado: primero las puertas, luego la salida"},
        {"the backpack full", "mochila llena o sin pociones de curación: a un mercader"},
        {"the quest's ground is levels", "la zona de la misión es de más nivel: farmear antes"},
        {"a quest creature", "hablar con un personaje de la misión"},
        {"a quest's goal", "ir al objetivo de la misión"},
        {"the quest's goal inside", "el objetivo está dentro de una casa: a su puerta"},
        {"no quest to see to", "sin misión: experiencia donde los enemigos son de su nivel"},
        {"at the quest's goal", "en el objetivo de la misión: mira alrededor"},
        {"nothing to see to", "descubrir terreno, recoger botín, luchar solo si le atacan"},
        {"an interior of its level", "un interior de su nivel cerca: entra a explorarlo"},
    };
    std::string text = names[std::clamp(static_cast<int>(g_intent), 0, 5)];
    for (const auto& [en, es] : reasons)
    {
        if (g_intentWhy.rfind(en, 0) == 0)
        {
            return text + ": " + es;
        }
    }
    return g_intentWhy.empty() ? text : text + ": " + g_intentWhy;
}

// The agent's overlay over the world (AgentOverlay): what it is about, where it goes, what it fights, the aggro reach.
static void publishOverlay(DWORD now, cCreature* self, float sx, float sy)
{
    using AgentOverlay::Layer;
    AgentOverlay::begin(self->x, self->y, sx, sy);
    cObjectManager* objects = cObjectManager::instance();
    // The scale: the target, else the first foe on screen.
    {
        float tx = 0, ty = 0;
        bool scaled = false;
        if (g_target && objects)
        {
            if (cCreature* t = objects->creature(g_target); t && AimAssist::screenOf(g_target, tx, ty))
            {
                AgentOverlay::calibrate(t->x, t->y, tx, ty);
                scaled = true;
            }
        }
        for (size_t i = 0; i < g_aggroFoes.size() && !scaled && i < 12; ++i)
        {
            if (AimAssist::screenOf(g_aggroFoes[i].id, tx, ty))
            {
                AgentOverlay::calibrate(g_aggroFoes[i].x, g_aggroFoes[i].y, tx, ty);
                scaled = true;
            }
        }
    }
    if (AgentOverlay::shown(Layer::Intent))
    {
        static const uint32_t colors[] = {IM_COL32(120, 200, 255, 255), IM_COL32(255, 200, 60, 255),
                                          IM_COL32(120, 255, 120, 255), IM_COL32(255, 160, 255, 255),
                                          IM_COL32(255, 120, 90, 255), IM_COL32(255, 80, 80, 255)};
        AgentOverlay::heroText(intentSpanish(),
                               colors[std::clamp(static_cast<int>(g_intent), 0, 5)]);
    }
    if (AgentOverlay::shown(Layer::Aggro))
    {
        int drawn = 0;
        for (const AggroFoe& f : g_aggroFoes)
        {
            if (std::hypot(static_cast<double>(f.x - self->x), static_cast<double>(f.y - self->y)) < 30.0 * kTileSize &&
                ++drawn <= 24)
            {
                AgentOverlay::ring(f.x, f.y, 11.2f, f.onHero ? IM_COL32(255, 60, 60, 200) : IM_COL32(255, 160, 40, 110),
                                   f.onHero ? 2.0f : 1.0f);
            }
        }
    }
    if (AgentOverlay::shown(Layer::Route))
    {
        if (g_questTravel && (g_questX || g_questY))
        {
            AgentOverlay::way(g_questX, g_questY, IM_COL32(120, 255, 120, 230),
                              g_intent == Intent::Shop ? "tienda" : "misión");
        }
        else if (ClickWalk::walking() && (g_walkX || g_walkY))
        {
            AgentOverlay::way(g_walkX, g_walkY, IM_COL32(120, 200, 255, 200), "paso");
        }
    }
    if (AgentOverlay::shown(Layer::Doors) && g_doorAt && now - g_doorAt < 5000)
    {
        AgentOverlay::way(g_doorX, g_doorY, IM_COL32(200, 90, 255, 240), "puerta");
        AgentOverlay::ring(g_doorX, g_doorY, 1.0f, IM_COL32(200, 90, 255, 240), 2.5f);
    }
    if (AgentOverlay::shown(Layer::Target) && g_target)
    {
        if (float tx = 0, ty = 0; AimAssist::screenOf(g_target, tx, ty))
        {
            AgentOverlay::around(tx, ty, 26.0f, g_collecting ? IM_COL32(255, 230, 60, 230) : IM_COL32(255, 60, 60, 230));
        }
    }
    AgentOverlay::end(now);
}

// The agent's mind map: a note for Obsidian (Mermaid mindmap) rewritten every 3 s, the agent on or off ([Mind] Path,
// default SacredBild-mente.md next to the game). Off, it shows what it would do if switched on.
static std::string mindSafe(std::string text)
{
    for (char& c : text)
    {
        if (c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' || c == '"' || c == '`')
        {
            c = ' ';
        }
    }
    return text;
}

static void writeMind(DWORD now, cCreature* self, int layer, int heroLevel)
{
    static DWORD s_at = 0;
    static std::wstring s_path;
    if (s_at && now - s_at < 3000)
    {
        return;
    }
    s_at = now;
    if (s_path.empty())
    {
        wchar_t exe[MAX_PATH] = {};
        GetModuleFileNameW(nullptr, exe, MAX_PATH);
        std::wstring dir = exe;
        dir = dir.substr(0, dir.find_last_of(L"\\/") + 1);
        wchar_t path[MAX_PATH] = {};
        GetPrivateProfileStringW(L"Mind", L"Path", L"", path, MAX_PATH, (dir + L"SacredBild.ini").c_str());
        s_path = path[0] ? path : dir + L"SacredBild-mente.md";
        char narrow[MAX_PATH * 2] = {};
        WideCharToMultiByte(CP_UTF8, 0, s_path.c_str(), -1, narrow, sizeof narrow, nullptr, nullptr);
        LOG("AutoAttack: the agent's mind map to {}", narrow);
    }
    std::string m;
    const auto node = [&](int depth, const std::string& text) {
        m += std::string(2 * depth, ' ') + mindSafe(text) + "\n";
    };
    SYSTEMTIME t;
    GetLocalTime(&t);
    char at[16];
    std::snprintf(at, sizeof at, "%02d:%02d:%02d", t.wHour, t.wMinute, t.wSecond);
    m += std::string("---\nactualizado: ") + at + "\n---\n# Mente del agente\n\n";
    m += g_on ? "Activo (F11). Lo que piensa y por qué.\n\n"
              : "Inactivo (F11 lo enciende). Lo que haría si lo encendieras.\n\n";
    m += "```mermaid\nmindmap\n";
    m += std::format("  root((Héroe nivel {} · {}))\n", heroLevel, g_on ? "activo" : "inactivo");
    // Intent: the one it follows, or the one it would take.
    int32_t qx = 0, qy = 0;
    double qr = 0.0;
    uint32_t who = 0;
    const bool quest = questTarget(self->x, self->y, qx, qy, qr, who);
    const double questTiles = quest ? std::hypot(static_cast<double>(qx - self->x), static_cast<double>(qy - self->y)) / kTileSize : 0.0;
    node(2, g_on ? "Intención" : "Haría");
    if (g_on)
    {
        node(3, intentSpanish());
        node(3, g_intentSince ? std::format("desde hace {} s", (now - g_intentSince) / 1000) : std::string("aún sin decidir"));
    }
    else
    {
        node(3, Gear::wantsShop() ? "Tienda: mochila llena o sin pociones"
                : quest           ? std::format("Misión a {:.0f} casillas", questTiles)
                : g_farmKnown     ? "Farmear donde los enemigos son de su nivel"
                                  : "Explorar lo que no ha visto");
    }
    node(2, "Opciones");
    node(3, quest ? std::format("Misión: a {:.0f} casillas{}", questTiles, who ? ", hablar con alguien" : "")
                  : "Misión: ninguna a la vista");
    node(3, g_farmKnown ? std::format("Farmear: zona a {:.0f} casillas",
                                      std::hypot(static_cast<double>(g_farmX - self->x), static_cast<double>(g_farmY - self->y)) / kTileSize)
                        : "Farmear: zona aún sin elegir");
    node(3, std::format("Tienda: {}, {} pociones", Gear::wantsShop() ? "hace falta" : "no hace falta",
                        std::max(0, Gear::healingLeft())));
    node(3, std::format("Explorar: {} celdas vistas en esta capa", MapMemory::cellsOn(layer)));
    node(2, "Combate");
    if (const CombatLearn::Forecast& fc = CombatLearn::forecast(); fc.foes > 0)
    {
        node(3, std::format("{} enemigos, ganar {:.0f} %", fc.foes, fc.win * 100.0f));
        node(3, std::format("perdería {:.0f} % de vida en {:.0f} s", fc.expected * 100.0f, fc.seconds));
    }
    else
    {
        node(3, "nadie con quien pelear");
    }
    int after = 0;
    for (const AggroFoe& f : g_aggroFoes)
    {
        after += f.onHero ? 1 : 0;
    }
    node(3, std::format("aggro: {} cerca, {} a por él", g_aggroFoes.size(), after));
    node(2, "Mundo");
    if (g_zone.valid)
    {
        node(3, std::format("zona región {}, niveles {}-{}", g_zone.region, g_zone.lo, g_zone.hi));
        node(3, std::format("{} misiones, {} enemigos, {} cofres", g_zone.quests, g_zone.enemies, g_zone.chests));
    }
    node(3, std::format("capa {}, casilla {},{}", layer, static_cast<int>(self->x / kTileSize), static_cast<int>(self->y / kTileSize)));
    node(2, "Recuerda");
    for (auto it = g_decisions.rbegin(); it != g_decisions.rend() && it - g_decisions.rbegin() < 4; ++it)
    {
        node(3, *it);
    }
    m += "```\n\n## Últimas decisiones\n\n";
    for (auto it = g_decisions.rbegin(); it != g_decisions.rend(); ++it)
    {
        m += "- " + *it + "\n";
    }
    // Written whole and swapped in, so Obsidian never reads half a note.
    const std::wstring tmp = s_path + L".tmp";
    if (FILE* f = _wfopen(tmp.c_str(), L"wb"))
    {
        std::fwrite(m.data(), 1, m.size(), f);
        std::fclose(f);
        MoveFileExW(tmp.c_str(), s_path.c_str(), MOVEFILE_REPLACE_EXISTING);
    }
}

bool AutoAttack::on()
{
    return g_on;
}

// The agent knows when it is stuck (the player, 2026-11-11: «el agente tiene que identificar cuando está atascado, y
// avisarte para que revises el motivo del atasco»): 150 s in the game world with no progress of any kind (not 6 tiles
// from where it stood, no blow that told, no loot taken, no quest done), not in a shop or a load, alive. Then a report
// line to SacredBild-stuck.txt beside the game (read by the coordinator's watcher, which looks into it) and to the log
// (the mosaic shows it). Again only after 10 min, or once it got going and stuck 20 tiles elsewhere.
static void watchStuck(DWORD now, const cCreature* self)
{
    static int32_t s_x = 0, s_y = 0;
    static DWORD s_since = 0, s_hurt = 0, s_loot = 0, s_quests = 0, s_toldAt = 0;
    static int32_t s_toldX = 0, s_toldY = 0;
    const bool moved = std::hypot(static_cast<double>(self->x - s_x), static_cast<double>(self->y - s_y)) > 6 * kTileSize;
    // A shop open over 3 min is no business of a player's (A1, 2026-11-11: its trade flag left set by a death in the
    // shop kept this from ever telling).
    static DWORD s_shopSince = 0;
    const bool shop = Gear::shopOpen();
    s_shopSince = shop ? (s_shopSince ? s_shopSince : now) : 0;
    const bool busy = AgentSave::worldChanging() || (shop && now - s_shopSince < 180000) || !heroAlive();
    // Idle though moving (the live verifier and the stuck solver, 2026-11-13: A2, a new Gladiator shut in the
    // colosseum, 66 min with no experience, walking the yard, which started the clock above again each time): 15 min
    // with neither a fight, a pick up nor a quest done is told as stuck; 25 min, the last save is loaded (as for 5 min
    // on one spot).
    {
        static DWORD s_idleSince = 0, s_idleTarget = 0, s_idleLoot = 0, s_idleQuests = 0, s_idleTold = 0;
        if (!s_idleSince || busy || g_lastTargetAt != s_idleTarget || g_lootCount != s_idleLoot || g_questsDoneAt != s_idleQuests)
        {
            s_idleSince = now;
            s_idleTarget = g_lastTargetAt;
            s_idleLoot = g_lootCount;
            s_idleQuests = g_questsDoneAt;
            s_idleTold = 0;
        }
        else if (now - s_idleSince > 900000 && !s_idleTold)
        {
            s_idleTold = now;
            LOG("AgentStuck: 15 min with neither a fight, a pick up nor a quest done (layer {}), though moving",
                reinterpret_cast<const uint8_t*>(self)[0x24]);
            Findings::note("stuck", self->x, self->y, "15 min with neither a fight, a pick up nor a quest done");
        }
        else if (now - s_idleSince > 1500000)
        {
            LOG("AgentStuck: 25 min with neither a fight, a pick up nor a quest done: the last save loaded");
            s_idleSince = now;
            AgentSave::reloadStuck();
        }
    }
    if (!s_since || moved || busy || g_lastHurtAt != s_hurt || g_lootCount != s_loot || g_questsDoneAt != s_quests)
    {
        s_x = self->x;
        s_y = self->y;
        s_since = now;
        s_hurt = g_lastHurtAt;
        s_loot = g_lootCount;
        s_quests = g_questsDoneAt;
        return;
    }
    // Escalated (the stuck solver, 2026-11-11, A3 35 min and A2 10 min still on open ground after taking a horse): at
    // 20 s still on horseback off it (the solver, 2026-11-12: a 2-tile lane at 3189,2812 held A1, A3 and A6 mounted
    // 90 s each time; a player gets off at once), at 5 min the last save loaded.
    static DWORD s_offFor = 0, s_reloadFor = 0;
    // The stuck solver, 2026-11-13 (67 of these in an hour, A8 from 1 to 24 an hour): 20 s in the saddle, not 20 s
    // still of which the last second mounted (the wait for a companion, a shop, a pick up, then up); only on a walk
    // that goes nowhere, not looking around a quest's goal within 2-3 tiles (that is no jam); and 5 min on foot after
    // it, not one (down, up again, down: a loop).
    static DWORD s_mountedSince = 0;
    const bool mountedNow = HeroProfile::current().mounted;
    s_mountedSince = mountedNow ? (s_mountedSince ? s_mountedSince : now) : 0;
    if (now - s_since >= 20000 && s_offFor != s_since && mountedNow && now - s_mountedSince >= 20000 &&
        (ClickWalk::routing() || g_questTravel))
    {
        s_offFor = s_since;
        g_onFootUntil = now + 300000;
        LOG("AgentStuck: 20 s in one place on horseback (layer {}): off the horse", reinterpret_cast<const uint8_t*>(self)[0x24]);
    }
    if (now - s_since >= 300000 && s_reloadFor != s_since)
    {
        s_reloadFor = s_since;
        LOG("AgentStuck: 5 min in one place (layer {}): the last save loaded", reinterpret_cast<const uint8_t*>(self)[0x24]);
        AgentSave::reloadStuck();
    }
    if (now - s_since < 150000)
    {
        return;
    }
    const bool elsewhere =
        std::hypot(static_cast<double>(self->x - s_toldX), static_cast<double>(self->y - s_toldY)) > 20 * kTileSize;
    if (s_toldAt && now - s_toldAt < 600000 && !elsewhere)
    {
        return;
    }
    s_toldAt = now;
    s_toldX = self->x;
    s_toldY = self->y;
    const HeroProfile::Data hero = HeroProfile::current();
    const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
    SYSTEMTIME t;
    GetLocalTime(&t);
    const std::string line = std::format(
        "{:02d}:{:02d}:{:02d} | {} nivel {} | casilla {},{} capa {} | {} | mision {},{} | objetivo {:x} | {} s sin avanzar",
        t.wHour, t.wMinute, t.wSecond, HeroProfile::className(hero.cls), hero.level, static_cast<int>(self->x / kTileSize),
        static_cast<int>(self->y / kTileSize), layer, intentSpanish(), static_cast<int>(g_questX / kTileSize),
        static_cast<int>(g_questY / kTileSize), g_target, (now - s_since) / 1000);
    LOG("AgentStuck: {}", line);
    wchar_t exe[MAX_PATH] = {};
    GetModuleFileNameW(nullptr, exe, MAX_PATH);
    std::wstring path = exe;
    path = path.substr(0, path.find_last_of(L"\\/") + 1) + L"SacredBild-stuck.txt";
    if (FILE* f = _wfopen(path.c_str(), L"ab"))
    {
        std::fwrite(line.data(), 1, line.size(), f);
        std::fwrite("\r\n", 1, 2, f);
        std::fclose(f);
    }
}

// Fighting at the weapon's distance (the player, 2026-11-11: «las armas con mayor distancia de rango son para atacar
// desde lo más lejos posible, y las de cuerpo a cuerpo son más eficientes en distancias cortas»; «no he visto el combate
// a distancia»). With a bow, crossbow, throwing weapon or gun an enemy that comes within 3 tiles gets a step back, to
// about 6 tiles off, away from where the enemies stand, as a good player keeps his distance and shoots again. Not when
// shut in, not more than 4 steps in 30 s (cornered, it fights where it stands), and never with low health on a dead end.
// Melee weapons (and the staff or spear, whose reach the game's own walk-up already strikes from) close in as before.
// True: a step back went out (no attack order this time).
static bool keepDistance(DWORD now, uint32_t id)
{
    static DWORD s_stepUntil = 0;
    static DWORD s_steps[4] = {};
    static int s_next = 0;
    if (s_stepUntil && static_cast<int>(now - s_stepUntil) < 0)
    {
        return true;    // the step under way: let it be walked
    }
    const HeroProfile::Data hero = HeroProfile::current();
    // The Battle Mage kites as the archers do (docs/Mentalidades.md §1: «Far», kite, 8 tiles): his spells reach
    // as far, his health is the thinnest.
    // The class's plan may say otherwise ([Distance] Kite: 0 never, 1 always; docs/Planes-de-combate.md).
    const Mind::Plan& cp = Mind::plan();
    // Not with the melee weapon in hand (the stuck solver, 2026-11-16, A3 since 09:10: 204 steps back in 95 min with the
    // weapon kind 4 «cuerpo a cuerpo», the art 200 a weapon art; the fights that had a step back made 12,4 exp/s against
    // 14,1 of the others, and 15,5 against 20,5 from 04:00 to 09:10).
    const bool kites = cp.kite >= 0 ? cp.kite == 1
                                    : (hero.ranged || (hero.cls == HeroProfile::Class::BattleMage && hero.weaponKind != 4));
    if (!hero.valid || !kites || hero.mounted || Whereabouts::area().shutIn)
    {
        return false;
    }
    cObjectManager* objects = cObjectManager::instance();
    cEngine* engine = FrameHooks::engine();
    cCreature* self = objects && engine ? objects->creature(engine->controlled) : nullptr;
    if (!self)
    {
        return false;
    }
    // The enemies near, by the world: the nearest and where they stand together.
    AimAssist::Foe foes[16];
    const int count = AimAssist::enemies(static_cast<float>(Config::autoAttack.range), foes, 16);
    double nearest = 1e9, cx = 0, cy = 0, weight = 0;
    for (int i = 0; i < count; ++i)
    {
        const cObject* o = objects->object(foes[i].id);
        if (!o)
        {
            continue;
        }
        const double dx = o->x - static_cast<double>(self->x), dy = o->y - static_cast<double>(self->y);
        const double d = std::hypot(dx, dy) / kTileSize;
        nearest = std::min(nearest, d);
        if (d < 6.0)
        {
            const double w = 1.0 / std::max(d, 0.5);
            cx += dx * w;
            cy += dy * w;
            weight += w;
        }
    }
    if (nearest >= cp.tooCloseTiles || weight <= 0)
    {
        return false;
    }
    int recent = 0;
    for (DWORD at : s_steps)
    {
        recent += at && now - at < 30000;
    }
    // Cornered (no more steps back, or no way back below): the weapon for the close fight, if a slot has one.
    static DWORD s_closeAt = 0;
    const auto closeIn = [&] {
        if (now - s_closeAt > 3000 && Gear::chooseWeaponFor(id))
        {
            s_closeAt = now;
            LOG("AutoAttack: cornered {:.1f} tiles from an enemy: the close weapon", nearest);
        }
    };
    if (recent >= cp.stepsPer30s)
    {
        closeIn();
        return false;
    }
    // Away from them, turned aside up to 90 degrees when that way is a wall or a fence.
    const double away = std::atan2(-cy, -cx);
    const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
    for (double turn : {0.0, 0.5, -0.5, 1.0, -1.0, 1.57, -1.57})
    {
        const double a = away + turn;
        const double tx = self->x / kTileSize + std::cos(a) * cp.stepTiles,
                     ty = self->y / kTileSize + std::sin(a) * cp.stepTiles;
        bool clear = true;
        for (int k = 1; k <= 8 && clear; ++k)
        {
            clear = ClickWalk::walkable(layer, static_cast<int>(self->x / kTileSize + std::cos(a) * k * 0.5),
                                        static_cast<int>(self->y / kTileSize + std::sin(a) * k * 0.5)) != 0;
        }
        if (!clear || Whereabouts::reachable(static_cast<int>(tx), static_cast<int>(ty)) == 0)
        {
            continue;
        }
        if (!Act::allowed(Act::Kind::Retreat, "keep the distance from a melee enemy"))
        {
            return false;
        }
        g_walkX = static_cast<int32_t>(tx * kTileSize);
        g_walkY = static_cast<int32_t>(ty * kTileSize);
        sendWalk();
        s_steps[s_next] = now;
        s_next = (s_next + 1) % 4;
        s_stepUntil = now + 700 + jitter(0, 250);
        g_keptDistanceAt = now;
        LOG("AutoAttack: keeping the distance (weapon kind {}): an enemy {:.1f} tiles off, a step back to {:.0f},{:.0f}, "
            "then {:x} again",
            hero.weaponKind, nearest, tx, ty, id);
        return true;
    }
    closeIn();
    return false;
}

void AutoAttack::onFrame()
{
    Teleports::onFrame();
    // The game's cinema mode (cUI_Manager +8 bit 0x10, the script's SetCinemaMode; Manolito, block M): not to be
    // skipped (the hero held for the script's NPC_Goto, MoveOver, Teleport); the agent stands, only noted here.
    if (cUI_Manager* ui = cUI_Manager::instance())
    {
        static bool s_cinema = false;
        const bool cinema = (ui->flags & cUI_Manager::cinematic) != 0;
        if (cinema != s_cinema)
        {
            s_cinema = cinema;
            LOG("AutoAttack: cinema mode {} (the script's scene: the agent stands)", cinema ? "on" : "off");
        }
    }
    // Menus present from the UI thread, the game from the render thread; around loading both may.
    static std::mutex frameLock;
    const std::unique_lock lock(frameLock, std::try_to_lock);
    if (!lock)
    {
        return;
    }
    const DWORD now = GetTickCount();
    // The player's keys and clicks only while the game has the focus; the agent itself (orders, Enter posted to the
    // game's window) also plays on in the background ([AutoAttack] Background).
    const bool focused = Focus::foreground();
    const bool foreground = focused || Config::autoAttack.background;
    AutoStart::onFrame();
    AgentSave::onFrame();
    // A load: the fight, the retreat and the enemies given up on were of the game left (the live verifier, 2026-11-11:
    // A1 «stepping back over» 3 min after it died, in the game loaded since; object ids are new there too).
    {
        static bool s_wasChanging = false;
        const bool changing = AgentSave::worldChanging();
        static int s_deaths = -1;    // the count read from disk at start is no new death
        if (s_deaths < 0)
        {
            s_deaths = AgentSave::deathsSinceSave();
        }
        if (AgentSave::deathsSinceSave() > s_deaths && AgentSave::lastDeathWasStuck())
        {
            // A stuck counted as a death: no fight lost, so neither the farming zone nor the last fight's place is
            // shunned (AgentSave shuns the place it stuck in); the quests after the load are not held for it.
            LOG("AutoAttack: a stuck counted as a death: only the place it stuck in shunned, not the fights' places");
            g_farmSector = -1;
        }
        else if (AgentSave::deathsSinceSave() > s_deaths)
        {
            if (g_farmKnown)
            {
                AgentSave::noteDeathSpot(static_cast<int>(g_farmX / kTileSize), static_cast<int>(g_farmY / kTileSize));
            }
            if (g_aggroHeroX || g_aggroHeroY)
            {
                AgentSave::noteDeathSpot(static_cast<int>(g_aggroHeroX / kTileSize), static_cast<int>(g_aggroHeroY / kTileSize));
            }
            LOG("AutoAttack: died: the farming zone at tile {},{} and where it fell ({},{}) shunned 30 min",
                g_farmKnown ? static_cast<int>(g_farmX / kTileSize) : -1, g_farmKnown ? static_cast<int>(g_farmY / kTileSize) : -1,
                static_cast<int>(g_aggroHeroX / kTileSize), static_cast<int>(g_aggroHeroY / kTileSize));
            g_farmSector = -1;
            if (s_deaths < 2 && AgentSave::deathsSinceSave() >= 2)
            {
                LOG("AutoAttack: careful from now on (2 deaths from the same save): none above the hero's level sought, the retreat sooner");
            }
        }
        s_deaths = AgentSave::deathsSinceSave();
        if (changing && !s_wasChanging)
        {
            g_retreatUntil = 0;
            g_retreatDoomed = false;
            g_retreatExtended = 0;
            g_retreatStartAt = 0;
            g_noRetreatUntil = 0;
            g_unreachable.clear();
            g_unreachableAt.clear();
            g_aggroFoes.clear();
            g_shotBy.clear();
            g_foesSeen.clear();         // object ids are new in the game loaded
            g_dangerSpots.clear();
            g_target = 0;
            // A shop trip and a walk of the game left (A1, 2026-11-11: dead with a shop open, then 27 min with no
            // order and no stuck report after the load).
            g_pending = 0;
            g_shopId = 0;
            g_shopTold = false;
            ClickWalk::cancel();
        }
        // A game loaded (a load only: not a save, a portal or a cave): Gear's town stop and quiet times begun again.
        static unsigned s_loadsSeen = 0;
        if (!changing && AgentSave::loads() != s_loadsSeen)
        {
            s_loadsSeen = AgentSave::loads();
            Gear::worldLoaded();
        }
        s_wasChanging = changing;
    }
    checkNewGame();

    // The toggle key, on its press and only while the game has the focus.
    const bool keyDown = focused && physicallyDown(Config::autoAttack.key);
    if (keyDown && !g_keyWasDown)
    {
        g_on = !g_on;
        LOG("AutoAttack: {}", g_on ? "on" : "off");
        g_homeSet = false;     // roaming starts from here
        MessageBeep(g_on ? MB_ICONASTERISK : MB_ICONEXCLAMATION);
    }
    g_keyWasDown = keyDown;

    if (focused && playerClicks())
    {
        g_quietUntil = now + static_cast<DWORD>(Config::autoAttack.pauseMs);
        endCollect("player's click");
        Tactics::reset();
    }

    // The player's own attacks, while their click holds the auto attack back and a moment after.
    if (g_quietUntil && static_cast<int>(now - g_quietUntil) < 1500)
    {
        notePlayerTarget();
    }
    // The quest creature's dialog: the first answer (Enter) until it closes; then it is done for a while. Read at a
    // player's pace (each page a few seconds on screen), so it shows that the agent speaks.
    if (g_on && UiNav::npcDialogOpen())
    {
        Lore::readDialog(UiNav::npcDialogText());    // what it is told, read before it answers
    }
    static DWORD s_talkAnswerAt = 0, s_talkOpenAt = 0;
    static int s_talkAnswers = 0;
    if (g_talkId && UiNav::npcDialogOpen())
    {
        if (!s_talkOpenAt)
        {
            s_talkOpenAt = now;
        }
        if (static_cast<int>(now - s_talkOpenAt) > 2500 && static_cast<int>(now - s_talkAnswerAt) > 3000)
        {
            if (!Act::allowed(Act::Kind::Talk, "answer the quest dialog (Enter)"))
            {
                return;
            }
            if (++s_talkAnswers > 12)
            {
                LOG("AutoAttack: quest dialog of {:x} goes on and on, left to the player", g_talkId);
                g_talkedAt[g_talkId] = now;
                g_talkId = 0;
                s_talkAnswers = 0;
                return;
            }
            LOG("AutoAttack: quest dialog of {:x}, answer 1 (Enter)", g_talkId);
            s_talkAnswerAt = now;
            Inject::key(VK_RETURN, true);
            Inject::key(VK_RETURN, false);
        }
        return;
    }
    s_talkOpenAt = 0;
    if (g_talkId && s_talkAnswers && static_cast<int>(now - s_talkAnswerAt) > 1500)
    {
        LOG("AutoAttack: spoke to {:x} ({} answers)", g_talkId, s_talkAnswers);
        g_talkedAt[g_talkId] = now;
        g_talkId = 0;
        s_talkAnswers = 0;
    }
    // A stone's dialogs (a gravestone: "Abrir", then the outcome's "Aceptar"): the first answer each time, as Enter
    // picks it; once none is open any more, the stone is done (enemies it raised are the fight's).
    static DWORD s_answerAt = 0;
    static int s_answers = 0;
    if (g_collecting && foreground && UiNav::npcDialogOpen() && fixedStone(g_target))
    {
        if (static_cast<int>(now - s_answerAt) > 700)
        {
            if (!Act::allowed(Act::Kind::Chests, "answer the stone's dialog (Enter)"))
            {
                return;
            }
            if (++s_answers > 4)
            {
                LOG("AutoAttack: stone {:x} keeps its dialog open, left to the player", g_target);
                g_lootDone.insert(lootKey(g_target));
                ++g_lootCount;
                s_answers = 0;
                endCollect("dialog");
                return;
            }
            LOG("AutoAttack: stone {:x}: dialog, answer 1 (Enter)", g_target);
            s_answerAt = now;
            Inject::key(VK_RETURN, true);
            Inject::key(VK_RETURN, false);
        }
        return;
    }
    // Any other NPC dialog left open with the agent on (a quest's next page after the talk seemed over, a creature
    // clicked on the way): the first answer after 4 s, as the agent would otherwise stand there for good.
    static DWORD s_strayOpenAt = 0, s_strayAnswerAt = 0;
    static int s_strayAnswers = 0;
    if (g_on && !s_answers && UiNav::npcDialogOpen() && static_cast<int>(now - g_craftHoldUntil) >= 0)
    {
        if (!s_strayOpenAt)
        {
            s_strayOpenAt = now;
            s_strayAnswers = 0;
        }
        // The loot's clocks stand still meanwhile (seen live, 2026-11-09: a help page at the start cost the loot
        // gone for its 6 s, «not reached»).
        g_lootBestAt = now;
        if (g_lootAtSince)
        {
            g_lootAtSince = now;
        }
        if (static_cast<int>(now - s_strayOpenAt) > 4000 && static_cast<int>(now - s_strayAnswerAt) > 3000)
        {
            if (!Act::allowed(Act::Kind::Talk, "answer the dialog left open (Enter)"))
            {
                return;
            }
            s_strayAnswerAt = now;
            ++s_strayAnswers;
            // The Enter that changes nothing (A4 and A8, 2026-11-15: 3 300 answers in 3 h, the stable's window open
            // behind the dialog): after 3, the window behind it closed; after 6, Escape, as a player leaves a talk.
            if (s_strayAnswers > 3 && Gear::closeStrayHorseWindow(true))
            {
                LOG("AutoAttack: an NPC dialog that the Enter does not close: the stable's window behind it closed");
                return;
            }
            // Escape three times at most (it could bring up the game menu instead, which its own watcher closes with
            // Escape too: the two must not take turns for good); then the dialog is left and answered every 30 s.
            if (s_strayAnswers > 6 && s_strayAnswers <= 9 &&
                Act::allowed(Act::Kind::Windows, "leave a dialog the Enter does not close (Escape)"))
            {
                LOG("AutoAttack: an NPC dialog that the Enter does not close ({} answers): Escape", s_strayAnswers);
                Inject::key(VK_ESCAPE, true);
                Inject::key(VK_ESCAPE, false);
                return;
            }
            if (s_strayAnswers > 9)
            {
                s_strayAnswerAt = now + 27000;
            }
            LOG("AutoAttack: an NPC dialog left open, answer 1 (Enter)");
            Inject::key(VK_RETURN, true);
            Inject::key(VK_RETURN, false);
        }
        return;
    }
    s_strayOpenAt = 0;
    // The stable's window left open with no horse wanted and no dialog over it: closed after 4 s, never while the
    // player is at it (no click of theirs for 20 s; the code reviewer, E2: one the player opens is theirs).
    if (g_on && Act::may(Act::Kind::Windows) && !(g_quietUntil && static_cast<int>(now - g_quietUntil) < 20000))
    {
        Gear::closeStrayHorseWindow();
    }
    if (s_answers && !UiNav::npcDialogOpen() && static_cast<int>(now - s_answerAt) > 900)
    {
        if (g_collecting && g_target)
        {
            LOG("AutoAttack: stone {:x} used ({} answers)", g_target, s_answers);
            g_lootDone.insert(lootKey(g_target));
            ++g_lootCount;
            g_target = 0;
        }
        s_answers = 0;
    }
    // A dialog opened while collecting: an NPC who spoke up as the hero passed, more often than the loot's own text
    // (fixtures with text are left out by their flags and kind already). The collect stops and leaves the dialog to
    // the player; nothing is marked, so the loot is tried again on the next collect.
    if (g_collecting && foreground && UiNav::npcDialogOpen())
    {
        LOG("AutoAttack: a dialog opened while going for {:x}, left to the player", g_target);
        endCollect("dialog");
        return;
    }
    if (g_collecting)
    {
        if (!foreground)
        {
            endCollect("focus lost");
        }
        else
        {
            collectFrame(now);
            return;
        }
    }
    // Collect always (AutoCollect), and also whenever the auto attack fights for the player: the loot of each fight
    // taken once it is over, before the next (the player's own play keeps to A unless AutoCollect is on).
    if (Act::may(Act::Kind::PickUp) && Config::autoAttack.pickup && (Config::autoAttack.autoCollect || g_on) &&
        !g_collecting && foreground &&
        !Controller::drives() && !ClickWalk::walking() &&
        Controller::worldRunning() && heroAlive())
    {
        autoCollect(now);
        if (g_collecting)
        {
            return;
        }
    }
    // The agent's map follows the hero always, the auto attack on or off (the radar only while it looks around).
    if (Controller::worldRunning())
    {
        cObjectManager* objects = cObjectManager::instance();
        cEngine* engine = FrameHooks::engine();
        if (cCreature* self = objects && engine ? objects->creature(engine->controlled) : nullptr)
        {
            const int layer = *(reinterpret_cast<const uint8_t*>(self) + 0x24);
            MapMemory::visit(layer, self->x, self->y);
            noteTrail(now, self->x, self->y, layer);
            watchTutorial(now);
            ride(now, self);
            if (g_on)
            {
                watchStuck(now, self);
                // The doors on the screen noted for the routes every 3 s, before one is needed (each is noted as it
                // is weighed: acceptDoor), so a plan goes through a gate rather than around a wall.
                static DWORD s_doorScanAt = 0;
                if (now - s_doorScanAt > 3000)
                {
                    s_doorScanAt = now;
                    AimAssist::Target none;
                    AimAssist::findObject(4000.0f, [](uint32_t id, void*) {
                        acceptDoor(id, nullptr);
                        return false;
                    }, nullptr, none);
                }
            }
            // A level gained by the same hero (one up, not a load's change): saved as for a quest done.
            {
                static int s_level = 0;
                static uint32_t s_hero = 0;
                const int level = *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(self) + 0x3A8 + 0x56);
                if (AgentSave::worldChanging())
                {
                    s_level = 0;
                }
                else
                {
                    if (s_hero == self->id && s_level && level == s_level + 1)
                    {
                        AgentSave::levelUp();
                    }
                    s_level = level;
                    s_hero = self->id;
                }
            }
            writeMind(now, self, layer,
                      *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(self) + 0x3A8 + 0x56));
            scanQuestMarks(now, self->x, self->y,
                           *reinterpret_cast<const uint16_t*>(reinterpret_cast<const uint8_t*>(self) + 0x3A8 + 0x56),
                           static_cast<uint8_t>(layer));
            if (float sx, sy; AimAssist::hero(sx, sy))
            {
                MapMemory::wantGround(layer, self->x, self->y, sx, sy);
                if (g_on)
                {
                    publishOverlay(now, self, sx, sy);
                }
            }
            if (!g_on)
            {
                MapMemory::beginRadar();
                MapMemory::endRadar();
                MapMemory::setRoute(false);
            }
            MapMemory::save(now, 300000);
        }
    }
    // Gear: put on what is better when calm, sell and buy at a merchant (its own settings, the auto attack on or off).
    // The merchant trip: the shop the agent opened is the trip's; once Gear has nothing more there, it is closed.
    // The inventory left open (a help window's, the player's earlier): with it open a pick up stays on the cursor
    // instead of going to the backpack (seen live 2026-11-09). Closed (I, its key) at once while the agent collects,
    // else after 3 s open with no click of the player's for 8 s; never at a shop nor at a combo master (A2 2026-11-12:
    // closed with the first rune in the swap's slot, 19 visits and no swap).
    static DWORD s_inventorySince = 0, s_inventoryClosedAt = 0;
    {
        cUI_Manager* ui = cUI_Manager::instance();
        cUI_Window2* inventory = ui && (ui->flags & cUI_Manager::inGame) ? ui->window(cUI_Manager::Window::inventory) : nullptr;
        // Without the focus too (the stuck solver, 2026-11-13: the game opens it itself on a pick up, a chest, a
        // door; a copy without the focus never closed it, the key does nothing there: runs of 5-15).
        if (g_on && Act::may(Act::Kind::Windows) && inventory && inventory->visible() && !Gear::shopOpen() &&
            !Gear::craftsmanOpen() && !Gear::storageOpen() && !Gear::sorting())
        {
            if (!s_inventorySince)
            {
                s_inventorySince = now;
            }
            const bool playerBusy = g_quietUntil && static_cast<int>(now - g_quietUntil) < 8000;
            if (now - s_inventoryClosedAt > 1500 &&
                (g_collecting || (now - s_inventorySince > 3000 && !playerBusy)) &&
                Act::allowed(Act::Kind::Windows, "close the inventory left open"))
            {
                // The key that does not close it (docs/Estudio-mejoras.md P5: A8 17 times in 30 s, A4 12; a copy
                // plays without the focus): after 3 presses, the windows' own close (0x7325C0 thiscall(window, bits
                // to clear from +0x10), as the horse window is closed).
                static int s_inventoryKeys = 0;
                static DWORD s_inventoryKeyAt = 0;
                s_inventoryKeys = now - s_inventoryKeyAt < 5000 ? s_inventoryKeys + 1 : 1;
                s_inventoryKeyAt = now;
                LOG("AutoAttack: the inventory is open{}: closed{}", g_collecting ? " while collecting" : "",
                    s_inventoryKeys > 3 || !foreground ? " (by the window's own close)" : "");
                s_inventoryClosedAt = now;
                if (s_inventoryKeys > 3 || !foreground)
                {
                    using ClearFlags = void(__fastcall*)(void* window, void*, uint32_t bits);
                    reinterpret_cast<ClearFlags>(0x7325C0)(inventory, nullptr, 1);
                    s_inventoryKeys = 0;
                    return;
                }
                Inject::key('I', true);
                Inject::key('I', false);
            }
        }
        else
        {
            s_inventorySince = 0;
        }
    }
    if (g_shopId && Gear::shopOpen() && g_shopTries)
    {
        LOG("AutoAttack: shop of {:x} open", g_shopId);
        Gear::tripOpened();
        g_shopTries = 0;
    }
    if (Gear::tripDone())
    {
        if (Gear::tripLeftFull())
        {
            g_shopUselessAt[g_shopId] = now;
            LOG("AutoAttack: the shop of {:x} took nothing more and the backpack is still full: another merchant, this "
                "one left 30 min",
                g_shopId);
        }
        LOG("AutoAttack: shop of {:x} closed, back to play", g_shopId);
        // Escape only while the shop is still open: with none open it brings up the game menu, which holds the
        // whole game (A7, 2026-11-15: the pause menu after «Tienda o artesano»).
        if (Gear::shopOpen() && Act::allowed(Act::Kind::Windows, "close the shop (Esc): the trip is over"))
        {
            Inject::key(VK_ESCAPE, true);
            Inject::key(VK_ESCAPE, false);
        }
        g_shopId = 0;
        g_shopTold = false;
    }
    if (foreground && !Controller::drives() && heroAlive())
    {
        doorUseCheck(now);
        doorPendingTick(now);
        Gear::onFrame(now, !g_collecting && !g_target && !g_pending && !g_retreatUntil && !Tactics::busy(now));
        HeroBuild::onFrame(now, !g_target && !g_retreatUntil && !Tactics::busy(now));
    }
    // A walk the player asked for on the agent's map: left be unless the hero is attacked.
    if (!g_on || !foreground || Controller::drives() || !Controller::worldRunning() || !heroAlive() ||
        (g_quietUntil && static_cast<int>(now - g_quietUntil) < 0) || (ClickWalk::walking() && !underAttack()))
    {
        g_target = 0;
        g_pending = 0;
        g_lastHealth = 0;
        Tactics::reset();
        return;
    }

    // A combat art under way: no order that would cut it short.
    Tactics::onFrame(now);
    if (Tactics::busy(now) || (g_pickupUntil && static_cast<int>(now - g_pickupUntil) < 0))
    {
        return;
    }
    // An art the player cast himself (a right click): it outlasts the pause after his click, and an order now would
    // cut it short. Nothing goes out, and Tactics casts nothing over it, until it is done.
    if (heroCasting())
    {
        return;
    }

    // A look at the situation now and then, as a player glances around, not every frame. With nothing aimed at the
    // looks come sooner, so a new attacker is answered quickly, yet at a steady pace: Tactics measures health and
    // damage between looks.
    if (!g_thinkAt || static_cast<int>(now - g_thinkAt) >= 0)
    {
        const bool idle = !g_target && !g_pending;
        g_thinkAt = now + (idle ? jitter(kIdleThinkMinMs, kIdleThinkMaxMs) : jitter(kThinkMinMs, kThinkMaxMs));
        Choice choice;
        if (!decide(now, choice))
        {
            g_target = 0;
            g_pending = 0;
            if (g_lootInstead && Act::allowed(Act::Kind::PickUp, "pick up the loot instead of fighting"))
            {
                g_lootInstead = false;
                startCollect(now);
                g_collectOne = !g_lootInsteadAll;
                return;
            }
            if (Act::allowed(Act::Kind::Walk, "explore and travel to the quests"))
            {
                roam(now);
            }
            return;
        }
        g_quietSince = 0;
        g_roamAt = 0;
        if (choice.id == g_target)
        {
            g_pending = 0;
        }
        else if (choice.id != g_pending)
        {
            // A new aim: acted on after a moment, sooner under threat.
            g_pending = choice.id;
            g_actAt = now + (choice.urgent ? jitter(kReactUrgentMinMs, kReactUrgentMaxMs)
                                           : jitter(kReactMinMs, kReactMaxMs));
        }
    }

    uint32_t id = g_target;
    if (g_pending && static_cast<int>(now - g_actAt) >= 0)
    {
        id = g_pending;
        g_pending = 0;
    }
    if (!id)
    {
        return;
    }
    if (id == g_target)
    {
        // The order again about every Repeat ms.
        const int sinceSent = static_cast<int>(now - g_sentAt);
        if (g_repeatMs <= 0 || sinceSent < g_repeatMs)
        {
            return;
        }
    }
    if (id != g_target)
    {
        ClickWalk::cancel();
        // A new enemy: the weapon slot that hurts it most first (at most every 3 s; no art under way here).
        static DWORD s_slotAt = 0;
        if (!g_looting && now - s_slotAt > 3000 && Gear::chooseWeaponFor(id))
        {
            s_slotAt = now;
        }
    }
    if (!g_looting && !Act::allowed(Act::Kind::Attack, "attack the enemy chosen"))
    {
        g_target = 0;
        g_pending = 0;
        return;
    }
    if (!g_looting && Act::may(Act::Kind::Retreat) && keepDistance(now, id))
    {
        return;
    }
    if (attack(id))
    {
        if (id != g_target)
        {
            // One left as too strong or out of reach is taken again only once it came into the melee: said so (the
            // live verifier, 2026-11-10: «too strong for now» then «target» 2 min on, the log not telling why).
            if (g_unreachable.count(id))
            {
                LOG("AutoAttack: target {:x} (left for now, but it came into the melee)", id);
            }
            else if (shotAtHero(id, now))
            {
                LOG("AutoAttack: target {:x}, the one shooting at the hero", id);
            }
            else
            {
                LOG("AutoAttack: target {:x}", id);
            }
            targetTaken(now, id);
        }
        g_target = id;
        g_sentAt = now;
        g_attackAt.store(now, std::memory_order_relaxed);
        const int repeat = Config::autoAttack.repeatMs;
        g_repeatMs = repeat > 0 ? repeat * static_cast<int>(jitter(80, 125)) / 100 : 0;
    }
    else if (id == g_target)
    {
        g_target = 0;
    }
}

bool AutoAttack::canRide(Sacred::cCreature* hero, Sacred::cCreature* horse)
{
    if (!hero || !horse)
    {
        return false;
    }
    // Manolito (deduced): skill 0x16 read as ZweiWaffen is, 0x582450 thiscall(hero +0x3A8, 0x16, 0), ret 8; the horse's
    // class its vtable +0x24 (0xD, 0); then the game's test 0x4267D0 thiscall([0xAAB5E4], skill, class, hero type
    // +0x10), ret 0xC, the cursor's MOUSE_CANTRIDE and the stable's «riding skill too low» otherwise.
    using Skill = uint8_t(__fastcall*)(void* stats, void*, int skill, int zero);
    using HorseClass = int(__fastcall*)(void* creature, void*, int what, int zero);
    using CanRide = uint8_t(__fastcall*)(void* types, void*, int skill, int cls, uint32_t heroType);
    auto* h = reinterpret_cast<uint8_t*>(hero);
    auto* m = reinterpret_cast<uint8_t*>(horse);
    if (*reinterpret_cast<const uint32_t*>(m + 0x1F4) & 0xF0)
    {
        return false;   // fleeing
    }
    void* types = *reinterpret_cast<void* const*>(0xAAB5E4);
    if (!types)
    {
        return false;
    }
    const int skill = reinterpret_cast<Skill>(0x582450)(h + 0x3A8, nullptr, 0x16, 0);
    const auto* vt = *reinterpret_cast<const uintptr_t* const*>(horse);
    const int cls = reinterpret_cast<HorseClass>(vt[0x24 / 4])(horse, nullptr, 0xD, 0);
    return reinterpret_cast<CanRide>(0x4267D0)(types, nullptr, skill, cls, *reinterpret_cast<const uint32_t*>(h + 0x10)) != 0;
}

void AutoAttack::footFor(unsigned long ms)
{
    g_onFootUntil = GetTickCount() + ms;
}

int AutoAttack::destinationRegion()
{
    return g_destRegion.load();
}

bool AutoAttack::freshQuestFailure()
{
    if (g_slotGeneration != AgentSave::generation())
    {
        return false;   // the journal not read since the last load or save
    }
    bool fresh = false;
    for (const int32_t number : g_failedNow)
    {
        if (std::find(g_failedInSlot.begin(), g_failedInSlot.end(), number) != g_failedInSlot.end())
        {
            continue;
        }
        if (std::find(g_paidFailures.begin(), g_paidFailures.end(), number) == g_paidFailures.end())
        {
            g_paidFailures.push_back(number);
            LOG("AutoAttack: quest {} failed since the last save: paid for with a load", number);
            fresh = true;
        }
        else
        {
            g_failedInSlot.push_back(number);
            LOG("AutoAttack: quest {} failed for good: it failed again after its load, the save let be", number);
        }
    }
    return fresh;
}

bool AutoAttack::storageNear()
{
    return g_storageNear.load();
}

bool AutoAttack::foughtWithin(unsigned long ms)
{
    const DWORD at = g_attackAt.load(std::memory_order_relaxed);
    return at && GetTickCount() - at < ms;
}

double AutoAttack::nearestHostileTiles()
{
    double nearest = 99.0 * kTileSize;
    for (const AggroFoe& f : g_aggroFoes)
    {
        nearest = std::min(nearest, std::hypot(static_cast<double>(f.x - g_aggroHeroX), static_cast<double>(f.y - g_aggroHeroY)));
    }
    return nearest / kTileSize;
}
