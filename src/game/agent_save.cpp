#include "game/agent_save.h"
#include "game/act.h"
#include "game/cheats.h"

#include <cstdlib>
#include <atomic>
#include "game/auto_attack.h"
#include "game/combat_learn.h"
#include "game/frame_hooks.h"
#include "game/gear.h"
#include "game/whereabouts.h"
#include "input/inject.h"
#include "log.h"
#include "sacred/engine.h"
#include "sacred/object.h"
#include "sacred/ui.h"

#include <windows.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <ctime>
#include <string>

using namespace Sacred;

namespace
{
    // Manolito, block S (AGENT_ADDRESSES «Partidas guardadas (bloque S)»): a cEvent (vtable 0x890B38) with +4 0x0F,
    // +8 2 save / 1 load, +0xC the slot, +0x20 the name, sent through 0x808E50()->0x8092F0(&ev, 0, 0) (ret 0xC); a save
    // only when 0x756F40()->0x75ADB0(1) allows it; nothing of it with a network game ([0x182EBEC]).
    constexpr uintptr_t kEventVtable = 0x890B38;
    constexpr uintptr_t kDispatcher = 0x808E50;
    constexpr uintptr_t kSend = 0x8092F0;
    constexpr uintptr_t kUiGetter = 0x756F40;
    constexpr uintptr_t kCanSave = 0x75ADB0;
    constexpr uintptr_t kNetwork = 0x182EBEC;
    // The save function and the free slot finder, to tell this is the exe those addresses are of.
    constexpr uintptr_t kSaveFn = 0x619BF0;
    constexpr uintptr_t kFreeSlotFn = 0x619B80;

    int g_slot = -1;            // -1 not looked at yet, 0 none (not an agent's copy)
    std::wstring g_path;        // its file
    char g_name[32] = {};
    bool g_loadedOnce = false;
    DWORD g_inGameSince = 0;
    bool g_saveWanted = false;
    bool g_restartSave = false; // the save wanted is the one before a restart (a fight's end and half health do)
    bool g_diedSince = false;   // died since the last save or load: no save
    int g_deathsSinceSave = 0;  // deaths since the slot was last written (kept across its loads)
    int32_t g_expAtSave = -1;   // the hero's experience at the last save or load (-1: taken in game next)
    // The hero's experience (its stats at +0x3A8, the experience 0x0C in: CombatLearn's kExperience).
    int32_t heroExperience(const cCreature* hero)
    {
        return *reinterpret_cast<const int32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x3A8 + 0x0C);
    }
    int32_t g_lastHealth = 1;
    DWORD g_actionAt = 0;       // the last save or load asked for
    bool g_actionSave = false;
    DWORD s_noHealthSince = 0;
    std::atomic<bool> g_reloadWanted{false};  // the hero's health read 0 since (a death the edge missed, lain in)  // ... and it was a save (the hero stays in the world, so a death still counts)
    unsigned g_generation = 0;  // each load and each save asked for
    std::atomic<unsigned> g_loads{0};   // each load asked for
    int g_sub = 0;              // the event's kind for the window's thread
    alignas(8) uint8_t g_event[0x40] = {};
    // Kept beside the slot across the copy's restarts (the live verifier, 2026-11-11: an install restarts all 8
    // every half hour, the deaths counted and the places shunned were forgotten, A3 back at once where it died):
    // SacredBild-deaths.txt, the deaths since the save on the first line, then «x y unix-time» of each spot.
    std::wstring g_deathsPath;
    std::wstring g_flagPath;    // SacredBild-save-now: the install asks for a save before a restart
    std::vector<AgentSave::DeathSpot> g_spots;
    // Places the hero stuck in (tiles), apart from the fights lost (the agent study, 2026-11-23: a stuck noted the
    // farming zone and the last fight's place as deaths, the saved spot beside them, so every quest after the load was
    // «where the hero died lately» and A6 farmed the same pocket 6.8 h). In memory only, 30 min each.
    std::vector<AgentSave::DeathSpot> g_stuckSpots;
    bool g_lastDeathStuck = false;

    void writeDeaths()
    {
        if (g_deathsPath.empty())
        {
            return;
        }
        FILE* f = _wfopen(g_deathsPath.c_str(), L"w");
        if (!f)
        {
            return;
        }
        std::fprintf(f, "%d\n", g_deathsSinceSave);
        for (const AgentSave::DeathSpot& d : g_spots)
        {
            std::fprintf(f, "%d %d %lld\n", d.x, d.y, static_cast<long long>(d.at));
        }
        std::fclose(f);
    }

    void readDeaths()
    {
        FILE* f = _wfopen(g_deathsPath.c_str(), L"r");
        if (!f)
        {
            return;
        }
        int deaths = 0;
        if (std::fscanf(f, "%d", &deaths) == 1)
        {
            g_deathsSinceSave = deaths;
        }
        const long long now = static_cast<long long>(std::time(nullptr));
        int x = 0, y = 0;
        long long at = 0;
        while (std::fscanf(f, "%d %d %lld", &x, &y, &at) == 3)
        {
            if (now - at < 14400)
            {
                g_spots.push_back({x, y, static_cast<std::time_t>(at)});
            }
        }
        std::fclose(f);
        LOG("AgentSave: {} deaths since the last save and {} places shunned, kept from before", g_deathsSinceSave,
            g_spots.size());
    }

    bool exeMatches()
    {
        const auto* save = reinterpret_cast<const uint8_t*>(kSaveFn);
        const auto* free = reinterpret_cast<const uint8_t*>(kFreeSlotFn);
        static const uint8_t kSaveHead[] = {0x6A, 0xFF, 0x68};
        static const uint8_t kSaveTail[] = {0x64, 0xA1, 0x00, 0x00, 0x00, 0x00, 0x50};
        static const uint8_t kFree[] = {0x81, 0xEC, 0x00, 0x01, 0x00, 0x00, 0x56, 0xBE, 0x01, 0x00, 0x00, 0x00};
        return std::memcmp(save, kSaveHead, sizeof(kSaveHead)) == 0 &&
               std::memcmp(save + 7, kSaveTail, sizeof(kSaveTail)) == 0 &&
               std::memcmp(free, kFree, sizeof(kFree)) == 0;
    }

    // The copy's slot by its folder: ...\SacredA<n>\Sacred.exe -> 9 + n; anything else none.
    void setAside();
    bool slotFileExists();

    void findSlot()
    {
        g_slot = 0;
        wchar_t exe[MAX_PATH] = {};
        GetModuleFileNameW(nullptr, exe, MAX_PATH);
        std::wstring path = exe;
        const size_t cut = path.find_last_of(L"\\/");
        if (cut == std::wstring::npos)
        {
            return;
        }
        const std::wstring dir = path.substr(0, cut);
        const size_t nameAt = dir.find_last_of(L"\\/");
        const std::wstring name = nameAt == std::wstring::npos ? dir : dir.substr(nameAt + 1);
        if (name.size() != 8 || name.compare(0, 7, L"SacredA") != 0 || name[7] < L'1' || name[7] > L'8')
        {
            LOG("AgentSave: not an agent's copy ({}): no saves", std::string(name.begin(), name.end()));
            return;
        }
        if (!exeMatches())
        {
            LOG("AgentSave: the save functions are not where block S has them: no saves");
            return;
        }
        // Only where the copy's SacredBild.ini asks for it ([AgentSave] Enabled=1), while it is tried on one copy.
        const std::wstring ini = dir + L"\\SacredBild.ini";
        if (!GetPrivateProfileIntW(L"AgentSave", L"Enabled", 0, ini.c_str()))
        {
            LOG("AgentSave: off for this copy ([AgentSave] Enabled=0)");
            return;
        }
        const int n = name[7] - L'0';
        g_slot = 9 + n;
        wchar_t file[32];
        swprintf(file, 32, L"\\save\\GAME%02d.PAK", g_slot);
        g_path = dir + file;
        g_deathsPath = dir + L"\\SacredBild-deaths.txt";
        g_flagPath = dir + L"\\SacredBild-save-now";
        readDeaths();
        std::snprintf(g_name, sizeof(g_name), "Agente A%d", n);
        LOG("AgentSave: the copy's slot is GAME{:02d}", g_slot);
        // Deaths kept from a build without this rule: the slot is set aside before the menu loads it.
        if (g_deathsSinceSave >= 10 && slotFileExists())
        {
            setAside();
        }
    }

    // A save with no way on (the player, 2026-11-11: «sí, desde 10»): the hero starts again from the start, as a
    // player would. The slot is kept aside as GAMEnn.BAK (not deleted); the new game's first quest done writes it anew.
    void setAside()
    {
        // One backup per hero only (the player, 2026-11-11: «apenas 1 backup por personaje, que sería el savegame
        // anterior siempre»): the save set aside becomes the .BAK, over the one there.
        // The set-aside hero is GAMEnn.OLD and its own backup GAMEnn.OLDBAK: GAMEnn.BAK is only ever the NEW hero's previous
        // save, so three deaths of the new hero (L2) never load the old one (L27) in its place (the stuck solver,
        // 2026-11-16, the coordinator's catch: the .BAK right after a set-aside was the old hero's).
        const std::wstring base = g_path.substr(0, g_path.size() - 4);
        // Never over an earlier hero set aside (2026-11-23, the study: A4's L26 hero would be lost by a second set-aside):
        // GAMEnn.OLD, then .OLD2, .OLD3... each with its own .OLDBAKk.
        std::wstring suffix;
        for (int k = 1; k < 100; ++k)
        {
            suffix = k == 1 ? std::wstring() : std::to_wstring(k);
            if (GetFileAttributesW((base + L".OLD" + suffix).c_str()) == INVALID_FILE_ATTRIBUTES)
            {
                break;
            }
        }
        const std::wstring bak = base + L".BAK", oldSave = base + L".OLD" + suffix, oldBak = base + L".OLDBAK" + suffix;
        MoveFileExW(bak.c_str(), oldBak.c_str(), MOVEFILE_REPLACE_EXISTING);
        MoveFileExW(g_path.c_str(), oldSave.c_str(), MOVEFILE_REPLACE_EXISTING);
        g_deathsSinceSave = 0;
        g_spots.clear();
        writeDeaths();
        LOG("AgentSave: the save is set aside as GAME{:02d}.OLD{} (its backup .OLDBAK{}), a new game from the start", g_slot,
            std::string(suffix.begin(), suffix.end()), std::string(suffix.begin(), suffix.end()));
    }

    bool slotFileExists()
    {
        const DWORD attributes = GetFileAttributesW(g_path.c_str());
        return attributes != INVALID_FILE_ATTRIBUTES && !(attributes & FILE_ATTRIBUTE_DIRECTORY);
    }

    // The save before the last one back as the slot's (the stuck solver, 2026-11-16: A7 wrote GAME16 at 21:58:36 in the
    // middle of a fight, at 70 % of its health, two potions left, 30 enemies of levels 10-30 about; every load put it back
    // there and it died 15 times in 34 min, the tenth setting the character aside; A4 the same, 9 deaths). A player who
    // dies three times from one save goes back to the one before it. The bad save is kept as GAMEnn.BAD. Once per 30 min.
    bool restoreBackup()
    {
        static DWORD s_restoredAt = 0;
        const DWORD now = GetTickCount();
        if (s_restoredAt && now - s_restoredAt < 1800000)
        {
            return false;
        }
        const std::wstring base = g_path.substr(0, g_path.size() - 4);
        const std::wstring backup = base + L".BAK", bad = base + L".BAD";
        const DWORD attributes = GetFileAttributesW(backup.c_str());
        if (attributes == INVALID_FILE_ATTRIBUTES || (attributes & FILE_ATTRIBUTE_DIRECTORY))
        {
            return false;
        }
        if (!MoveFileExW(g_path.c_str(), bad.c_str(), MOVEFILE_REPLACE_EXISTING) || !CopyFileW(backup.c_str(), g_path.c_str(), FALSE))
        {
            LOG("AgentSave: the save before the last could not be put back (error {})", GetLastError());
            return false;
        }
        s_restoredAt = now;
        g_deathsSinceSave = 0;
        LOG("AgentSave: three deaths from one save: the save before it is the slot's again (the bad one kept as GAME{:02d}.BAD)",
            g_slot);
        return true;
    }

    // On the window's thread (the game's own UI sends these there).
    void sendEvent(void*)
    {
        std::memset(g_event, 0, sizeof(g_event));
        *reinterpret_cast<uintptr_t*>(g_event) = kEventVtable;
        *reinterpret_cast<uint32_t*>(g_event + 4) = 0x0F;
        *reinterpret_cast<uint32_t*>(g_event + 8) = static_cast<uint32_t>(g_sub);
        *reinterpret_cast<uint32_t*>(g_event + 0xC) = static_cast<uint32_t>(g_slot);
        *reinterpret_cast<const char**>(g_event + 0x20) = g_name;
        void* dispatcher = reinterpret_cast<void*(__cdecl*)()>(kDispatcher)();
        if (!dispatcher)
        {
            LOG("AgentSave: no event dispatcher: nothing sent");
            return;
        }
        reinterpret_cast<void(__fastcall*)(void*, void*, void*, int, int)>(kSend)(dispatcher, nullptr, g_event, 0, 0);
    }

    bool canSave()
    {
        void* ui = reinterpret_cast<void*(__cdecl*)()>(kUiGetter)();
        return ui && (reinterpret_cast<uint32_t(__fastcall*)(void*, void*, int)>(kCanSave)(ui, nullptr, 1) & 0xFF) != 0;
    }

    void load(DWORD now, const char* why)
    {
        LOG("AgentSave: {}: loading GAME{:02d}", why, g_slot);
        ++g_loads;
        g_expAtSave = -1;
        g_sub = 1;
        g_actionAt = now;
        g_actionSave = false;
        g_saveWanted = false;
        g_diedSince = false;
        ++g_generation;
        Inject::call(&sendEvent, nullptr);
    }
}

unsigned AgentSave::loads()
{
    return g_loads.load();
}

unsigned AgentSave::generation()
{
    return g_generation;
}

void AgentSave::questDone()
{
    // Not the journal first read after a load (seen live: A4 saved 22 s after loading, nothing done).
    if (g_actionAt && GetTickCount() - g_actionAt < 90000 && g_sub == 1)
    {
        return;
    }
    g_saveWanted = true;
}

namespace
{
    std::atomic<bool> g_failedQuest{false};
}

void AgentSave::questFailed()
{
    g_failedQuest = true;
}

void AgentSave::visitDone(const char* where)
{
    if (!g_saveWanted)
    {
        LOG("AgentSave: {} done: a save is due", where);
    }
    questDone();
}

void AgentSave::levelUp()
{
    LOG("AgentSave: a level gained: a save is due");
    questDone();
}

namespace
{
    int g_newClass = 0;

    // On the window's thread: what the hero selection's Start does for a new hero (0x70D6E0's branch 0x70DA2D).
    void beginNewGame(void*)
    {
        uint8_t* setup = *reinterpret_cast<uint8_t**>(0x182EBE8);
        const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xCDCA1C);
        HWND window = holder ? *reinterpret_cast<HWND*>(holder + 0xB0) : nullptr;
        if (!setup || !window || *reinterpret_cast<const uintptr_t*>(0xAD6EF8))
        {
            LOG("AgentSave: a new game cannot begin from here (no setup, no window, or a game on)");
            return;
        }
        reinterpret_cast<void(__fastcall*)(void*, void*, int)>(0x7D8550)(setup, nullptr, g_newClass);
        *reinterpret_cast<uint32_t*>(setup + 0x14) = 1;
        *reinterpret_cast<uint32_t*>(0x182EE44) = 0;        // Bronze, the selection's own first choice
        *reinterpret_cast<uint8_t*>(0x182EE50) = 0;
        *reinterpret_cast<uint8_t*>(0x182EE51) = 0;
        if (uint8_t* flag = reinterpret_cast<uint8_t*(__cdecl*)()>(0x417E70)())
        {
            *flag = 1;
        }
        *(setup + 0x381D) = 0;
        alignas(8) static uint8_t ev[0x40];
        std::memset(ev, 0, sizeof(ev));
        *reinterpret_cast<uintptr_t*>(ev) = 0x890DD0;
        *reinterpret_cast<uint32_t*>(ev + 4) = 0x28;
        *reinterpret_cast<uint32_t*>(ev + 0xC) = static_cast<uint32_t>(g_newClass);
        if (void* dispatcher = reinterpret_cast<void*(__cdecl*)()>(kDispatcher)())
        {
            reinterpret_cast<void(__fastcall*)(void*, void*, void*, int, int)>(kSend)(dispatcher, nullptr, ev, 1, 0);
        }
        PostMessageW(window, 0x8002, 0, 0);
        // A new hero, a new count (the player, 2026-11-11: «al iniciar partida nueva resetea las muertes del
        // personaje»): its deaths and the places shunned were the last hero's.
        g_deathsSinceSave = 0;
        g_spots.clear();
        writeDeaths();
        LOG("AgentSave: a new game with class {} begun from the start menu: deaths and places shunned reset", g_newClass);
    }
}

bool AgentSave::worldChanging()
{
    cEngine* engine = FrameHooks::engine();
    if (engine && (engine->flags & cEngine::loading))
    {
        return true;
    }
    return g_sub == 1 && g_actionAt && GetTickCount() - g_actionAt < 30000;
}

bool AgentSave::newGameFromMenu(int gameClass)
{
    // A new game: the givers come to in the last one are new again (AutoAttack's SacredBild-givers.txt).
    if (!g_deathsPath.empty())
    {
        const std::wstring givers = g_deathsPath.substr(0, g_deathsPath.find_last_of(L"\\/") + 1) + L"SacredBild-givers.txt";
        if (DeleteFileW(givers.c_str()))
        {
            LOG("AgentSave: a new game: the givers come to before forgotten");
        }
        // And the quests skipped in it (AutoAttack's SacredBild-skips.txt)
        const std::wstring skips = g_deathsPath.substr(0, g_deathsPath.find_last_of(L"\\/") + 1) + L"SacredBild-skips.txt";
        if (DeleteFileW(skips.c_str()))
        {
            LOG("AgentSave: a new game: the quests skipped before forgotten");
        }
        const std::wstring caps = g_deathsPath.substr(0, g_deathsPath.find_last_of(L"\\/") + 1) + L"SacredBild-caps.txt";
        if (DeleteFileW(caps.c_str()))
        {
            LOG("AgentSave: a new game: the quests' 45 min clocks forgotten");
        }
    }
    // The two functions where block S 10 has them, else the clicks as before.
    static const uint8_t kStartSig[] = {0x64, 0xA1, 0x00, 0x00, 0x00, 0x00, 0x6A, 0xFF, 0x68};
    static const uint8_t kClassSig[] = {0x8B, 0x44, 0x24, 0x04, 0x89, 0x41, 0x44, 0xC2, 0x04, 0x00};
    if (std::memcmp(reinterpret_cast<const void*>(0x70D6E0), kStartSig, sizeof(kStartSig)) != 0 ||
        std::memcmp(reinterpret_cast<const void*>(0x7D8550), kClassSig, sizeof(kClassSig)) != 0)
    {
        static bool told = false;
        if (!told)
        {
            told = true;
            LOG("AgentSave: the hero selection's functions are not where block S 10 has them: the menu's clicks");
        }
        return false;
    }
    if (*reinterpret_cast<const uint32_t*>(kNetwork) || *reinterpret_cast<const uintptr_t*>(0xAD6EF8) ||
        !*reinterpret_cast<const uintptr_t*>(0x182EBE8) || gameClass < 1 || gameClass > 9)
    {
        return false;
    }
    g_newClass = gameClass;
    Inject::call(&beginNewGame, nullptr);
    return true;
}

bool AgentSave::loadFromMenu()
{
    if (g_slot < 0)
    {
        findSlot();
    }
    if (g_slot <= 0 || g_loadedOnce || !slotFileExists() || *reinterpret_cast<const uint32_t*>(kNetwork))
    {
        return false;
    }
    // In the menu with no engine yet ([0xAD6EF8] 0): the menu's Load posts 0x8002 (1, slot) to the game's window, whose
    // handler closes the menu and builds the engine loading ./SAVE/GAME<slot>.PAK; it also sets [[0x182EBE8]+0x14] 1.
    const uintptr_t holder = *reinterpret_cast<const uintptr_t*>(0xCDCA1C);
    HWND window = holder ? *reinterpret_cast<HWND*>(holder + 0xB0) : nullptr;
    uint8_t* setup = *reinterpret_cast<uint8_t**>(0x182EBE8);
    if (*reinterpret_cast<const uintptr_t*>(0xAD6EF8) || !window || !setup)
    {
        return false;
    }
    *reinterpret_cast<uint32_t*>(setup + 0x14) = 1;
    PostMessageW(window, 0x8002, 1, static_cast<LPARAM>(g_slot));
    g_loadedOnce = true;
    ++g_loads;
    g_expAtSave = -1;
    g_sub = 1;
    g_actionAt = GetTickCount();
    g_actionSave = false;
    LOG("AgentSave: loading GAME{:02d} from the start menu", g_slot);
    return true;
}

void AgentSave::onFrame()
{
    if (g_slot < 0)
    {
        findSlot();
    }
    // Saving and loading in the game are the player's unless he allows them (the menu's start is AutoStart's). A
    // restart's save, asked from outside with the flag file, is made all the same (the environment's auditor,
    // 2026-11-14: with SaveLoad at No a copy would be closed without saving).
    const bool saveLoad = Act::automatic(Act::Kind::SaveLoad) ||
                          ((g_saveWanted || g_reloadWanted) &&
                           Act::allowed(Act::Kind::SaveLoad, g_reloadWanted ? "load the last save" : "save the game"));
    if (!saveLoad && (g_flagPath.empty() || GetFileAttributesW(g_flagPath.c_str()) == INVALID_FILE_ATTRIBUTES) &&
        !g_restartSave)
    {
        g_reloadWanted = false;
        return;
    }
    // No save of a game played under a cheat the game does not keep in step itself (a test in a laboratory copy).
    if (Cheats::taints())
    {
        static bool s_told = false;
        if (!s_told)
        {
            s_told = true;
            LOG("AgentSave: a laboratory cheat is on: this game is not saved while it is");
        }
        g_saveWanted = false;
        return;
    }
    // A save every 10 minutes too (the live verifier, four times: A8 lost a level 13 and A3 a level 8 with 25 000
    // experience, 1 h 45 without a save: only a quest done asked for one). It waits for a calm moment as the others.
    {
        static DWORD s_periodAt = GetTickCount();
        if (const DWORD now = GetTickCount(); now - s_periodAt > 600000)
        {
            s_periodAt = now;
            // Only with experience gained since the last save or load (the agent study, 2026-11-23: A6 6.8 h in one
            // pocket, 13 stuck loads, each 10-min save writing the pocket again and zeroing the deaths, so nothing ever
            // climbed). A quest, a level or a visit still saves at once.
            cObjectManager* om = cObjectManager::instance();
            const cCreature* h = om ? om->hero() : nullptr;
            const int32_t gained = h ? heroExperience(h) : -1;
            if (!g_saveWanted && gained >= 0 && g_expAtSave >= 0 && gained <= g_expAtSave)
            {
                LOG("AgentSave: 10 minutes played, no experience gained since the last save or load: not saved");
            }
            else if (!g_saveWanted)
            {
                LOG("AgentSave: 10 minutes played: a save is due");
                g_saveWanted = true;
            }
        }
    }
    if (g_slot <= 0)
    {
        return;
    }
    const DWORD now = GetTickCount();
    // A restart coming (the install asks with SacredBild-save-now beside the exe): saved first (the player, 2026-11-11:
    // the Daemon «no sube de nivel nunca» while gaining experience, each restart loading a save an hour old; «prefiero
    // guardar a cada reinicio», not every 10 min). Looked for every 2 s; no fight and half health enough then.
    // First thing each frame (2026-11-12: 7 of 8 copies never saw it, an earlier return of the frame's in the way).
    static DWORD s_flagLookAt = 0;
    if (now - s_flagLookAt > 2000)
    {
        s_flagLookAt = now;
        if (!g_flagPath.empty() && DeleteFileW(g_flagPath.c_str()))
        {
            g_saveWanted = true;
            g_restartSave = true;
            LOG("AgentSave: a restart is coming: a save due");
        }
    }
    cUI_Manager* ui = cUI_Manager::instance();
    cEngine* engine = FrameHooks::engine();
    const bool loading = engine && (engine->flags & cEngine::loading);
    const bool inGame = ui && (ui->flags & cUI_Manager::inGame) && !loading;
    cObjectManager* objects = cObjectManager::instance();
    cCreature* hero = objects ? objects->hero() : nullptr;
    if (!inGame || !hero || *reinterpret_cast<const uint32_t*>(kNetwork))
    {
        g_inGameSince = 0;
        return;
    }
    if (!g_inGameSince)
    {
        g_inGameSince = now;
        if (g_expAtSave < 0)
        {
            g_expAtSave = heroExperience(hero);
        }
        g_lastHealth = hero->health;
    }
    // The copy's own game, once in a game at start (a new one begun by AutoStart, then the saved one loaded over it).
    if (!g_loadedOnce)
    {
        if (now - g_inGameSince < 15000)
        {
            return;
        }
        g_loadedOnce = true;
        if (slotFileExists())
        {
            load(now, "the copy's own game");
            return;
        }
        LOG("AgentSave: no GAME{:02d} yet: this new game is the copy's", g_slot);
    }
    // After a load the hero is settling in (its health read anew); after a save it stays in the world, and a death
    // then is one (the live verifier, 2026-11-11: A5 saved at 21:20:59, died at 21:21:01, the death missed in the
    // save's 15 s, the game's own respawn went on with no load, the hero «bugged» for 17 min).
    if (g_actionAt && now - g_actionAt < 15000 && !(g_actionSave && hero->health <= 0 && g_lastHealth > 0))
    {
        g_lastHealth = hero->health;
        s_noHealthSince = 0;
        return;
    }
    // Died: its last save loaded (the player: «los que mueren tienen que cargar la partida anterior»). A quest failed
    // is a death too (the player, 2026-11-11).
    const int32_t health = hero->health;
    const bool failedQuest = g_failedQuest.exchange(false);
    // Stuck in one place for minutes (AutoAttack's watchStuck): the last save, counted as a death (the stuck solver,
    // 2026-11-11: A3 35 min still on open ground, alive, after buying a horse).
    if (g_reloadWanted.exchange(false) && slotFileExists())
    {
        // A save that loads into a place the hero cannot leave (the stuck solver, 2026-11-11: A3's GAME12, saved on
        // horseback, each load still at 3320,2679, load, still, death, load for 2 h): stuck twice on the same tile
        // after loads of it, it is set aside and a new game begun, like 10 deaths from it.
        static int32_t s_stuckX = 0, s_stuckY = 0;
        static int s_stuckTimes = 0;
        const int32_t tx = static_cast<int32_t>(hero->x / 53.66563), ty = static_cast<int32_t>(hero->y / 53.66563);
        if (s_stuckTimes && std::abs(tx - s_stuckX) <= 3 && std::abs(ty - s_stuckY) <= 3)
        {
            ++s_stuckTimes;
        }
        else
        {
            s_stuckTimes = 1;
            s_stuckX = tx;
            s_stuckY = ty;
        }
        if (s_stuckTimes >= 3)
        {
            // The save before it first, as a player would (2026-11-23: A4's L26 hero was set aside by a decision loop,
            // not a bad place); only with no backup left, a new game.
            if (restoreBackup())
            {
                LOG("AgentSave: stuck at tile {},{} after {} loads of the same save: the save before it loaded", tx, ty,
                    s_stuckTimes - 1);
                s_stuckTimes = 0;
                load(now, "stuck in one place across loads: the save before it");
                return;
            }
            LOG("AgentSave: stuck at tile {},{} after {} loads of the same save: it cannot be played on", tx, ty,
                s_stuckTimes - 1);
            setAside();
            ExitProcess(0);
        }
        // Counted as a death (the player, 2026-11-11: «que atasco cuente como muerte»): the place shunned a while
        // (AutoAttack notes the spot on the count going up) and 10 of them set the save aside. CombatLearn is not
        // told: no fight was lost.
        ++g_deathsSinceSave;
        g_lastDeathStuck = true;
        g_stuckSpots.push_back({tx, ty, std::time(nullptr)});
        LOG("AgentSave: stuck 5 min: counted as death {} since the last save (tile {},{} shunned 30 min)", g_deathsSinceSave,
            tx, ty);
        if (g_deathsSinceSave >= 10)
        {
            setAside();
            ExitProcess(0);
        }
        writeDeaths();
        load(now, "the hero stuck in one place for 5 min");
        return;
    }
    // Lying with no health and no death seen (the player, 2026-11-11: A5 «no está muerto, está bugueado», health 0
    // for 17 min after a death the save's grace missed): 20 s of it are a death too.
    if (health > 0)
    {
        s_noHealthSince = 0;
    }
    else if (!s_noHealthSince)
    {
        s_noHealthSince = now;
    }
    const bool lying = s_noHealthSince && now - s_noHealthSince > 20000;
    if (lying)
    {
        s_noHealthSince = 0;
        LOG("AgentSave: the hero has lain with no health for 20 s: counted as a death");
    }
    const bool died = (health <= 0 && g_lastHealth > 0) || failedQuest || lying;
    if (failedQuest)
    {
        LOG("AgentSave: a quest failed: counted as a death");
    }
    g_lastHealth = health;
    if (died)
    {
        if (slotFileExists())
        {
            ++g_deathsSinceSave;
            g_lastDeathStuck = false;
            LOG("AgentSave: death {} since the last save", g_deathsSinceSave);
            if (g_deathsSinceSave >= 3 && restoreBackup())
            {
                writeDeaths();
                load(now, "the hero died three times from one save: the one before it");
                return;
            }
            if (g_deathsSinceSave >= 10)
            {
                setAside();
                ExitProcess(0);
            }
            writeDeaths();
            load(now, "the hero died");
        }
        else
        {
            // No save yet: from the start again (the player: «o desde 0 si no tiene partida»). The game quits
            // without saving (its exit saves nothing, block S) and the launcher starts it anew, AutoStart a new game.
            LOG("AgentSave: the hero died with no save yet: the game quits, a new one from the start");
            ExitProcess(0);
        }
        return;
    }
    // A quest done: saved once the game allows it, with no fight about and the hero alive, unless it died since.
    static DWORD s_wantedSince = 0;
    if (!g_saveWanted)
    {
        s_wantedSince = 0;
        return;
    }
    if (!s_wantedSince)
    {
        s_wantedSince = now ? now : 1;
    }
    if (g_diedSince)
    {
        g_saveWanted = false;
        g_diedSince = false;    // the quests from here on count again
        LOG("AgentSave: a quest done, but the hero died since the last save: not saved");
        return;
    }
    // A fight foreseen holds the save, but not for ever: wanted for 3 minutes, the distance to the nearest enemy
    // below decides alone (A4, 2026-11-14: due twice in 40 min, 164 targets, never saved and not a word why).
    // 8 minutes, not 3 (the stuck solver, 2026-11-16: A7's GAME16 written at 21:58:36, 3.0 min after it was wanted, in a
    // fight with two enemies and 70 % of its health: the wait ran out just then).
    const bool patient = now - s_wantedSince > 480000;
    // 15 min at most (the owner, 2026-11-17 19:10, A1: wanted at 18:53, died at 19:00 with nothing saved since 18:44):
    // past it, saved as soon as no fight is under way, the potions, the enemies about and the health aside.
    const bool overdue = !g_restartSave && now - s_wantedSince > 900000;
    if (overdue)
    {
        static DWORD s_overdueTold = 0;
        if (now - s_overdueTold > 60000)
        {
            s_overdueTold = now;
            LOG("AgentSave: the save wanted for 15 min: made as soon as no fight is under way");
        }
    }
    const int foes = CombatLearn::forecast().foes;
    // Not shut in a closed area (the stuck solver, 2026-11-14: A3 saved at 12:23, 13:21 and 13:31 inside the cave
    // 2.3 at 4043..4091 x 70..122 and could not leave it: every load, every 5-min stuck reload and every death put it
    // back there, 2 hours). A save is made where a way on is known: outside.
    const bool shutIn = Whereabouts::area().valid && Whereabouts::area().shutIn;
    const bool allowed = canSave() && !shutIn;
    // Not with the potions gone and the gold to buy them (the stuck solver, 2026-11-16: A8 wrote GAME17 at 06:52:08 with
    // none, in the middle of a zone of 15-25 levels; every load put it back there dry and it died 22 times in 43 min;
    // 35 of the 80 deaths of A1, A3, A6 and A8 came within 4 min of the previous one): the merchant first, the save
    // after, or at the latest 10 min after it was wanted.
    // With two potions or fewer too (A7 had two at 21:58:36).
    if (!g_restartSave && now - s_wantedSince < 600000 && Gear::healingLeft() >= 0 && Gear::healingLeft() <= 2 &&
        Gear::wantsShop())
    {
        static DWORD s_dryToldAt = 0;
        if (now - s_dryToldAt > 60000)
        {
            s_dryToldAt = now;
            LOG("AgentSave: the save waits (two healing potions or fewer: the merchant first)");
        }
        return;
    }
    // Not in a fight or 15 s after one, whatever the wait (up to 12 min): the save is the place every load returns to.
    // A restart's save too, 8 s after.
    if ((!g_restartSave && (now - s_wantedSince < 720000 || overdue) && AutoAttack::foughtWithin(15000)) ||
        (g_restartSave && AutoAttack::foughtWithin(8000)))
    {
        static DWORD s_fightToldAt = 0;
        if (now - s_fightToldAt > 60000)
        {
            s_fightToldAt = now;
            LOG("AgentSave: the save waits (a fight under way or just over)");
        }
        return;
    }
    if (health <= 0 || (foes > 0 && !patient && !overdue) || !allowed)
    {
        static DWORD s_heldToldAt = 0;
        if (now - s_heldToldAt > 60000)
        {
            s_heldToldAt = now;
            LOG("AgentSave: the save waits ({})", health <= 0 ? "the hero is down" : shutIn ? "shut in a closed area" : !allowed ? "the game does not allow it now"
                                                                                           : "a fight under way");
        }
        return;
    }
    // Not where enemies stand about, nor hurt (the live verifier, 2026-11-11: A1 saved beside a group and died 5 times
    // in 31 min, each load straight back among them): a player saves once the place is quiet and the hero whole.
    // A restart's save at 80 % of the health at least (A4 and A7, 2026-11-16 21:40: «a restart coming: saving GAME13 (405 of 756
    // health)», in a fight, and eight deaths from that save in 32 min; A7 the same minute): not at half.
    if (overdue ? false
        : g_restartSave ? health * 100 < hero->maxHealth * 80
                      // Wanted for 3 minutes and never that quiet (A4 and A6, 2026-11-14: due 20 min and not saved,
                      // one fight after another): then with none within 10 tiles and half the health.
                      // Tighter (A7, 2026-11-16: saved at 70 % of its health among 30 enemies): 25 tiles and 70 % after
                      // the wait, 40 tiles and 85 % before it.
                      : now - s_wantedSince > 480000
                            ? AutoAttack::nearestHostileTiles() < 25.0 || health * 10 < hero->maxHealth * 7
                            : AutoAttack::nearestHostileTiles() < 40.0 || health * 100 < hero->maxHealth * 85)
    {
        static DWORD s_toldAt = 0;
        if (now - s_toldAt > 30000)
        {
            s_toldAt = now;
            LOG("AgentSave: a quest done: the save waits (an enemy {:.0f} tiles off, {} of {} health)",
                AutoAttack::nearestHostileTiles(), health, hero->maxHealth);
        }
        return;
    }
    // Not on horseback (the player, 2026-11-11: «el elfo oscuro lo veo muriendo encima del caballo»): A5 saved mounted
    // 0.3 s after a level gained, and every load of it showed the hero at 0 health on the horse, dying there, then
    // standing again without it. Off the horse first, then saved.
    // Nor half off it (Manolito, block AG: the riding bits and the control left on the horse with the hero on foot;
    // A6 saved so, 2026-11-12, and each load had the camera on the horse): AutoAttack mends that first.
    const cEngine* rideEngine = FrameHooks::engine();
    if (rideEngine && rideEngine->controlled != hero->id &&
        !*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x1EC))
    {
        return;
    }
    if (*reinterpret_cast<const uint32_t*>(reinterpret_cast<const uint8_t*>(hero) + 0x1EC) != 0)
    {
        AutoAttack::footFor(20000);
        static DWORD s_mountTold = 0;
        if (now - s_mountTold > 30000)
        {
            s_mountTold = now;
            LOG("AgentSave: the save waits for the hero to get off the horse");
        }
        return;
    }
    // The process's free address space: the game's save builds each block in one piece of memory (the quests' about
    // 11 MB), and a 32-bit Sacred.exe has 2 GB (Manolito block BI: A2 crashed at 14:26 saving GAME11, the 11 MB asked
    // for not there, D3D9On12 and the textures loaded). Too little in one piece: no save now (it would only crash).
    {
        size_t largest = 0, total = 0;
        MEMORY_BASIC_INFORMATION mbi{};
        for (auto* at = static_cast<uint8_t*>(nullptr); VirtualQuery(at, &mbi, sizeof(mbi)) == sizeof(mbi);
             at = static_cast<uint8_t*>(mbi.BaseAddress) + mbi.RegionSize)
        {
            if (mbi.State == MEM_FREE)
            {
                total += mbi.RegionSize;
                largest = std::max(largest, static_cast<size_t>(mbi.RegionSize));
            }
            if (mbi.RegionSize == 0)
            {
                break;
            }
        }
        LOG("AgentSave: free address space {} MB, the largest piece {} MB", total >> 20, largest >> 20);
        if (largest < (24u << 20))
        {
            LOG("AgentSave: under 24 MB free in one piece: no save now, the game would crash building it");
            g_saveWanted = false;
            g_restartSave = false;
            return;
        }
    }
    // Never a save with a quest failed since the last one (the coordinator, 2026-11-16: «comprueba que nunca se guarde
    // después de fallar una»): the save waits and the last one is loaded, as for any failure; one failed again after
    // its load is let be (AutoAttack logs it «failed for good»). Before a restart the save is only skipped: the
    // restart loads the last one.
    if (AutoAttack::freshQuestFailure())
    {
        g_saveWanted = false;
        if (g_restartSave)
        {
            g_restartSave = false;
            LOG("AgentSave: a quest failed since the last save: no save before the restart, it loads the last one");
            return;
        }
        LOG("AgentSave: a quest failed since the last save: not saved, the last one loaded");
        g_failedQuest = true;
        return;
    }
    // The last save kept beside it first (a bad game is not carried on with nothing to go back to).
    const std::wstring backup = g_path.substr(0, g_path.size() - 4) + L".BAK";
    if (slotFileExists())
    {
        CopyFileW(g_path.c_str(), backup.c_str(), FALSE);
    }
    LOG("AgentSave: {}: saving GAME{:02d} ({} of {} health)", g_restartSave ? "a restart coming" : "a quest done", g_slot,
        health, hero->maxHealth);
    g_saveWanted = false;
    g_restartSave = false;
    g_deathsSinceSave = 0;
    g_expAtSave = heroExperience(hero);
    writeDeaths();
    g_sub = 2;
    ++g_generation;
    g_actionAt = now;
    g_actionSave = true;
    Inject::call(&sendEvent, nullptr);
}

int AgentSave::deathsSinceSave()
{
    return g_deathsSinceSave;
}

void AgentSave::noteDeathSpot(int x, int y)
{
    const std::time_t now = std::time(nullptr);
    std::erase_if(g_spots, [now](const DeathSpot& d) { return now - d.at >= 14400; });
    g_spots.push_back({x, y, now});
    writeDeaths();
}

bool AgentSave::lastDeathWasStuck()
{
    return g_lastDeathStuck;
}

bool AgentSave::nearDeathSpot(int x, int y, bool stuckToo)
{
    if (stuckToo)
    {
        const std::time_t at = std::time(nullptr);
        std::erase_if(g_stuckSpots, [at](const DeathSpot& d) { return at - d.at >= 1800; });
        if (std::any_of(g_stuckSpots.begin(), g_stuckSpots.end(),
                        [&](const DeathSpot& d) { return (x - d.x) * (x - d.x) + (y - d.y) * (y - d.y) < 400; }))
        {
            return true;
        }
    }
    // Died there again and again (the live verifier, 2026-11-11: A3 back at 3223,2664 each time the 30 min ran out,
    // dead there since 07:50): shunned 30 min after one death, 60 after two, 120 after three, 240 after more.
    const std::time_t now = std::time(nullptr);
    int deaths = 0;
    std::time_t newest = 0;
    for (const DeathSpot& d : g_spots)
    {
        if (now - d.at < 14400 && (x - d.x) * (x - d.x) + (y - d.y) * (y - d.y) < 400)
        {
            ++deaths;
            newest = std::max(newest, d.at);
        }
    }
    return deaths > 0 && now - newest < 1800LL << (std::min(deaths, 4) - 1);
}

void AgentSave::reloadStuck()
{
    g_reloadWanted = true;
}
