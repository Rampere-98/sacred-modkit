#include "game/map_cache.h"
#include "game/d3d_stats.h"
#include "config/render.h"
#include "log.h"
#include "patch.h"
#include "sacred/world.h"
#include "spin_lock.h"

#include <gtl/phmap.hpp>

#include <algorithm>
#include <cstdint>
#include <mutex>
#include <shared_mutex>
#include <utility>
#include <vector>

#include <windows.h>

namespace
{
    using namespace Sacred;

    using CacheFn = decltype(Addr::recordCache)::Ptr;

    constexpr uintptr_t kNodeRecord = 0x14;

    // The ids one owner's map holds, valid while the map still has the head and size it had when the index last
    // saw it: the cache functions are the only code that inserts or evicts, and clearing resets the size.
    struct Index
    {
        cMapData* owner = nullptr;
        uint8_t* head = nullptr;
        uint32_t size = 0;
        gtl::flat_hash_map<uint32_t, uint8_t*> nodes;
    };

    // The exe's own map erase (thiscall: the map, the node; ENG 0063D910 layers, 0063D8F0 records) and in-order
    // next (cdecl, ENG 00833DE0), read from the cache functions' own call sites.
    using EraseFn = void(__thiscall*)(RecordMap* map, uint8_t* node);
    using NextFn = uint8_t*(__cdecl*)(uint8_t* node);
    NextFn g_next = nullptr;

    struct Cache
    {
        CacheFn original;
        RecordMap cMapData::* map;
        uintptr_t stampOffset;  // last use, in the node
        EraseFn erase = nullptr;
        uint32_t limit = 0;     // the game evicts the oldest, walking the whole map, on every miss from this size on
        SharedSpinLock mutex;       // the game calls some of these from its logic thread as well
        Index indexes[4];
        uint32_t next = 0;
        bool loggedFull = false;
    };

    Cache g_layers{nullptr, &cMapData::layerRecords, 0x14 + sizeof(LayerRecord)};
    Cache g_records{nullptr, &cMapData::records, 0x14 + 0x40};

    void stamp(const Cache& c, uint8_t* node)
    {
        *reinterpret_cast<uint32_t*>(node + c.stampOffset) = *Addr::g_recordStamp;
    }

    Index* findIndex(Cache& c, cMapData* owner)
    {
        for (Index& ix : c.indexes)
        {
            if (ix.owner == owner)
            {
                return &ix;
            }
        }
        return nullptr;
    }

    // Full, the game walks the whole map for the oldest node on every miss (262143 layer records after 3 h of play:
    // the owner's hitches of 0.3-1.3 s from 06:30 on, 2026-11-23). One walk here takes the oldest quarter out at once,
    // so the next misses find room and the game's walk never runs.
    void trim(Cache& c, RecordMap& map)
    {
        std::vector<std::pair<uint32_t, uint8_t*>> nodes;
        nodes.reserve(map.size);
        for (uint8_t* node = *reinterpret_cast<uint8_t**>(map.head + 8); node && node != map.head && nodes.size() <= map.size;
             node = g_next(node))
        {
            nodes.emplace_back(*reinterpret_cast<uint32_t*>(node + c.stampOffset), node);
        }
        const size_t drop = nodes.size() / 4;
        if (drop == 0)
        {
            return;
        }
        std::nth_element(nodes.begin(), nodes.begin() + drop, nodes.end());
        const DWORD start = GetTickCount();
        for (size_t i = 0; i < drop; ++i)
        {
            c.erase(&map, nodes[i].second);
        }
        LOG("Record caches: {} cache at {} entries: the oldest {} taken out in one go ({} ms)",
            &c == &g_layers ? "layer" : "record", nodes.size(), drop, GetTickCount() - start);
    }

    uint8_t* lookup(Cache& c, cMapData* owner, void* edx, uint32_t id)
    {
        if (id == 0)
        {
            return c.original(owner, edx, id);
        }
        RecordMap& map = owner->*c.map;
        {
            std::shared_lock lock(c.mutex);
            const Index* ix = findIndex(c, owner);
            if (ix && ix->head == map.head && ix->size == map.size)
            {
                const auto it = ix->nodes.find(id);
                if (it != ix->nodes.end())
                {
                    stamp(c, it->second);
                    return it->second + kNodeRecord;
                }
            }
        }

        std::unique_lock lock(c.mutex);
        Index* ix = findIndex(c, owner);
        if (!ix)
        {
            ix = &c.indexes[c.next++ % std::size(c.indexes)];
            ix->owner = owner;
            ix->nodes.clear();
            ix->head = nullptr;
        }
        if (ix->head != map.head || ix->size != map.size)
        {
            ix->nodes.clear();
            ix->head = map.head;
            ix->size = map.size;
        }
        uint8_t* node = Addr::recordMapFind(&map, &id);
        if (node != map.head)
        {
            stamp(c, node);     // what the game does on a hit
        }
        else
        {
            D3DStats::count(D3DStats::CRecordRead);
            if (c.erase && g_next && c.limit && map.size + 1 >= c.limit)
            {
                trim(c, map);
                ix->nodes.clear();
                ix->head = map.head;
                ix->size = map.size;
            }
            uint8_t* record = c.original(owner, edx, id);
            if (map.size != ix->size + 1)
            {
                if (!c.loggedFull && map.size == ix->size)
                {
                    c.loggedFull = true;
                    LOG("Record caches: {} cache full at {} entries, evicting (a whole-map scan per miss)",
                        &c == &g_layers ? "layer" : "record", map.size);
                }
                ix->nodes.clear();  // a node was evicted: it may be one the index knows
            }
            ix->head = map.head;
            ix->size = map.size;
            // The new node, unless the eviction took it right away (then the game returns a dangling record).
            node = record ? Addr::recordMapFind(&map, &id) : nullptr;
            if (!node || node == map.head || node + kNodeRecord != record)
            {
                return record;
            }
        }
        ix->nodes.emplace(id, node);
        return node + kNodeRecord;
    }

    uint8_t* __fastcall hookLayers(cMapData* owner, void* edx, uint32_t id) { return lookup(g_layers, owner, edx, id); }
    uint8_t* __fastcall hookRecords(cMapData* owner, void* edx, uint32_t id) { return lookup(g_records, owner, edx, id); }
}

void MapCache::install()
{
    // recordCache keeps 0x2000 records; full, every miss reads the file and walks the whole tree for the oldest. The
    // wide sectors (5x5) need more than that, so walking the map evicted on most misses and the frames stalled.
    // 0x8000 holds them (~3 MB more).
    if (const uintptr_t full = Addr::recordCache ? Addr::recordCache + 0xC6 : 0;
        full && Patch::verify(full, {0x3D, 0x00, 0x20, 0x00, 0x00}) && Patch::imm32(full + 1, 0x2000, 0x8000))
    {
        LOG("Record caches: the record cache holds 0x8000 records (was 0x2000)");
    }
    if (!Config::render.recordIndex)
    {
        return;
    }
    // The erase and the in-order next from the cache functions' own calls (verified as E8 calls first): layers
    // +0x142 next, +0x158 erase, limit `cmp ecx, 0x40000` at +0x121; records +0xFE erase, limit 0x2000 (0x8000 patched).
    const auto callTarget = [](uintptr_t site) -> uintptr_t {
        return site && *reinterpret_cast<const uint8_t*>(site) == 0xE8
                   ? site + 5 + *reinterpret_cast<const int32_t*>(site + 1)
                   : 0;
    };
    if (const uintptr_t layers = Addr::layerRecordCache, records = Addr::recordCache; layers && records)
    {
        const uintptr_t next = callTarget(layers + 0x142), eraseLayer = callTarget(layers + 0x158),
                        eraseRecord = callTarget(records + 0xFE);
        if (next && eraseLayer && eraseRecord && Patch::verify(layers + 0x121, {0x81, 0xF9, 0x00, 0x00, 0x04, 0x00}))
        {
            g_next = reinterpret_cast<NextFn>(next);
            g_layers.erase = reinterpret_cast<EraseFn>(eraseLayer);
            g_layers.limit = 0x40000;
            g_records.erase = reinterpret_cast<EraseFn>(eraseRecord);
            g_records.limit = Patch::verify(records + 0xC6, {0x3D, 0x00, 0x80, 0x00, 0x00}) ? 0x8000 : 0x2000;
            LOG("Record caches: full caches trimmed by a quarter at once (next {:x}, erase {:x}/{:x})", next, eraseLayer,
                eraseRecord);
        }
        else
        {
            LOG("Record caches: the erase calls not where expected: full caches left to the game's walk");
        }
    }
    Patch::hook(g_layers.original, Addr::layerRecordCache, &hookLayers, "layerRecordCache");
    Patch::hook(g_records.original, Addr::recordCache, &hookRecords, "recordCache");
    LOG("Record caches: hash index in front of the tree lookups");
}
