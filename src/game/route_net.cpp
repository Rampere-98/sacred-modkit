#include "game/route_net.h"
#include "game/map_memory.h"
#include "game/teleports.h"
#include "log.h"

#include <windows.h>
#include <algorithm>
#include <climits>
#include <cstdint>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <mutex>
#include <queue>
#include <string>
#include <thread>
#include <vector>

namespace
{
    struct Node
    {
        int layer, x, y;
        std::string kind, name;
    };
    struct Way
    {
        int to, cost;               // cost in tenths of a tile, as the script worked it out
        int points;                 // index into g_points (-1 for a door: no walk, the game's jump)
        bool reversed;              // its points walked from the end
        int door = -1;              // index into g_doors: a door from this node's landing to `to`'s
    };
    // A door of the net ("P from to cost name box"): one way, from a landing to the other's.
    struct Door
    {
        int from = -1, to = -1;
        std::string name;           // DefPos' suffix ("17.2")
        bool box = false;           // the interior's walkable part (by the world files): x0..x1, y0..y1
        int x0 = 0, y0 = 0, x1 = 0, y1 = 0;
    };
    std::vector<Node> g_nodes;
    std::vector<std::vector<Way>> g_ways;
    std::vector<std::vector<std::pair<int, int>>> g_points;
    std::vector<Door> g_doors;
    bool g_loaded = false;          // under g_lock, as all here

    std::mutex g_lock;

    // A trip worked out, kept for its goal while the hero stays on it.
    struct Kept
    {
        int layer = -1, toX = 0, toY = 0, fromX = 0, fromY = 0;
        DWORD at = 0;
        bool ok = false;
        bool noWay = false;                       // the net holds nodes near both ends and no way between them
        std::vector<std::pair<int, int>> points;  // the hero's start .. the goal
        size_t progress = 0;                      // the point nearest the hero last asked
        int tiles = 0;                            // the walk's length by the net
        // The doors on the trip: at points[doorAt[i]] the hero steps through door g_doors[doorOf[i]] and lands at
        // points[doorAt[i] + 1] (no walk between those two).
        std::vector<size_t> doorAt;
        std::vector<int> doorOf;
    };
    Kept g_kept;
    bool g_busy = false;
    // Lengths asked for (walkTiles: the portals' choice of walking or jumping), kept apart from the trip walked.
    std::deque<Kept> g_lengths;

    constexpr int kReach = 120;     // nodes this near an end (tiles, the larger axis) are tried for it
    // The nearest few only (the coordinator, 2026-11-16: 8 tried near the hero, each 1.5-5 s live).
    constexpr int kTry = 4, kKeep = 3;
    // A trip's whole working out (the coordinator, 2026-11-16: A8 took 108 s to find no node near 1317,2240, another
    // trip 27 s, eight copies holding the processor and this thread at the lowest priority): past it, given up, and
    // the old ways for the walk.
    constexpr DWORD kBudgetMs = 45000;  // 10 s gave every trip up live (A2-A8, 20:15: each stretch to a node 1.5-5 s on the low thread)
    constexpr int kStretchMargin = 24;
    constexpr int kOffTrip = 40;    // the hero this far from every point ahead: the trip is worked out again

    std::wstring netPath()
    {
        wchar_t exe[MAX_PATH] = {};
        GetModuleFileNameW(nullptr, exe, MAX_PATH);
        std::wstring p = exe;
        p = p.substr(0, p.find_last_of(L"\\/"));
        return p.substr(0, p.find_last_of(L"\\/") + 1) + L"SacredBild-red.txt";
    }

    int cheb(int ax, int ay, int bx, int by)
    {
        return std::max(std::abs(ax - bx), std::abs(ay - by));
    }

    // Under g_lock.
    void load()
    {
        g_loaded = true;
        const DWORD t0 = GetTickCount();
        FILE* f = _wfopen(netPath().c_str(), L"rb");
        if (!f)
        {
            LOG("RouteNet: no net beside the copies (SacredBild-red.txt): far walks the old ways");
            return;
        }
        std::string line;
        char buf[4096];
        size_t ways = 0;
        while (std::fgets(buf, sizeof(buf), f))
        {
            line = buf;
            // A way's line can be longer than the buffer: read on to its end.
            while (!line.empty() && line.back() != '\n' && std::fgets(buf, sizeof(buf), f))
            {
                line += buf;
            }
            const char* p = line.c_str();
            if (p[0] == 'N')
            {
                int id = 0, layer = 0, x = 0, y = 0, used = 0;
                char kind[32] = {}, name[96] = {};
                if (std::sscanf(p, "N %d %d %d %d %31s %n", &id, &layer, &x, &y, kind, &used) >= 5 &&
                    id == static_cast<int>(g_nodes.size()))
                {
                    std::sscanf(p + used, "%95s", name);
                    g_nodes.push_back({layer, x, y, kind, name});
                }
            }
            else if (p[0] == 'W')
            {
                char* end = nullptr;
                const long a = std::strtol(p + 1, &end, 10);
                const long b = std::strtol(end, &end, 10);
                const long cost = std::strtol(end, &end, 10);
                if (a < 0 || b < 0 || a >= static_cast<long>(g_nodes.size()) || b >= static_cast<long>(g_nodes.size()) || cost <= 0)
                {
                    continue;
                }
                std::vector<std::pair<int, int>> pts;
                for (;;)
                {
                    char* e2 = nullptr;
                    const long x = std::strtol(end, &e2, 10);
                    if (e2 == end || *e2 != ',')
                    {
                        break;
                    }
                    char* e3 = nullptr;
                    const long y = std::strtol(e2 + 1, &e3, 10);
                    if (e3 == e2 + 1)
                    {
                        break;
                    }
                    pts.push_back({static_cast<int>(x), static_cast<int>(y)});
                    end = e3;
                }
                if (pts.size() < 2)
                {
                    continue;
                }
                g_ways.resize(g_nodes.size());
                const int idx = static_cast<int>(g_points.size());
                g_points.push_back(std::move(pts));
                g_ways[a].push_back({static_cast<int>(b), static_cast<int>(cost), idx, false});
                g_ways[b].push_back({static_cast<int>(a), static_cast<int>(cost), idx, true});
                ++ways;
            }
            else if (p[0] == 'P')
            {
                // A door: "P from to cost name x0,y0,x1,y1" (or "-" for no box), one way.
                int a = -1, b = -1, cost = 0, used = 0;
                char name[64] = {}, box[64] = {};
                if (std::sscanf(p, "P %d %d %d %63s %n", &a, &b, &cost, name, &used) < 4 || a < 0 || b < 0 ||
                    a >= static_cast<int>(g_nodes.size()) || b >= static_cast<int>(g_nodes.size()) || cost <= 0 || a == b)
                {
                    continue;
                }
                Door d;
                d.from = a;
                d.to = b;
                d.name = name;
                if (std::sscanf(p + used, "%63s", box) == 1 &&
                    std::sscanf(box, "%d,%d,%d,%d", &d.x0, &d.y0, &d.x1, &d.y1) == 4)
                {
                    d.box = true;
                }
                g_ways.resize(g_nodes.size());
                g_ways[a].push_back({b, cost, -1, false, static_cast<int>(g_doors.size())});
                g_doors.push_back(std::move(d));
            }
        }
        std::fclose(f);
        g_ways.resize(g_nodes.size());
        LOG("RouteNet: net of {} nodes, {} ways and {} doors read in {} ms", g_nodes.size(), ways, g_doors.size(),
            GetTickCount() - t0);
    }

    // The walk's length in tenths of a tile along route tiles.
    int lengthOf(const std::vector<std::pair<int, int>>& cells)
    {
        int c = 0;
        for (size_t i = 1; i < cells.size(); ++i)
        {
            c += (cells[i].first != cells[i - 1].first && cells[i].second != cells[i - 1].second) ? 14 : 10;
        }
        return c;
    }

    struct End
    {
        int node, cost;
        std::vector<std::pair<int, int>> cells;   // the hero to the node, or the node to the goal
    };

    // The nodes near (x, y) on `layer` a route over the agent's map reaches (towards them, or from them to (x, y)):
    // the nearest first, at most kKeep. Not under g_lock (routeWithin takes the map's).
    // Each search gets what is left of the budget that ends at `deadline`; `late` set when it ran out.
    std::vector<End> ends(const std::vector<std::pair<int, int>>& around, int layer, int x, int y, bool toNode, int& tried,
                          DWORD deadline, bool& late)
    {
        std::vector<End> out;
        tried = 0;
        for (const auto& [node, d] : around)
        {
            if (static_cast<int>(out.size()) >= kKeep || tried >= kTry)
            {
                break;
            }
            const DWORD now = GetTickCount();
            if (static_cast<int32_t>(deadline - now) <= 0)
            {
                late = true;
                break;
            }
            ++tried;
            const Node& n = g_nodes[node];
            std::vector<std::pair<int, int>> cells;
            const DWORD left = deadline - now;
            const bool ok = toNode ? MapMemory::routeWithin(layer, x, y, n.x, n.y, kStretchMargin, cells, left)
                                   : MapMemory::routeWithin(layer, n.x, n.y, x, y, kStretchMargin, cells, left);
            if (!ok && static_cast<int32_t>(deadline - GetTickCount()) <= 0)
            {
                late = true;
                break;
            }
            if (ok)
            {
                out.push_back({node, lengthOf(cells), std::move(cells)});
            }
        }
        return out;
    }

    std::vector<std::pair<int, int>> nearNodes(int layer, int x, int y)
    {
        std::vector<std::pair<int, int>> around;
        for (int i = 0; i < static_cast<int>(g_nodes.size()); ++i)
        {
            const Node& n = g_nodes[i];
            const int d = cheb(n.x, n.y, x, y);
            if (n.layer == layer && d <= kReach)
            {
                around.push_back({i, d});
            }
        }
        std::sort(around.begin(), around.end(), [](const auto& a, const auto& b) { return a.second < b.second; });
        return around;
    }

    void addThinned(std::vector<std::pair<int, int>>& out, const std::vector<std::pair<int, int>>& cells, size_t every)
    {
        for (size_t i = 0; i < cells.size(); i += every)
        {
            out.push_back(cells[i]);
        }
        if (!cells.empty() && (cells.size() - 1) % every)
        {
            out.push_back(cells.back());
        }
    }

    // On the low thread: the trip from (fromX, fromY) to (toX, toY).
    Kept work(int layer, int fromX, int fromY, int toX, int toY)
    {
        const DWORD t0 = GetTickCount();
        Kept k;
        k.layer = layer;
        k.fromX = fromX;
        k.fromY = fromY;
        k.toX = toX;
        k.toY = toY;
        // A goal one cannot stand on (a quest giver against a house's wall, the baron at 1676,2352 in a block no route
        // enters): the stretches end on the known walkable tile nearest it, the walk's last steps left to the grid.
        int goalX = toX, goalY = toY;
        if (MapMemory::nearestWalkable(layer, toX, toY, 16, goalX, goalY) && (goalX != toX || goalY != toY))
        {
            LOG("RouteNet: goal {},{} not walkable: the net's trip ends at {},{}", toX, toY, goalX, goalY);
        }
        std::vector<std::pair<int, int>> nearStart, nearGoal;
        {
            const std::lock_guard lock(g_lock);
            if (!g_loaded)
            {
                load();
            }
            nearStart = nearNodes(layer, fromX, fromY);
            nearGoal = nearNodes(layer, goalX, goalY);
        }
        // No node near one end: nothing to search for, the old ways at once.
        if (nearStart.empty() || nearGoal.empty())
        {
            LOG("RouteNet: trip {},{} to {},{} on layer {}: no node within {} tiles of the {}, {} ms", fromX, fromY, toX,
                toY, layer, kReach, nearStart.empty() ? "hero" : "goal", GetTickCount() - t0);
            k.at = GetTickCount();
            return k;
        }
        // g_nodes and g_ways are only written by load(), done above: read without the lock from here.
        int triedA = 0, triedB = 0;
        bool late = false;
        const DWORD deadline = t0 + kBudgetMs;
        std::vector<End> a = ends(nearStart, layer, fromX, fromY, true, triedA, deadline, late);
        std::vector<End> b = a.empty() || late ? std::vector<End>{} : ends(nearGoal, layer, goalX, goalY, false, triedB, deadline, late);
        if (late)
        {
            LOG("RouteNet: trip {},{} to {},{} on layer {}: given up after {} ms (the stretches to the nodes: {} tried near "
                "the hero, {} near the goal): the old ways", fromX, fromY, toX, toY, layer, GetTickCount() - t0, triedA,
                triedB);
            k.at = GetTickCount();
            return k;
        }
        if (a.empty() || b.empty())
        {
            LOG("RouteNet: trip {},{} to {},{} on layer {}: no node reached near the {} ({} within {} tiles, {} tried), {} ms",
                fromX, fromY, toX, toY, layer, a.empty() ? "hero" : "goal", (a.empty() ? nearStart : nearGoal).size(),
                kReach, a.empty() ? triedA : triedB, GetTickCount() - t0);
            k.at = GetTickCount();
            return k;
        }
        // Dijkstra over the nodes, from the ones near the hero (their stretch's cost) to the ones near the goal.
        const size_t n = g_nodes.size();
        std::vector<int> dist(n, INT32_MAX), prev(n, -1), prevWay(n, -1);
        std::vector<int> goalCost(n, -1), goalEnd(n, -1);
        for (size_t i = 0; i < b.size(); ++i)
        {
            goalCost[b[i].node] = b[i].cost;
            goalEnd[b[i].node] = static_cast<int>(i);
        }
        using Entry = std::pair<int, int>;
        std::priority_queue<Entry, std::vector<Entry>, std::greater<Entry>> open;
        std::vector<int> startEnd(n, -1);
        for (size_t i = 0; i < a.size(); ++i)
        {
            if (a[i].cost < dist[a[i].node])
            {
                dist[a[i].node] = a[i].cost;
                startEnd[a[i].node] = static_cast<int>(i);
                open.push({a[i].cost, a[i].node});
            }
        }
        int best = INT32_MAX, bestNode = -1;
        while (!open.empty())
        {
            const auto [c, v] = open.top();
            open.pop();
            if (c > dist[v])
            {
                continue;
            }
            if (c >= best)
            {
                break;
            }
            if (goalCost[v] >= 0 && c + goalCost[v] < best)
            {
                best = c + goalCost[v];
                bestNode = v;
            }
            for (size_t wi = 0; wi < g_ways[v].size(); ++wi)
            {
                const Way& w = g_ways[v][wi];
                if (c + w.cost < dist[w.to])
                {
                    dist[w.to] = c + w.cost;
                    prev[w.to] = v;
                    prevWay[w.to] = static_cast<int>(wi);
                    open.push({c + w.cost, w.to});
                }
            }
        }
        if (bestNode < 0)
        {
            LOG("RouteNet: trip {},{} to {},{} on layer {}: the net has no way between the nodes near either end, {} ms",
                fromX, fromY, toX, toY, layer, GetTickCount() - t0);
            k.at = GetTickCount();
            k.noWay = true;
            return k;
        }
        std::vector<int> chain{bestNode};
        while (prev[chain.back()] >= 0)
        {
            chain.push_back(prev[chain.back()]);
        }
        std::reverse(chain.begin(), chain.end());
        addThinned(k.points, a[startEnd[chain.front()]].cells, 6);
        std::string names;
        for (size_t i = 0; i < chain.size(); ++i)
        {
            const Node& nd = g_nodes[chain[i]];
            if (nd.kind != "paso" && names.size() < 160)
            {
                names += (names.empty() ? "" : " > ") + nd.name;
            }
            if (i + 1 < chain.size())
            {
                const Way& w = g_ways[chain[i]][prevWay[chain[i + 1]]];
                if (w.door >= 0)
                {
                    // Through a door: its landing here (the trip's last point so far: every way ends on its node),
                    // then the other landing, where the hero comes out.
                    if (k.points.empty() || k.points.back() != std::pair{nd.x, nd.y})
                    {
                        k.points.push_back({nd.x, nd.y});
                    }
                    k.doorAt.push_back(k.points.size() - 1);
                    k.doorOf.push_back(w.door);
                    k.points.push_back({g_nodes[w.to].x, g_nodes[w.to].y});
                    if (names.size() < 200)
                    {
                        names += (names.empty() ? "door " : " > door ") + g_doors[w.door].name;
                    }
                    continue;
                }
                const auto& pts = g_points[w.points];
                if (w.reversed)
                {
                    k.points.insert(k.points.end(), pts.rbegin() + 1, pts.rend());
                }
                else
                {
                    k.points.insert(k.points.end(), pts.begin() + 1, pts.end());
                }
            }
        }
        addThinned(k.points, b[goalEnd[chain.back()]].cells, 6);
        if (goalX != toX || goalY != toY)
        {
            k.points.push_back({toX, toY});
        }
        k.ok = true;
        k.tiles = best / 10;
        k.at = GetTickCount();
        LOG("RouteNet: trip {},{} to {},{} on layer {}: {} tiles by the net ({} as the crow flies), {} nodes{}{}, {} points, "
            "worked out in {} ms", fromX, fromY, toX, toY, layer, best / 10, cheb(fromX, fromY, toX, toY), chain.size(),
            names.empty() ? "" : ": ", names, k.points.size(), k.at - t0);
        return k;
    }
}

bool RouteNet::tripPasses(int layer, int toX, int toY, bool (*hit)(int tx, int ty))
{
    const std::lock_guard lock(g_lock);
    const Kept& k = g_kept;
    if (!k.ok || k.layer != layer || cheb(k.toX, k.toY, toX, toY) > 4)
    {
        return false;
    }
    for (size_t i = std::min(k.progress, k.points.size()); i < k.points.size(); i += 4)
    {
        if (hit(k.points[i].first, k.points[i].second))
        {
            return true;
        }
    }
    return false;
}

float RouteNet::tilesLeft(int layer, int heroX, int heroY, int toX, int toY)
{
    const std::lock_guard lock(g_lock);
    const Kept& k = g_kept;
    if (!k.ok || k.layer != layer || cheb(k.toX, k.toY, toX, toY) > 4 || k.points.size() < 2 || k.progress >= k.points.size())
    {
        return -1.0f;
    }
    size_t nearest = k.progress;
    int nearestD = INT32_MAX;
    const size_t windowEnd = std::min(k.points.size(), k.progress + 24);
    for (size_t i = k.progress; i < windowEnd; ++i)
    {
        const int d = cheb(k.points[i].first, k.points[i].second, heroX, heroY);
        if (d < nearestD)
        {
            nearestD = d;
            nearest = i;
        }
    }
    if (nearestD > 40)
    {
        return -1.0f;
    }
    double left = 0.0;
    for (size_t i = nearest + 1; i < k.points.size(); ++i)
    {
        // Through a door, no tiles: the game's jump from one landing to the other, thousands of tiles apart.
        if (std::find(k.doorAt.begin(), k.doorAt.end(), i - 1) != k.doorAt.end())
        {
            left += 2.0;
            continue;
        }
        left += std::hypot(static_cast<double>(k.points[i].first - k.points[i - 1].first),
                           static_cast<double>(k.points[i].second - k.points[i - 1].second));
    }
    return static_cast<float>(left);
}

RouteNet::Trip RouteNet::trip(int layer, int fromX, int fromY, int toX, int toY, std::vector<std::pair<int, int>>& out)
{
    const std::lock_guard lock(g_lock);
    if (g_loaded && g_nodes.empty())
    {
        return Trip::None;
    }
    Kept& k = g_kept;
    const DWORD now = GetTickCount();
    if (k.layer == layer && std::abs(k.toX - toX) <= 4 && std::abs(k.toY - toY) <= 4)
    {
        if (!k.ok)
        {
            // No trip for this goal: the old ways for two minutes, unless the hero has gone well away.
            if (now - k.at < 120000 && cheb(k.fromX, k.fromY, fromX, fromY) <= 24)
            {
                return Trip::None;
            }
        }
        else if (now - k.at < 600000)
        {
            // On the trip still: the point ahead nearest the hero, and the trip from there.
            size_t nearest = k.progress;
            int nearestD = INT32_MAX;
            // Only a window ahead (about 150 tiles): round a mountain the trip comes back near where it was, beyond
            // the rock, and the nearest point of all of it would skip the way round.
            const size_t windowEnd = std::min(k.points.size(), k.progress + 24);
            for (size_t i = k.progress; i < windowEnd; ++i)
            {
                const int d = cheb(k.points[i].first, k.points[i].second, fromX, fromY);
                if (d < nearestD)
                {
                    nearestD = d;
                    nearest = i;
                }
            }
            if (nearestD <= kOffTrip)
            {
                // A door passed since last asked: the hero came out at its other landing.
                size_t end = k.points.size();
                for (size_t i = 0; i < k.doorAt.size(); ++i)
                {
                    if (k.doorAt[i] >= k.progress && k.doorAt[i] < nearest)
                    {
                        LOG("RouteNet: through door {} on the trip to {},{}: out at {},{} (the hero at {},{})",
                            g_doors[k.doorOf[i]].name, toX, toY, k.points[k.doorAt[i] + 1].first,
                            k.points[k.doorAt[i] + 1].second, fromX, fromY);
                    }
                    // The walk goes as far as the next door's landing; the step through is doorAhead's.
                    if (k.doorAt[i] >= nearest && end == k.points.size())
                    {
                        end = k.doorAt[i] + 1;
                    }
                }
                k.progress = nearest;
                out.assign(k.points.begin() + static_cast<std::ptrdiff_t>(nearest),
                           k.points.begin() + static_cast<std::ptrdiff_t>(end));
                out.insert(out.begin(), {fromX, fromY});
                return Trip::Ready;
            }
            static int s_off = 0;
            if (s_off++ < 40)
            {
                LOG("RouteNet: the hero at {},{} is {} tiles off the trip to {},{}: worked out again", fromX, fromY,
                    nearestD, toX, toY);
            }
        }
    }
    if (!g_busy)
    {
        g_busy = true;
        std::thread([=] {
            // Its work is small and bounded (boxes of ~170 tiles a side, a net of ~1400 nodes, 4 stretches an end, the
            // trip's budget): at the lowest priority, with eight copies holding the processor, it ran only when Windows
            // lifted a starved thread, every few seconds (20:15: each stretch 1.5-5 s, «0 in the search»). At the
            // game's own priority it shares the processor as the game's threads do.
            SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_NORMAL);
            Kept r = work(layer, fromX, fromY, toX, toY);
            const std::lock_guard done(g_lock);
            g_kept = std::move(r);
            g_busy = false;
        }).detach();
    }
    return Trip::Working;
}

bool RouteNet::knownNoWay(int fromX, int fromY, int toX, int toY)
{
    const std::lock_guard lock(g_lock);
    if (!g_loaded || g_nodes.empty())
    {
        return false;
    }
    const DWORD now = GetTickCount();
    const auto same = [&](const Kept& k) {
        return k.layer == 0 && std::abs(k.toX - toX) <= 4 && std::abs(k.toY - toY) <= 4 && cheb(k.fromX, k.fromY, fromX, fromY) <= 12;
    };
    for (const Kept& k : g_lengths)
    {
        if (same(k) && now - k.at < 600000)
        {
            return k.noWay;
        }
    }
    return g_kept.noWay && same(g_kept) && now - g_kept.at < 600000;
}

float RouteNet::walkTiles(int fromX, int fromY, int toX, int toY)
{
    const std::lock_guard lock(g_lock);
    if (g_loaded && g_nodes.empty())
    {
        return -2.0f;
    }
    const DWORD now = GetTickCount();
    const auto same = [&](const Kept& k) {
        return k.layer == 0 && std::abs(k.toX - toX) <= 4 && std::abs(k.toY - toY) <= 4 && cheb(k.fromX, k.fromY, fromX, fromY) <= 12;
    };
    for (const Kept& k : g_lengths)
    {
        if (same(k) && now - k.at < 300000)
        {
            return k.ok ? static_cast<float>(k.tiles) : -2.0f;
        }
    }
    // The trip walked now may be the one asked for.
    if (g_kept.ok && same(g_kept) && now - g_kept.at < 300000)
    {
        return static_cast<float>(g_kept.tiles);
    }
    if (!g_busy)
    {
        g_busy = true;
        std::thread([=] {
            // Its work is small and bounded (boxes of ~170 tiles a side, a net of ~1400 nodes, 4 stretches an end, the
            // trip's budget): at the lowest priority, with eight copies holding the processor, it ran only when Windows
            // lifted a starved thread, every few seconds (20:15: each stretch 1.5-5 s, «0 in the search»). At the
            // game's own priority it shares the processor as the game's threads do.
            SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_NORMAL);
            Kept r = work(0, fromX, fromY, toX, toY);
            r.points.clear();   // only its length is kept
            r.points.shrink_to_fit();
            const std::lock_guard done(g_lock);
            g_lengths.push_front(std::move(r));
            if (g_lengths.size() > 24)
            {
                g_lengths.pop_back();
            }
            g_busy = false;
        }).detach();
    }
    return -1.0f;
}

bool RouteNet::doorAhead(int layer, int heroX, int heroY, int toX, int toY, int& landX, int& landY, const char*& name)
{
    const std::lock_guard lock(g_lock);
    const Kept& k = g_kept;
    if (!k.ok || k.layer != layer || cheb(k.toX, k.toY, toX, toY) > 4)
    {
        return false;
    }
    for (size_t i = 0; i < k.doorAt.size(); ++i)
    {
        if (k.doorAt[i] < k.progress)
        {
            continue;
        }
        const auto& [x, y] = k.points[k.doorAt[i]];
        if (cheb(x, y, heroX, heroY) > 10)
        {
            return false;   // the next door is still ahead, walked to first
        }
        landX = x;
        landY = y;
        name = g_doors[k.doorOf[i]].name.c_str();   // g_doors is only written by load()
        return true;
    }
    return false;
}

bool RouteNet::insideOf(int landX, int landY, int x, int y)
{
    const std::lock_guard lock(g_lock);
    if (!g_loaded)
    {
        load();
    }
    for (const Door& d : g_doors)
    {
        const Node& to = g_nodes[d.to];
        if (d.box && cheb(to.x, to.y, landX, landY) <= 6 && x >= d.x0 && x <= d.x1 && y >= d.y0 && y <= d.y1)
        {
            return true;
        }
    }
    return false;
}

bool RouteNet::sameInterior(int ax, int ay, int bx, int by)
{
    const std::lock_guard lock(g_lock);
    if (!g_loaded)
    {
        load();
    }
    for (const Door& d : g_doors)
    {
        if (d.box && ax >= d.x0 && ax <= d.x1 && ay >= d.y0 && ay <= d.y1 && bx >= d.x0 && bx <= d.x1 && by >= d.y0 &&
            by <= d.y1)
        {
            return true;
        }
    }
    return false;
}

void RouteNet::doorStep(int layer, int landX, int landY, int heroX, int heroY, int& stepX, int& stepY)
{
    stepX = landX;
    stepY = landY;
    // A cave's way in or out is the script's zone a few tiles off its landing (Manolito, block BE).
    if (int cx = 0, cy = 0; Teleports::caveTriggerNear(landX, landY, 8, cx, cy))
    {
        stepX = cx;
        stepY = cy;
        return;
    }
    // A house's or cellar's: the stairs anchor by the landing, the one on the hero's side.
    double best = 1e18;
    for (const auto& [ax, ay] : Teleports::anchorsNear(layer, landX, landY, 6))
    {
        if (const double d = std::hypot(ax - heroX, ay - heroY); d < best)
        {
            best = d;
            stepX = ax;
            stepY = ay;
        }
    }
}
