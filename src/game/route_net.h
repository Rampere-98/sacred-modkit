#pragma once

#include <utility>
#include <vector>

// The route net (the player, 2026-11-11: «las rutas ya deberían estar precalculadas antes que el agente piense en
// usarlas»): towns, services, entrances, portals and way points, with the walks between them worked out away from the
// game over the eight copies' shared map (tools/red_rutas.py red -> steamapps\common\SacredBild-red.txt). Live, only
// the short stretches are searched (the hero to a node near, a node near to the goal, MapMemory::routeWithin in small
// boxes) and the net between them, a few hundred nodes: no big search on the game's time.
namespace RouteNet
{
    enum class Trip
    {
        None,       // no net, or no node reached near one of the ends: the old ways
        Working,    // being worked out on a low thread: ask again
        Ready,      // `out` holds the tiles to walk, from about the hero to the goal, a point every few tiles
    };
    Trip trip(int layer, int fromX, int fromY, int toX, int toY, std::vector<std::pair<int, int>>& out);
    // The walk's length in tiles by the net on the surface (layer 0) from tile (fromX, fromY) to (toX, toY), for
    // choosing between walking and a portal: -1 while it is worked out (on the same low thread; ask again), -2 with no
    // net or no way by it. Kept five minutes for ends within 4 tiles (the goal) and 12 (the start).
    float walkTiles(int fromX, int fromY, int toX, int toY);
    // True when walkTiles' answer for those ends (asked before; the same ends as there) is that the net holds nodes near both
    // and no way between them: a place the walkers' map does not join (an enclave, the far bank of a river). False for
    // «not worked out yet», for no net, and for a start or an end with no node near it.
    bool knownNoWay(int fromX, int fromY, int toX, int toY);
    // The tiles still to walk of the trip being walked to (toX, toY) on `layer`, from the point of the trip nearest the
    // hero at (heroX, heroY) (within the 24 points ahead of the one last asked for; the trip is the net's, not the
    // hero's every step): -1 when the net has no trip for that goal or the hero is over 40 tiles off it. The auto attack's measure of progress along
    // a detour that is, in a straight line, first away from the goal (a river's bend: 1276 tiles for 385 as the crow flies).
    float tilesLeft(int layer, int heroX, int heroY, int toX, int toY);
    // Whether any point of the trip kept for (toX, toY) on `layer`, from the one the hero is nearest on, satisfies `hit`
    // (tiles). False when the net has no trip kept for that goal.
    bool tripPasses(int layer, int toX, int toY, bool (*hit)(int tx, int ty));

    // The game's doors in the net (tools/red_rutas.py red --defpos: "P" lines, DefPos' tpreinz/tprausz and
    // tpstart/tptarget; A5, 2026-11-17: quest 701's goal 4101,624 inside cave 17.2, an interior placed far off on the map,
    // its door at 3176,1930). A trip through one ends `out` at the door's landing; the hero then steps on the door (the
    // game's own jump) and lands at the other one, where the trip goes on.
    // True when the trip kept for (toX, toY) on `layer` has a door next, its landing within 10 tiles of the hero at
    // (heroX, heroY): that landing and the door's name (DefPos' suffix, "17.2").
    bool doorAhead(int layer, int heroX, int heroY, int toX, int toY, int& landX, int& landY, const char*& name);
    // Whether tile (x, y) lies inside the interior a door of the net lands in at (landX, landY) (within 6 tiles): the
    // interior's walkable part by the world files, as a box.
    bool insideOf(int landX, int landY, int x, int y);
    // Whether tiles (ax, ay) and (bx, by) both lie inside one interior a door of the net lands in (its box).
    bool sameInterior(int ax, int ay, int bx, int by);
    // The tile to step on to go through a door whose landing is (landX, landY) on `layer`, the hero at (heroX, heroY):
    // a cave's zone beside the landing (Teleports::caveTriggerNear), else the stairs anchor nearest the hero
    // (Teleports::anchorsNear), else the landing. On the game's thread (both read its memory).
    void doorStep(int layer, int landX, int landY, int heroX, int heroY, int& stepX, int& stepY);
}
