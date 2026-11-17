# equipo.py - ask a running agent copy (SacredA1..A8) for its hero's equipment and print it.
# The ModKit (Gear::dumpGear) looks every 2 s for SacredBild.equipo beside Sacred.exe, writes the table to
# SacredBild-equipo.md there (body slots 0-17, weapon slots 1-5 hands 0/1: id, type, rarity, set, class-exclusive,
# required level, damage or resistances, worth score; active slot, defence and resistances, gold, backpack and
# storage counts) and deletes the request. Read only: nothing in the game is moved.
# Usage: python tools/equipo.py A2 [--root D:\SteamLibrary\steamapps\common] [--wait 30]
import argparse
import os
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('copy', help='A1..A8 (or a full folder path)')
    ap.add_argument('--root', default=r'D:\SteamLibrary\steamapps\common')
    ap.add_argument('--wait', type=float, default=30.0, help='seconds to wait for the answer')
    a = ap.parse_args()
    folder = a.copy if os.path.isdir(a.copy) else os.path.join(a.root, 'Sacred' + a.copy.upper())
    if os.path.basename(folder.rstrip('\\/')).lower() == 'sacred gold':
        sys.exit("not the owner's folder: agent copies only")
    ask = os.path.join(folder, 'SacredBild.equipo')
    answer = os.path.join(folder, 'SacredBild-equipo.md')
    before = os.path.getmtime(answer) if os.path.exists(answer) else 0.0
    open(ask, 'w').close()
    end = time.time() + a.wait
    while time.time() < end:
        if os.path.exists(answer) and os.path.getmtime(answer) > before and not os.path.exists(ask):
            time.sleep(0.2)
            sys.stdout.reconfigure(encoding='utf-8')
            print(open(answer, encoding='utf-8').read())
            return
        time.sleep(0.5)
    if os.path.exists(ask):
        os.remove(ask)
    sys.exit('no answer in {:.0f} s (the game not running, in a menu, or a ModKit without Gear::dumpGear)'.format(a.wait))


if __name__ == '__main__':
    main()
