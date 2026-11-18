# sqw_quest_open.py - which script blocks set a quest's script variable (the quest number in decimal) and under
# which conditions, from the game's compiled quest scripts (bin/<folder>/FunkCode.bin + Vectoren.bin).
# Format: docs/Descompilacion/Sub-script_quest.md (instruction = u16 op, u16 len incl. header, tagged operands).
# Strings inside an instruction are read loosely (printable runs ending in 0), enough to name the variables,
# labels and quest numbers it uses.
# Usage: python -I tools/sqw_quest_open.py [--bin "D:\...\Sacred Gold\bin\NetScript"] 151 152 1001 ...
import argparse
import os
import re
import struct

OPS = {0x43: 'SetVar', 0x44: 'SetVarBit', 0x45: 'UnsetVarBit', 0x4B: 'IncVar', 0x4C: 'DecVar', 0x14: 'TriggerQuest',
       0x15: 'SetUpQuest', 0x75: 'ActivateQuest', 0x0F: 'ExitQuest', 0x3A: 'IF', 0x42: 'ELSEIF', 0x3B: 'ELSE',
       0x0A: 'QuestDone', 0x0B: 'QuestNotDone', 0x0C: 'QuestInProgress', 0x0D: 'QuestNotInProgress', 0x19: 'CheckForQuestPool',
       0x01: 'CreateNPC', 0x16: 'CallFunktion', 0x35: 'QuestBook', 0x76: 'SetClientVars'}


def strings(b):
    return [m.group(1).decode('latin1') for m in re.finditer(rb'([\x20-\x7e]{1,40})\x00', b)]


def i32s(b):
    out = []
    for i in range(len(b)):
        if b[i] in (0x0B, 0x11, 0x36, 0x75, 0x1C) and i + 5 <= len(b):
            out.append(struct.unpack_from('<i', b, i + 1)[0])
    return out


def blocks(folder):
    v = open(os.path.join(folder, 'Vectoren.bin'), 'rb').read()
    f = open(os.path.join(folder, 'FunkCode.bin'), 'rb').read()
    n = struct.unpack_from('<I', v, 0)[0]
    for k in range(n):
        off, ln, q, _ = struct.unpack_from('<4i', v, 0x44 + k * 0x54)
        name = v[0x44 + k * 0x54 + 0x14:0x44 + k * 0x54 + 0x54].split(b'\0')[0].decode('latin1')
        yield name, q, f[off:off + ln]
    yield 'StartCode', -1, open(os.path.join(folder, 'StartCode.bin'), 'rb').read()


def instrs(code):
    i = 0
    while i + 4 <= len(code):
        op, ln = struct.unpack_from('<HH', code, i)
        if ln < 4:
            break
        yield op, code[i + 4:i + ln]
        i += ln


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', default=r'D:\SteamLibrary\steamapps\common\Sacred Gold\bin\NetScript')
    ap.add_argument('--all', action='store_true', help='every instruction of the matching blocks')
    ap.add_argument('--summary', action='store_true', help='one line a quest: the outside blocks that set it up or trigger it')
    ap.add_argument('quests', nargs='+')
    a = ap.parse_args()
    want = set(a.quests)
    if a.summary:
        found = {w: [] for w in a.quests}
        for name, q, code in blocks(a.bin):
            for op, args in instrs(code):
                if op in (0x14, 0x15, 0x75):
                    for x in want & ({str(v) for v in i32s(args)} | set(strings(args))):
                        if str(q) != x:
                            found[x].append('{}<{}>'.format(OPS[op], name))
        for w in a.quests:
            print(w, '|', ', '.join(sorted(set(found[w]))) or '-')
        return
    for name, q, code in blocks(a.bin):
        lines, hit = [], set()
        for op, args in instrs(code):
            ss = strings(args)
            nums = {str(x) for x in i32s(args)}
            if op in (0x43, 0x44, 0x4B) and want & set(ss):
                hit |= want & set(ss)
            if op in (0x14, 0x15, 0x75) and want & (set(ss) | nums):
                hit |= {'{}:{}'.format(OPS[op], x) for x in want & (set(ss) | nums)}
            if a.all or op in OPS:
                lines.append('    {} {} {}'.format(OPS.get(op, hex(op)), ss, i32s(args)))
        if hit:
            print('== {} (block quest {}) sets {}'.format(name, q, sorted(hit)))
            print('\n'.join(lines[:60]))


if __name__ == '__main__':
    main()
