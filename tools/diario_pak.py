# diario_pak.py - the quest journal of a Sacred Gold save (GAMExx.PAK), read only.
# Found 2026-11-23: in the decompressed chunk 0xA1 the journal is an array of records of 0x170 bytes,
# +0 state (2 just taken, <= 99 open, 100 done, 101 failed), +4 quest number (in memory the records are 0x174
# with the state at +4 and the number at +8, block BN). The array is found by its stride from any record.
# Usage: python -I tools/diario_pak.py GAME02.PAK [more.PAK ...] [--json]
import json
import struct
import sys
import zlib

MARK = b'\xde\xc0\xad\xba'
STRIDE = 0x170


def chunk(d, kind):
    for o in range(0x100, 0x400, 12):
        t, off, size = struct.unpack_from('<3I', d, o)
        if t == kind and size and d[off:off + 4] == MARK:
            return zlib.decompress(d[off + 0x20:off + 0x20 + struct.unpack_from('<I', d, off + 4)[0]])
    return b''


def journal(path):
    b = chunk(open(path, 'rb').read(), 0xA1)

    def ok(o):
        if not 0 <= o <= len(b) - 8:
            return False
        st, n = struct.unpack_from('<ii', b, o)
        return 0 <= st <= 101 and 1 <= n <= 20000

    best = []
    for o in range(0, len(b) - 8, 4):
        st, n = struct.unpack_from('<ii', b, o)
        if st == 100 and 1 <= n <= 20000 and ok(o + STRIDE) and ok(o + 2 * STRIDE):
            s = o
            while ok(s - STRIDE):
                s -= STRIDE
            e = o
            while ok(e + STRIDE):
                e += STRIDE
            if (e - s) // STRIDE + 1 > len(best):
                best = [struct.unpack_from('<ii', b, x) for x in range(s, e + 1, STRIDE)]
            break
    return {'done': sorted(n for st, n in best if st == 100), 'failed': sorted(n for st, n in best if st == 101),
            'open': sorted(n for st, n in best if st < 100)}


def main():
    paths = [a for a in sys.argv[1:] if a != '--json']
    res = {p: journal(p) for p in paths}
    if '--json' in sys.argv:
        print(json.dumps(res))
        return
    for p, j in res.items():
        print('{}: {} done, {} open, {} failed'.format(p, len(j['done']), len(j['open']), len(j['failed'])))
        for k in ('done', 'open', 'failed'):
            print('  {}: {}'.format(k, ' '.join(map(str, j[k]))))


if __name__ == '__main__':
    main()
