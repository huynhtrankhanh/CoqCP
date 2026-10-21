#!/usr/bin/env python3
"""Exercise actual IIL memo helpers against an independent Python dictionary."""
import random
import subprocess
import tempfile
from pathlib import Path

from test_siphash import siphash

MAX = 2**64 - 1


def main():
    repo = Path(__file__).resolve().parents[3]
    templates = repo / 'programs/ZFCProofChecker'
    runtime = (templates / 'runtime.js.in').read_text()
    hashing = runtime[runtime.index("procedure('sipRound'"):runtime.index("procedure('rehashFormulas'")]
    rename = (templates / 'rename.js.in').read_text()
    helpers = rename[rename.index('// Sparse per-substitution memo table.'):rename.index("procedure(\n  'rename',")]
    source = "environment({meta:array([int64],32),sipState:array([int64,int64,int64,int64],1),renameMemo:array([int64,int64,int64,int64],0),renameMemoScratch:array([int64,int64,int64,int64],0),printBuffer:array([int8],20)})\n"
    source += hashing + helpers + "\nprocedure('main',{},()=>{\nstore('meta',20,[1024])\n"
    expected = []

    def emit_meta(index, value):
        nonlocal source
        source += f"call(PrintInt64,{{buffer:'printBuffer'}},'unsigned',{{num:retrieve('meta',{index})[0]}})\nwriteChar(coerceInt8(10))\n"
        expected.append(str(value))

    rng = random.Random(20261021)
    for seed in [(0, 0), (MAX, MAX), (506097522914230528, 1084818905618843912)]:
        source += f"store('meta',26,[{seed[0]}])\nstore('meta',27,[{seed[1]}])\nstore('meta',8,[0])\nstore('meta',29,[16])\nstore('meta',30,[0])\ngrow('renameMemo',16)\nrange(16,(i)=>{{store('renameMemo',i,[0,0,0,0])}})\n"
        # Force a cluster through the end of the initial table, then grow it.
        keys = []
        for node in range(10000):
            if siphash(seed, (5, node, 0)) % 16 == 15:
                keys.append((node, 0))
                if len(keys) == 24:
                    break
        keys += [(0, 0), (0, 1), (MAX, MAX)]
        keys += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(200)]
        values = {}
        for i, (node, depth) in enumerate(keys):
            value = 0 if i % 9 == 0 else rng.randrange(MAX)
            values[node, depth] = value
            source += f"call('renameCachePut',{{node:{node},depth:{depth},value:{value}}})\n"
        for node, depth in reversed(keys):
            source += f"call('renameCacheGet',{{node:{node},depth:{depth}}})\n"
            emit_meta(31, values[node, depth])
        # Updating an existing exact pair must not create another entry.
        node, depth = keys[0]
        source += f"call('renameCachePut',{{node:{node},depth:{depth},value:0}})\ncall('renameCacheGet',{{node:{node},depth:{depth}}})\n"
        emit_meta(31, 0)
        emit_meta(30, len(values))
        source += f"call('renameCacheGet',{{node:{MAX},depth:0}})\n"
        emit_meta(31, MAX)
        emit_meta(8, 0)
    # A capacity doubling that cannot fit in a word must fail before allocation.
    source += "store('meta',29,[9223372036854775808])\ncall('renameCacheGrow',{})\n"
    emit_meta(8, 1)
    source += '})\n'
    with tempfile.TemporaryDirectory(prefix='coqcp-rename-cache-') as temporary:
        output = Path(temporary)
        (output / 'Memo.js').write_text(source)
        subprocess.run(['node', str(repo / 'compiler/dist/cli.js'), str(output / 'Memo.v'),
                        str(output / 'Memo.cpp'), str(output / 'Memo.js'),
                        str(repo / 'programs/IO/PrintInt64.js')], check=True, capture_output=True)
        subprocess.run(['g++', '-std=c++20', '-O2', str(output / 'Memo.cpp'), '-o', str(output / 'memo')],
                       check=True, capture_output=True)
        actual = subprocess.check_output([str(output / 'memo')], text=True, timeout=5).splitlines()
        assert actual == expected
    print(f'Rename cache: {len(expected)} dictionary-oracle checks passed across three seeds, collisions, wraparound, rehashing, zero values, updates, misses and capacity overflow.')


if __name__ == '__main__':
    main()
