#!/usr/bin/env python3
"""Check the actual IIL SipHash against a published vector and independent oracle."""
import random
import subprocess
import tempfile
from pathlib import Path

MASK = (1 << 64) - 1


def siphash(key, words):
    v = [0x736f6d6570736575 ^ key[0], 0x646f72616e646f6d ^ key[1],
         0x6c7967656e657261 ^ key[0], 0x7465646279746573 ^ key[1]]

    def rotate(x, n):
        return ((x << n) | (x >> (64 - n))) & MASK

    def round_():
        v[0] = (v[0] + v[1]) & MASK
        v[1] = rotate(v[1], 13) ^ v[0]
        v[0] = rotate(v[0], 32)
        v[2] = (v[2] + v[3]) & MASK
        v[3] = rotate(v[3], 16) ^ v[2]
        v[0] = (v[0] + v[3]) & MASK
        v[3] = rotate(v[3], 21) ^ v[0]
        v[2] = (v[2] + v[1]) & MASK
        v[1] = rotate(v[1], 17) ^ v[2]
        v[2] = rotate(v[2], 32)

    for word in [*words, 24 << 56]:
        v[3] ^= word
        round_()
        round_()
        v[0] ^= word
    v[2] ^= 255
    for _ in range(4):
        round_()
    return v[0] ^ v[1] ^ v[2] ^ v[3]


def main():
    repo = Path(__file__).resolve().parents[3]
    key = (0x0706050403020100, 0x0f0e0d0c0b0a0908)
    words = (0x0706050403020100, 0x0f0e0d0c0b0a0908, 0x1716151413121110)
    # veorq/SipHash vectors.h, vectors_sip64[24], little-endian output bytes.
    # https://github.com/veorq/SipHash/blob/master/vectors.h
    assert siphash(key, words) == 0xb8ad50c6f649af94
    rng = random.Random(20261019)
    cases = [(key, words), ((0, 0), (0, 0, 0)), ((MASK, MASK), (MASK, MASK, MASK))]
    cases += [(tuple(rng.getrandbits(64) for _ in range(2)),
               tuple(rng.getrandbits(64) for _ in range(3))) for _ in range(64)]
    runtime = (repo / 'programs/ZFCProofChecker/runtime.js.in').read_text()
    helpers = runtime[runtime.index("procedure('sipRound'"):runtime.index("procedure('rehashFormulas'")]
    source = "environment({meta: array([int64],32), sipState: array([int64,int64,int64,int64],1), printBuffer: array([int8],20)})\n"
    source += helpers + "\nprocedure('main', {}, () => {\nstore('meta',20,[1024])\n"
    for key, words in cases:
        source += f"store('meta',26,[{key[0]}])\nstore('meta',27,[{key[1]}])\n"
        source += f"call('formulaHash',{{tag:{words[0]},a:{words[1]},b:{words[2]}}})\n"
        source += "call(PrintInt64,{buffer:'printBuffer'},'unsigned',{num:retrieve('meta',28)[0]})\nwriteChar(coerceInt8(10))\n"
    source += '})\n'
    with tempfile.TemporaryDirectory(prefix='coqcp-siphash-') as directory:
        directory = Path(directory)
        (directory / 'SipHash.js').write_text(source)
        subprocess.run(['node', str(repo / 'compiler/dist/cli.js'), str(directory / 'SipHash.v'),
                        str(directory / 'SipHash.cpp'), str(directory / 'SipHash.js'),
                        str(repo / 'programs/IO/PrintInt64.js')], check=True, capture_output=True)
        result = subprocess.run(['g++', '-std=c++20', '-O2', str(directory / 'SipHash.cpp'),
                                 '-o', str(directory / 'siphash')], capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stderr)
        actual = subprocess.check_output([str(directory / 'siphash')], text=True).splitlines()
        assert actual == [str(siphash(*case)) for case in cases]
    print(f'SipHash-2-4: published 24-byte vector and {len(cases)-1} additional oracle cases passed.')


if __name__ == '__main__':
    main()
