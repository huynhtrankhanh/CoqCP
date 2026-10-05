#!/usr/bin/env python3
"""Check generated output against a live grader, keeping stdin open."""
import argparse
import itertools
import os
from pathlib import Path
import random
import selectors
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]


def run_case(binary, permutation, crlf=False, fragmented=False):
    n = len(permutation)
    child = subprocess.Popen([str(binary)], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    selector = selectors.DefaultSelector()
    selector.register(child.stdout, selectors.EVENT_READ)
    buffered = bytearray()
    questions = 0

    def read_line():
        deadline = time.monotonic() + 2
        while b'\n' not in buffered:
            remaining = deadline - time.monotonic()
            assert remaining > 0 and selector.select(remaining), 'Output not flushed'
            data = os.read(child.stdout.fileno(), 4096)
            assert data, 'Program exited before answering'
            buffered.extend(data)
        line, _, rest = buffered.partition(b'\n')
        buffered[:] = rest
        return line.decode('ascii')

    def send(data):
        if fragmented:
            for start in range(0, len(data), 17):
                child.stdin.write(data[start:start+17])
                child.stdin.flush()
        else:
            child.stdin.write(data)
            child.stdin.flush()

    newline = '\r\n' if crlf else '\n'
    try:
        send(f'{n}{newline}'.encode())
        while True:
            line = read_line()
            if line.startswith('! '):
                result = list(map(int, line[2:].split()))
                assert result == list(permutation), (permutation, result)
                assert questions == 10, questions
                assert child.wait(timeout=2) == 0
                assert not buffered and child.stdout.read() == b'', 'Output after answer'
                assert child.stderr.read() == b''
                return
            assert questions < 10, 'Query limit exceeded'
            expected = ''.join(str((i >> questions) & 1) for i in range(n))
            assert line == '? ' + expected, (n, questions, line)
            # Apply the statement's permutation directly to the actual query.
            reply = ''.join(line[2:][a-1] for a in permutation)
            send((reply + newline).encode())
            questions += 1
    finally:
        if child.poll() is None:
            child.kill()
        child.wait()
        selector.close()
        child.stdin.close()
        child.stdout.close()
        child.stderr.close()


def cases():
    for n in range(1, 7):
        yield from itertools.permutations(range(1, n+1))
    rng = random.Random(3228)
    for _ in range(150):
        a = list(range(1, rng.randint(1, 1000)+1))
        rng.shuffle(a)
        yield a
    # Values just below, at, and above every relevant power of two.
    for n in sorted({1, 1000} | {2**k+d for k in range(1, 10) for d in (-1, 0, 1)}):
        yield list(range(1, n+1))
        yield list(range(n, 0, -1))
        a = list(range(1, n+1))
        rng.shuffle(a)
        yield a


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='coqcp-3228-') as folder:
        binary = args.binary.resolve() if args.binary else Path(folder) / 'solution'
        if not args.binary:
            subprocess.run(['g++', '-std=c++20', '-O2',
                            str(ROOT / 'generated-cpp/PermutedBinaryStrings.cpp'),
                            '-o', str(binary)], check=True)
        count = 0
        for count, a in enumerate(cases(), 1):
            run_case(binary, a, crlf=count % 3 == 0, fragmented=count % 5 == 0)
        print(f'{count} interactive cases passed; exactly 10 valid queries per case')


if __name__ == '__main__':
    main()
