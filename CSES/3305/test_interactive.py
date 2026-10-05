#!/usr/bin/env python3
"""Exercise compiled CoqCP output through real pipes, never preloading replies."""
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


def model(finland, sweden, k):
    n = len(finland)
    queries = []

    def ask(country, i):
        if i == 0:
            return 1_000_000_001
        if i == n + 1:
            return 0
        assert 1 <= i <= n
        queries.append((country, i))
        return (finland if country == 'F' else sweden)[i - 1]

    lo, hi = max(0, k - n), min(k, n)
    for _ in range(17):
        if lo == hi:
            break
        mid = (lo + hi) // 2
        f, s = ask('F', mid + 1), ask('S', k - mid)
        if f < s:
            hi = mid
        else:
            lo = mid + 1
    assert lo == hi
    answer = min(ask('F', lo), ask('S', k - lo))
    return queries, answer


def run_case(binary, finland, sweden, k):
    n = len(finland)
    expected_queries, expected_answer = model(finland, sweden, k)
    assert expected_answer == sorted(finland + sweden, reverse=True)[k - 1]
    child = subprocess.Popen([str(binary)], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    selector = selectors.DefaultSelector()
    selector.register(child.stdout, selectors.EVENT_READ)
    buffered = bytearray()
    queries = []

    def read_line():
        deadline = time.monotonic() + 2
        while b'\n' not in buffered:
            if not selector.select(max(0, deadline - time.monotonic())):
                raise AssertionError('No flushed query/answer; stdin is still open')
            data = os.read(child.stdout.fileno(), 4096)
            assert data, 'Program exited without reporting an answer'
            buffered.extend(data)
        line, _, rest = buffered.partition(b'\n')
        buffered[:] = rest
        return line.decode('ascii')

    try:
        child.stdin.write(f'{n} {k}\n'.encode())
        child.stdin.flush()
        while True:
            line = read_line()
            parts = line.split()
            assert len(parts) == 2, f'Invalid output: {line!r}'
            country, value = parts[0], int(parts[1])
            if country == '!':
                assert value == expected_answer, (n, k, value, expected_answer)
                assert queries == expected_queries, 'Source/model query traces differ'
                # stdin stays open until the program has actually terminated.
                assert child.wait(timeout=2) == 0
                assert not buffered and child.stdout.read() == b'', 'Output after answer'
                assert child.stderr.read() == b''
                return len(queries)
            assert country in ('F', 'S'), line
            assert 1 <= value <= n, line
            queries.append((country, value))
            assert len(queries) <= 36
            score = (finland if country == 'F' else sweden)[value - 1]
            child.stdin.write(f'{score}\n'.encode())
            child.stdin.flush()
    finally:
        if child.poll() is None:
            child.kill()
        child.wait()
        selector.close()
        child.stdin.close()
        child.stdout.close()
        child.stderr.close()


def cases():
    # Every ownership assignment and every rank for small contests.
    for n in range(1, 5):
        values = set(range(1, 2*n + 1))
        for chosen in itertools.combinations(sorted(values), n):
            f = sorted(chosen, reverse=True)
            s = sorted(values - set(chosen), reverse=True)
            for k in range(1, 2*n + 1):
                yield f, s, k
    rng = random.Random(3305)
    for _ in range(150):
        n = rng.randint(1, 300)
        values = rng.sample(range(1, 1_000_000_001), 2*n)
        yield sorted(values[:n], reverse=True), sorted(values[n:], reverse=True), rng.randint(1, 2*n)
    # Maximum n, opposite ownership orders, interleaving, endpoint scores.
    n = 100_000
    for f, s in [
        (list(range(2*n, n, -1)), list(range(n, 0, -1))),
        (list(range(n, 0, -1)), list(range(2*n, n, -1))),
        (list(range(2*n, 0, -2)), list(range(2*n-1, 0, -2))),
        ([1_000_000_000-i for i in range(n)], list(range(n, 0, -1))),
    ]:
        for k in [1, 2, n-1, n, n+1, 2*n-1, 2*n]:
            yield f, s, k


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='coqcp-3305-') as folder:
        binary = args.binary.resolve() if args.binary else Path(folder) / 'solution'
        if not args.binary:
            subprocess.run(['g++', '-std=c++20', '-O2', '-Wall', '-Wextra',
                            str(ROOT / 'generated-cpp/KthHighestScore.cpp'), '-o', str(binary)], check=True)
        count, maximum = 0, 0
        for f, s, k in cases():
            maximum = max(maximum, run_case(binary, f, s, k))
            count += 1
        print(f'{count} interactive cases passed; maximum observed queries: {maximum} (bound: 36)')


if __name__ == '__main__':
    main()
