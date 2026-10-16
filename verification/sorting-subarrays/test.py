#!/usr/bin/env python3
"""Independent list-sort oracle and maximum-bound tests for the executable."""
import argparse
import itertools
import json
from pathlib import Path
import random
import subprocess
import time


def encode(a, k, queries, separator="\n"):
    lines = [f"{len(a)} {k} {len(queries)}", " ".join(map(str, a))]
    lines.extend(f"{l} {r}" for l, r in queries)
    return (separator.join(lines) + separator).encode()


def oracle(a, k, queries):
    a = a.copy()
    for l, r in queries:
        a[l - 1:r] = sorted(a[l - 1:r])
    return a[k - 1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("--random-cases", type=int, default=2000)
    parser.add_argument("--stress", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    executable = str(args.executable.resolve())
    rng = random.Random(26016)
    count = 0

    def check(a, k, queries, expected=None, separator="\n", timeout=180, final_newline=True):
        nonlocal count
        if expected is None:
            expected = oracle(a, k, queries)
        data = encode(a, k, queries, separator)
        if not final_newline:
            data = data[:-len(separator)]
        result = subprocess.run([executable], input=data,
                                capture_output=True, check=True, timeout=timeout)
        assert result.stdout == f"{expected}\n".encode(), (a, k, queries, expected, result.stdout)
        count += 1

    check([4, 2, 1, 3, 5], 3, [(1, 3), (2, 4)], 3)
    check([1], 1, [(1, 1)], final_newline=False)
    check([-1000000000, 1000000000], 1, [(1, 2)], final_newline=False)
    check([4, 2, 1, 3, 5], 3, [(1, 3), (2, 4)], 3, final_newline=False)
    check([-2, 1, -1], 2, [(1, 3)], separator="\r\n", final_newline=False)
    # Exhaust all binary arrays, selected positions, and single query ranges.
    for n in range(1, 6):
        intervals = [(l, r) for l in range(1, n + 1) for r in range(l, n + 1)]
        for values in itertools.product((-1, 1), repeat=n):
            for k in range(1, n + 1):
                for query in intervals:
                    check(list(values), k, [query])

    alphabet = [-1000000000, -999999999, -17, -2, -1, 1, 2, 17, 999999999, 1000000000]
    for case in range(args.random_cases):
        n = rng.choice([1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 65])
        a = [rng.choice(alphabet) for _ in range(n)]
        queries = []
        for _ in range(rng.randint(1, 70)):
            l = rng.randint(1, n)
            queries.append((l, rng.randint(l, n)))
        check(a, rng.randint(1, n), queries, separator="\r\n" if case % 3 == 0 else "\n")
    differential = count
    print(f"{differential} oracle comparisons passed", flush=True)

    stress_results = []
    if args.stress:
        n = 200000

        def stress(name, a, k, qs, expected):
            start = time.monotonic()
            check(a, k, qs, expected)
            seconds = round(time.monotonic() - start, 3)
            stress_results.append({"name": name, "n": len(a), "q": len(qs), "seconds": seconds})
            print(f"{name}: passed ({seconds}s)", flush=True)

        stress("singleton-many-queries", [-1000000000], 1, [(1, 1)] * n, -1000000000)
        stress("descending-full-sort", list(range(n, 0, -1)), n, [(1, n)], n)
        a = [rng.choice(alphabet) for _ in range(n)]
        qs = [(p, p) for p in (rng.randint(1, n) for _ in range(n))]
        stress("maximum-singleton-queries", a, n, qs, a[-1])
        qs = []
        for _ in range(n - 1):
            l, r = sorted((rng.randint(1, n), rng.randint(1, n)))
            qs.append((l, r))
        qs.append((1, n))
        k = n // 2
        stress("maximum-random-overlaps", a, k, qs, sorted(a)[k - 1])
        qs = [(i % (n // 2) + 1, n - i % (n // 2)) for i in range(n - 1)]
        qs.append((1, n))
        stress("maximum-nested-queries", a, 1, qs, min(a))

    # The wrapper rejects dimensions and values outside the formal contract.
    malformed_inputs = [b"0 1 1\n", b"1 1 0\n1\n", b"1 1 1\n0\n1 1\n",
                        b"1 1 1\n1\n1 2\n", b"1 1 1\n1\n1 1\n7\n",
                        b"1 1 1\n1\n1", b"1 1 1\n1000000001\n1 1\n",
                        b"1 1 1\n999999999999999999999999999\n1 1\n",
                        b"1 1 1\n--1\n1 1\n", b"1 1 1\n1x\n1 1\n",
                        b"200001 1 1\n"]
    for malformed in malformed_inputs:
        result = subprocess.run([executable], input=malformed, capture_output=True, timeout=5)
        assert result.returncode != 0 and not result.stdout
    report = {"oracle_comparisons": differential, "stress": stress_results,
              "invalid_inputs_rejected": len(malformed_inputs)}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
