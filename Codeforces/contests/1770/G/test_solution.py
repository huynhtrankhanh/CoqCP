"""Independent executable oracles; these tests are not a Rocq certificate."""
import argparse
import itertools
from pathlib import Path
import random
import subprocess
import time

MOD = 998244353
ROOT = Path(__file__).resolve().parents[4]


def enumerate_masks(s):
    best, ways = -1, 0
    for mask in range(1 << len(s)):
        balance, retained = 0, 0
        for i, ch in enumerate(s):
            if mask >> i & 1:
                balance += 1 if ch == "(" else -1
                retained += 1
                if balance < 0:
                    break
        else:
            if balance == 0:
                if retained > best:
                    best, ways = retained, 0
                if retained == best:
                    ways += 1
    return ways % MOD


def quadratic_oracle(s):
    # For each retained-prefix balance, store its greatest length and the
    # number of index masks attaining that length. No minimum-prefix split,
    # special-position recurrence, binomial coefficients, or NTT is used.
    states = {0: (0, 1)}
    for ch in s:
        following = {}

        def add(balance, length, ways):
            old_length, old_ways = following.get(balance, (-1, 0))
            if length > old_length:
                following[balance] = length, ways
            elif length == old_length:
                following[balance] = length, (old_ways + ways) % MOD

        for balance, (length, ways) in states.items():
            add(balance, length, ways)  # delete this index
            new_balance = balance + (1 if ch == "(" else -1)
            if new_balance >= 0:
                add(new_balance, length + 1, ways)  # retain this index
        states = following
    return states[0][1]


def run(executable, s, ending="\n"):
    result = subprocess.run(
        [str(executable)], input=(s + ending).encode(), capture_output=True,
        timeout=15, check=True,
    )
    value = result.stdout.decode("ascii")
    if not value.endswith("\n") or not value[:-1].isdigit():
        raise AssertionError((s[:100], "malformed output", value))
    return int(value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--executable", type=Path, required=True)
    parser.add_argument("--large", action="store_true")
    args = parser.parse_args()
    rng = random.Random(1770)
    count = 0
    for n in range(1, 11):
        for chars in itertools.product("()", repeat=n):
            s = "".join(chars)
            expected = enumerate_masks(s)
            assert quadratic_oracle(s) == expected, s
            assert run(args.executable, s) == expected, s
            count += 1
    for n in (33, 65, 100, 250, 500, 1000):
        cases = ["".join(rng.choices("()", k=n)) for _ in range(20)]
        cases += ["(" * n, ")" * n, "())" * (n // 3), "(()" * (n // 3)]
        cases += ["(" * (n // 4) + ")" * (n // 2) + "(" * (n // 4)]
        for s in cases:
            expected = quadratic_oracle(s)
            for ending in ("\n", "\r\n", ""):
                actual = run(args.executable, s, ending)
                assert actual == expected, (s, ending, expected, actual)
                count += 1
    print(f"PASS: {count} independent oracle comparisons", flush=True)

    if args.large:
        cases = {
            "all-open": "(" * 500000,
            "all-close": ")" * 500000,
            "balanced": "()" * 250000,
            "random": "".join(rng.choices("()", k=500000)),
            "record-valleys": ("(" * 1000 + ")" * 2000) * 166 + "(" * 2000,
            "dense-records": "())" * 166666 + ")(",
            "single-valley": "(" * 125000 + ")" * 250000 + "(" * 125000,
        }
        for name, s in cases.items():
            start = time.monotonic()
            answer = run(args.executable, s)
            elapsed = time.monotonic() - start
            assert 0 <= answer < MOD
            if name in ("all-open", "all-close", "balanced"):
                assert answer == 1
            if name == "single-valley":
                # Retain every initial open, choose 125000 middle closes,
                # and delete every final open. This is C(250000,125000).
                # Compute it independently in linear time.
                numerator = denominator = 1
                for i in range(1, 125001):
                    numerator = numerator * (125000 + i) % MOD
                    denominator = denominator * i % MOD
                choose = numerator * pow(denominator, MOD - 2, MOD) % MOD
                assert answer == choose
            print(f"{name}: n={len(s)}, {elapsed:.3f}s, answer={answer}", flush=True)


if __name__ == "__main__":
    main()
