#!/usr/bin/env python3
"""
Brute-force check of the Erdős–Straus conjecture for small n.

Conjecture: for every n ≥ 2 there exist positive integers x, y, z with
    4/n = 1/x + 1/y + 1/z.

This script exhaustively enumerates ALL solutions (up to permutation) for each
n in [2, N] using exact integer arithmetic, and reports:
  - whether any n has NO solution (which would be a counterexample),
  - the number of solutions per n,
  - one example solution per n.

IMPORTANT: this checks only finitely many n. It does NOT prove the conjecture.

Usage:  python3 brute_force.py [N]      (default N = 100)
"""

import sys
from fractions import Fraction


def solutions(n: int):
    """Return all solutions (x, y, z) with x ≤ y ≤ z to 4/n = 1/x + 1/y + 1/z.

    Derivation: fix x; set a = 4x - n, b = n*x. Then
        1/y + 1/z = a/b,
    and assuming y ≤ z we get  b/a < y ≤ 2b/a.  For each such y, the forced
    z = b*y / (a*y - b) must be a positive integer.
    """
    sols = set()
    # The smallest variable lies in (n/4, 3n/4].
    for x in range(n // 4 + 1, (3 * n) // 4 + 1):
        a = 4 * x - n
        if a <= 0:
            continue
        b = n * x
        y_lo = b // a + 1          # y > b/a
        y_hi = (2 * b) // a        # y ≤ 2b/a  (since y ≤ z)
        for y in range(y_lo, y_hi + 1):
            num = a * y - b
            if num <= 0:
                continue
            den = b * y
            if den % num == 0:
                z = den // num
                if z >= y:         # keep y ≤ z canonical
                    sols.add(tuple(sorted((x, y, z))))
    return sorted(sols)


def verify(n: int, x: int, y: int, z: int) -> bool:
    """Exact check that 4/n = 1/x + 1/y + 1/z."""
    return Fraction(4, n) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)


def main(N: int) -> None:
    print(f"Checking Erdős–Straus for n = 2 .. {N}  (exact rational arithmetic)")
    print("-" * 72)
    failures = []
    total_solutions = 0
    for n in range(2, N + 1):
        s = solutions(n)
        if not s:
            failures.append(n)
            print(f"n = {n:4d}:  NO SOLUTION   <-- would be a counterexample")
            continue
        total_solutions += len(s)
        # exact sanity check of every returned solution
        for xyz in s:
            assert verify(n, *xyz), (n, xyz)
        print(f"n = {n:4d}:  {len(s):3d} solution(s),  smallest = {s[0]}")
    print("-" * 72)
    print(f"Total distinct solutions over n ∈ [2,{N}]: {total_solutions}")
    if failures:
        print(f"COUNTEREXAMPLES FOUND: {failures}")
    else:
        print(f"No counterexample up to n = {N} "
              f"(consistent with the known check to ~1e14).")


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    main(N)
