#!/usr/bin/env python3
"""
Phase 11 — Attack Surface Discovery (Track D: computational).

Focus: the six hard residue classes  n ≡ 1, 121, 169, 289, 361, 529 (mod 840).
For each class we compute, for primes p ≡ c (mod 840):

  (1) the minimal certificate stratum  a  (smallest a ≡ 3 (mod 4) that works),
  (2) the minimal working divisor  d | M^2  (M = p(p+a)/4) with  d ≡ -M (mod a),
  (3) the factorisation of that d,

and contrast the six hard classes against a few "easy" classes (covered by
polynomial identities) to test whether the hard classes genuinely carry a
larger minimal `a` / more complicated certificate divisor.

All output is register B (finite computation, no proof).
"""

from itertools import product
from sympy import isprime, factorint
from math import gcd


def divisors_of_square(M):
    """All divisors of M^2 as a set (bounded exponents 0..2e_i)."""
    fac = factorint(M)
    ps = list(fac)
    es = list(fac.values())
    out = set()
    for combo in product(*(range(2 * e + 1) for e in es)):
        d = 1
        for pi, ei in zip(ps, combo):
            d *= pi ** ei
        out.add(d)
    return out


def two_sided_ok_with_witness(M, a):
    """Return (True, d) for the first d | M^2 with d ≡ -M (mod a) and M^2/d ≡ -M (mod a)."""
    M2 = M * M
    for d in sorted(divisors_of_square(M)):
        if (d + M) % a == 0 and (M2 // d + M) % a == 0:
            return (True, d)
    return (False, None)


def a_works_with_witness(p, a):
    """Full two-sided certificate for stratum a; returns (ok, d). M = p(p+a)/4."""
    if (p + a) % 4 != 0:
        return (False, None)
    M = p * (p + a) // 4
    return two_sided_ok_with_witness(M, a)


def minimal_a_with_witness(p, amax=200):
    for a in range(3, amax, 4):
        ok, d = a_works_with_witness(p, a)
        if ok:
            return (a, d)
    return (None, None)


def primes_in_class(c, m, limit):
    out = []
    x = c
    if x < 5:
        x += m
    while x <= limit:
        if isprime(x):
            out.append(x)
        x += m
    return out


def fmt_factor(n):
    f = factorint(n)
    return "*".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items()))


def main():
    HARD = [1, 121, 169, 289, 361, 529]
    EASY = [5, 61, 113]   # ≡ 1 (mod 4), NOT in the six hard classes (covered by identities)
    LIMIT = 5_000_000

    print("=" * 78)
    print("HARD six classes: first primes p ≡ c (mod 840), minimal a, minimal working d")
    print("=" * 78)
    for c in HARD:
        ps = primes_in_class(c, 840, LIMIT)[:10]
        rows = []
        for p in ps:
            a, d = minimal_a_with_witness(p)
            rows.append((p, a, d))
        print(f"\nclass {c:>3} (mod 840): {len(ps)} primes shown")
        for p, a, d in rows:
            if a is None:
                print(f"   p={p:>8}  minimal a = NONE (up to 200)")
            else:
                print(f"   p={p:>8}  minimal a = {a:>3}   d = {d:>10} = {fmt_factor(d)}")

    print()
    print("=" * 78)
    print("per-class minimal-a statistics (all p ≡ c (mod 840), p <= %d)" % LIMIT)
    print("=" * 78)
    for c in HARD + EASY:
        ps = primes_in_class(c, 840, LIMIT)
        stats = []
        none = 0
        for p in ps:
            a, _ = minimal_a_with_witness(p)
            if a is None:
                none += 1
            else:
                stats.append(a)
        if stats:
            mean = sum(stats) / len(stats)
            print(f"  class {c:>3}: n={len(ps):>3}  min_a={min(stats):>3}  "
                  f"median_a={sorted(stats)[len(stats)//2]:>3}  max_a={max(stats):>3}  "
                  f"mean_a={mean:5.1f}  (none={none})")
        else:
            print(f"  class {c:>3}: n={len(ps)}  (no primes found)")

    print()
    print("=" * 78)
    print("evolution of minimal a within the HARD classes (first 8 records per class)")
    print("=" * 78)
    for c in HARD:
        ps = primes_in_class(c, 840, LIMIT)
        cur = 0
        rec = []
        for p in ps:
            a, _ = minimal_a_with_witness(p)
            if a is not None and a > cur:
                rec.append((p, a))
                cur = a
        print(f"  class {c:>3}: record (p, minimal a) sequence = {rec[:8]}")

    print()
    print("NOTE: register B only — finite computation, no proof.")


if __name__ == "__main__":
    main()
