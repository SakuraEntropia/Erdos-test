#!/usr/bin/env python3
"""
NEW EXPERIMENTS (register B).

Part C: the six "hard" classes mod 840 (primes == 1,121,169,289,361,529 mod 840).
For each class: what is the minimal a = 4*x_min - p, and is there a pattern?

Part D: structure of the certificate divisor d in the minimal-a solution:
how large is d relative to M = p*x?  We report, for the a=3 solution and for the
minimal-a solution, the smallest divisor d | M^2 with d == -M (mod a) and ratio d/M.

Part E: corrected clean criterion for a=7 (divisor-residue set of x=(p+7)/4):
    a=7 works  <=>  D(x^2) meets {5 p^2, 5 p, 5} (mod 7),
with the two always-works classes p == 3, 6 (mod 7).  Verified vs full certificate.

All output register B (finite computation, no proof).
"""

from itertools import product
from sympy import isprime, factorint
from collections import Counter, defaultdict


def a_works(p, a):
    if (p + a) % 4 != 0:
        return False
    x = (p + a) // 4
    M = p * x
    fac = factorint(M)
    ps = list(fac)
    es = list(fac.values())
    for combo in product(*(range(2 * e + 1) for e in es)):
        d = 1
        for pi, ei in zip(ps, combo):
            d *= pi ** ei
        if (d + M) % a == 0:
            return True
    return False


def min_cert_divisor(p, a):
    """Smallest d | M^2 with d == -M (mod a), i.e. the certificate divisor. None if a fails."""
    if (p + a) % 4 != 0:
        return None
    x = (p + a) // 4
    M = p * x
    fac = factorint(M)
    ps = list(fac)
    es = list(fac.values())
    best = None
    for combo in product(*(range(2 * e + 1) for e in es)):
        d = 1
        for pi, ei in zip(ps, combo):
            d *= pi ** ei
        if (d + M) % a == 0:
            if best is None or d < best:
                best = d
    return best


def residue_set_of_square(m, q):
    """Set of residues mod q attained by divisors of m^2 (bounded exponents 0..2e_i)."""
    S = {1}
    for pi, e in factorint(m).items():
        r = pi % q
        powers = set()
        v = 1
        for k in range(2 * e + 1):
            powers.add(v)
            v = (v * r) % q
        new = set()
        for s in S:
            for pw in powers:
                new.add((s * pw) % q)
        S = new
    return S


def a7_clean(p):
    """a=7 works <=> D(x^2) meets {5 p^2, 5 p, 5} mod 7, x=(p+7)/4."""
    x = (p + 7) // 4
    D = residue_set_of_square(x, 7)
    targets = {(5 * p * p) % 7, (5 * p) % 7, (5) % 7}
    return bool(D & targets)


def main():
    # ============ Part C: six hard classes mod 840 ============
    print("=== C. six hard classes mod 840: minimal a ===")
    N = 600000
    classes = [1, 121, 169, 289, 361, 529]
    for c in classes:
        primes = [p for p in range(5, N + 1) if p % 840 == c and isprime(p)]
        amin_dist = Counter()
        record = None
        for p in primes:
            found = None
            for a in range(3, 300, 4):
                if a_works(p, a):
                    found = a
                    break
            if found is None:
                print(f"  class {c}: NO solution for a<=299 at p={p}")
                continue
            amin_dist[found] += 1
            if record is None or found > record[0]:
                record = (found, p)
        print(f"class {c} (mod 840): {len(primes)} primes, max minimal a = {record[0]} (at p={record[1]})")
        top = sorted(amin_dist.items())[:12]
        print(f"    minimal-a distribution (top): {top}")
        # smallest few primes and their minimal a
        print(f"    first primes -> (p, min a): {[(p, next(a for a in range(3,300,4) if a_works(p,a))) for p in primes[:8]]}")

    # ============ Part D: divisor structure ============
    print("\n=== D. certificate divisor d relative to M, minimal-a solutions ===")
    print("first 25 primes p==1(mod4) >= 73: (p, min a, d_min, d/M ratio as fraction)")
    shown = 0
    for p in range(73, 100000, 4):
        if not isprime(p):
            continue
        found = None
        for a in range(3, 300, 4):
            if a_works(p, a):
                found = a
                break
        if found is None:
            continue
        d = min_cert_divisor(p, found)
        x = (p + found) // 4
        M = p * x
        from fractions import Fraction
        print(f"  p={p:>5} a={found:>3} d={d:>6}  d/M={Fraction(d, M)}")
        shown += 1
        if shown >= 25:
            break

    # ============ Part E: corrected a=7 clean criterion ============
    print("\n=== E. corrected a=7 clean criterion (divisor-residue set) vs certificate ===")
    N2 = 100000
    primes = [p for p in range(5, N2 + 1, 4) if isprime(p) and p != 7]
    mism = 0
    for p in primes:
        if a7_clean(p) != a_works(p, 7):
            mism += 1
            if mism <= 5:
                print(f"  MISMATCH p={p}: clean={a7_clean(p)} cert={a_works(p,7)}")
    print(f"a=7 clean vs certificate: primes={len(primes)}, mismatches={mism} (should be 0)")
    # always-works classes
    for r in range(1, 7):
        sub = [p for p in primes if p % 7 == r]
        works = sum(1 for p in sub if a_works(p, 7))
        print(f"  p == {r} (mod 7): {len(sub)} primes, a=7 works for {works} ({works*100//max(len(sub),1)}%)")

    print("\nNOTE: register B only -- finite computation, no proof.")


if __name__ == "__main__":
    main()
