#!/usr/bin/env python3
"""
NEW EXPERIMENTS (register B).

Part A: two NEW explicit parametric identities coming out of the one-sided divisor
criterion (d=p and d=x are divisors of M^2 hitting -M mod q).  For prime q = 3 mod 4:

  (A1) p == -4 (mod q):  d = p   =>  4/p = 1/x + 1/y + 1/z  with
        x=(p+q)/4, y=p(p+q+4)/(4q), z=p(p+q)(p+q+4)/(16q).

  (A2) p == -1 (mod q):  d = x   =>  4/p = 1/x + 1/y + 1/z  with
        x=(p+q)/4, y=(p+q)(p+1)/(4q), z=p(p+q)(p+1)/(4q).

Part B: growth of minimal a = 4*x_min - p over primes p == 1 (mod 4): which values
3,7,11,15,19,23,27,... actually occur, their first occurrence, and record holders.

All output register B (finite computation, no proof).
"""

from fractions import Fraction
from itertools import product
from sympy import isprime, factorint


# ---------------- certificate check (one-sided divisor criterion) ----------------
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


def main():
    # ============ Part A: explicit identities ============
    print("=== A. Two explicit parametric identities (exact Fraction check) ===\n")
    for q in [3, 7, 11, 19, 23, 31]:
        n1 = n2 = 0
        bad1 = bad2 = []
        for p in range(5, 100001, 4):
            if not isprime(p) or p == q:
                continue
            if p % q == (-4) % q:   # p == -4 (mod q)
                n1 += 1
                x = (p + q) // 4
                y = p * (p + q + 4) // (4 * q)
                z = p * (p + q) * (p + q + 4) // (16 * q)
                if not (y > 0 and z > 0 and p * (p + q + 4) % (4 * q) == 0
                        and Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)):
                    bad1.append(p)
            if p % q == (-1) % q:   # p == -1 (mod q)
                n2 += 1
                x = (p + q) // 4
                y = (p + q) * (p + 1) // (4 * q)
                z = p * (p + q) * (p + 1) // (4 * q)
                if not (y > 0 and z > 0 and (p + q) * (p + 1) % (4 * q) == 0
                        and Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)):
                    bad2.append(p)
        print(f"q={q:>2}:  p==-4: {n1} primes, failures={len(bad1)}  "
              f"|  p==-1: {n2} primes, failures={len(bad2)}   (both should be 0)")
    print("  (A1/A2 cover disjoint residue classes p mod q; note for q=3 both are p==2 mod 3)")

    # ============ Part B: minimal a growth ============
    print("\n=== B. minimal a = 4*x_min - p, primes p == 1 (mod 4) ===")
    N = 300000
    CAP = 500
    from collections import Counter
    amin_dist = Counter()
    first_occur = {}
    record_holder = []          # (p, a) whenever a exceeds all previous
    record_max = 0
    no_solution = []
    primes = [p for p in range(5, N + 1, 4) if isprime(p)]
    for p in primes:
        found = None
        for a in range(3, CAP, 4):
            if a_works(p, a):
                found = a
                break
        if found is None:
            no_solution.append(p)
            continue
        amin_dist[found] += 1
        if found not in first_occur:
            first_occur[found] = p
        if found > record_max:
            record_max = found
            record_holder.append((p, found))
    print(f"primes p==1(mod4) <= {N}: {len(primes)}")
    print(f"no solution for a in {{3,7,...,{CAP-1}}}: {no_solution[:10] or 'NONE'}  (count={len(no_solution)})")
    print(f"max minimal a found: {record_max}")
    print("record holders (p, a) [a strictly increasing]:")
    for (p, a) in record_holder:
        print(f"    a = {a:>3} first reached at p = {p}")
    print("distribution of minimal a (values that occur):")
    for a in sorted(amin_dist):
        print(f"    a = {a:>3}: {amin_dist[a]:>6} primes   (first at p={first_occur[a]})")
    # which a == 3 (mod 4) do NOT occur as minimal a up to N?
    occ = set(amin_dist)
    missing = [a for a in range(3, record_max + 1, 4) if a not in occ]
    print(f"values a == 3 (mod 4) in [3,{record_max}] that DO NOT occur as minimal a: {missing}")

    print("\nNOTE: register B only -- finite computation, no proof.")


if __name__ == "__main__":
    main()
