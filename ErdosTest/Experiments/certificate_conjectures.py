#!/usr/bin/env python3
"""
Test CONJECTURES about the minimal certificate a = 4x - n for primes p ≡ 1 (mod 4).

For a = 3, x = (p+3)/4, and 4/p = 1/x + 1/y + 1/z forces
    1/y + 1/z = 3/(p·x)   <==>   (3y - M)(3z - M) = M^2,  M = p·x = p(p+3)/4.
So a=3 works  <=>  M^2 has a divisor u ≡ -M (mod 3).  Since gcd(M,3)=1 we need
u ≡ 2 (mod 3).  That exists  <=>  M has a prime factor ≡ 2 (mod 3) (to any power).
Equivalently (for prime p ≡ 1 mod 4, 3 ∤ p):
    a=3 works  <=>  p ≡ 2 (mod 3)  OR  (p+3)/4 has a prime factor ≡ 2 (mod 3).

This script VERIFIES that characterization against a direct search, and
investigates the analogous a=7 case.  All output is register B (computation).
"""

from sympy import isprime, factorint


def has_solution_with_a(p, a):
    """Direct search: is there a solution 4/p = 1/x+1/y+1/z with 4x - p = a ?"""
    if (p + a) % 4 != 0:
        return None
    x = (p + a) // 4
    if x <= 0:
        return None
    # a·y·z = p·x·(y+z), so z = p·x·y / (a·y - p·x), need a·y - p·x > 0.
    ymin = p * x // a + 1
    ymax = 2 * p * x // a + 2           # z >= y  =>  a·y - p·x <= p·x
    for y in range(ymin, ymax + 1):
        den = a * y - p * x
        if den <= 0:
            continue
        num = p * x * y
        if num % den != 0:
            continue
        z = num // den
        if z >= y:
            return (x, y, z)
    return None


def a3_char_pred(p):
    """Predicted a=3 solvability: p ≡ 2 (mod 3) or (p+3)/4 has a prime factor ≡ 2 (mod 3)."""
    if p % 3 == 2:
        return True
    m = (p + 3) // 4
    return any(q % 3 == 2 for q in factorint(m))


def main():
    N = 5000
    print(f"=== 1. a=3 characterization test, primes p ≡ 1 (mod 4), p ≤ {N} ===\n")
    mismatch = 0
    a3_fail = []
    for p in range(5, N + 1, 4):
        if not isprime(p):
            continue
        direct = has_solution_with_a(p, 3) is not None
        pred = a3_char_pred(p)
        if direct != pred:
            mismatch += 1
            print(f"  MISMATCH p={p}: direct={direct} pred={pred}")
        if not direct:
            a3_fail.append(p)
    print(f"  mismatches: {mismatch}  (should be 0)")
    print(f"  primes ≤ {N} with NO a=3 solution: {len(a3_fail)}")
    print(f"  first few: {a3_fail[:20]}")

    print("\n=== 2. minimal a = 4·x_min − p, primes p ≡ 1 (mod 4) ===\n")
    from collections import Counter
    amin_dist = Counter()
    amin_fail = []
    for p in range(5, N + 1, 4):
        if not isprime(p):
            continue
        found = None
        for a in range(3, 100, 4):           # a ≡ 3 (mod 4) necessarily
            s = has_solution_with_a(p, a)
            if s is not None:
                found = a
                break
        if found is None:
            amin_fail.append(p)
        else:
            amin_dist[found] += 1
    print(f"  primes ≤ {N} with NO solution for a ∈ {{3,7,11,...,99}}: {amin_fail}")
    print("  distribution of minimal a:")
    for k in sorted(amin_dist):
        print(f"    a = {k:>2}: {amin_dist[k]} primes")

    print("\n=== 3. a=7 characterization (analogous), primes p ≡ 1 (mod 4) ===\n")
    # a=7, x=(p+7)/4, M = p·x = p(p+7)/4, need divisor u of M^2 with u ≡ -M (mod 7).
    a7_fail = []
    for p in range(5, N + 1, 4):
        if not isprime(p):
            continue
        if has_solution_with_a(p, 7) is None:
            a7_fail.append(p)
    print(f"  primes ≤ {N} with NO a=7 solution: {len(a7_fail)}")
    print(f"  first few: {a7_fail[:20]}")

    print("\n=== 4. neither a=3 nor a=7 works ? (the minimal-a ≥ 11 case) ===\n")
    both_fail = [p for p in a3_fail if p in a7_fail]
    print(f"  primes ≤ {N} failing BOTH a=3 and a=7: {both_fail[:20] or 'NONE'}")

    print("\nNOTE: register B only — finite computation, no proof.")


if __name__ == "__main__":
    main()
