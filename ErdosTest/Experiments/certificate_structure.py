#!/usr/bin/env python3
"""
Explore the DIVISOR-CERTIFICATE structure of Erdős–Straus solutions.

For a solution 4/n = 1/x + 1/y + 1/z (x ≤ y ≤ z), the certificate is
    a = 4x - n,   d = a·y - n·x,   e = a·z - n·x
satisfying (proved in Lean, Certificate.lean):
    a + n = 4x,  a·y = d + n·x,  a·z = e + n·x,  d·e = (n·x)^2.
This script (i) independently VERIFIES those identities for every solution it
finds, (ii) verifies the parity theorem (n odd ⟹ at most one odd denominator),
and (iii) tests candidate CONJECTURES about the minimal certificate.

All output here is COMPUTATIONAL EVIDENCE (register B), never a proof.
"""

from fractions import Fraction


def solutions(n):
    """All canonical solutions x <= y <= z to 4/n = 1/x+1/y+1/z, exact."""
    out = []
    for x in range(n // 4 + 1, n + 1):          # x > n/4 (Lemma B), x < n for canonical min
        a = 4 * x - n
        if a <= 0:
            continue
        # need y in (n*x/a, ...) with a*y - n*x > 0 and z = n*x*y/(a*y - n*x) integer >= y
        ymin = max(x, n * x // a + 1)
        # upper bound for y: z >= y  =>  n*x*y/(a*y - n*x) >= y  =>  a*y - n*x <= n*x
        #  => a*y <= 2*n*x  =>  y <= 2*n*x/a
        ymax = 2 * n * x // a + 2
        for y in range(ymin, ymax + 1):
            den = a * y - n * x
            if den <= 0:
                continue
            num = n * x * y
            if num % den != 0:
                continue
            z = num // den
            if z >= y:
                out.append((x, y, z))
    return out


def verify_certificate(n, x, y, z):
    a = 4 * x - n
    d = a * y - n * x
    e = a * z - n * x
    ok = (a > 0 and d > 0 and e > 0 and a + n == 4 * x
          and a * y == d + n * x and a * z == e + n * x
          and d * e == (n * x) * (n * x))
    parity_ok = ((x % 2) + (y % 2) + (z % 2)) <= 1 if n % 2 == 1 else True
    return ok, parity_ok, a, d, e


def main():
    N = 300
    print(f"=== 1. Verify certificate + parity for ALL solutions, n = 2..{N} ===\n")
    total = 0
    cert_fail = 0
    parity_fail = 0
    for n in range(2, N + 1):
        for (x, y, z) in solutions(n):
            total += 1
            ok, pok, a, d, e = verify_certificate(n, x, y, z)
            if not ok:
                cert_fail += 1
                print(f"  CERT FAIL n={n} {x,y,z}")
            if not pok:
                parity_fail += 1
                print(f"  PARITY FAIL n={n} {x,y,z}")
    print(f"  total solutions: {total}")
    print(f"  certificate failures: {cert_fail}")
    print(f"  parity failures: {parity_fail}")
    print("  (both should be 0 — matching the Lean theorems)\n")

    print("=== 2. Primes p ≡ 1 (mod 4): minimal x, minimal a = 4x−n, and whether a=3 works ===\n")
    from sympy import isprime
    print(f"{'p':>4} {'x_min':>6} {'a_min':>6} {'a≡3?':>6} {'a=3 works?':>12} {'(x,y,z) for a=3':>30}")
    a3_failures = []
    for p in range(5, 300, 4):
        if not isprime(p):
            continue
        sols = solutions(p)
        xmin = min(s[0] for s in sols)
        amin = 4 * xmin - p
        a_is_3 = amin == 3
        a3 = [s for s in sols if 4 * s[0] - p == 3]
        works3 = len(a3) > 0
        if not works3:
            a3_failures.append(p)
        print(f"{p:>4} {xmin:>6} {amin:>6} {str(a_is_3):>6} {str(works3):>12} {str(a3[:1]):>30}")
    print(f"\n  primes p ≡ 1 (mod 4) up to {N} with NO a=3 solution: {a3_failures}")

    print("\n=== 3. Minimal a over ALL n ≡ 1 (mod 4) (not just primes) ===\n")
    from collections import Counter
    amin_dist = Counter()
    for n in range(5, N + 1, 4):
        sols = solutions(n)
        xmin = min(s[0] for s in sols)
        amin_dist[4 * xmin - n] += 1
    print("  distribution of a_min = 4*x_min - n over n ≡ 1 (mod 4):")
    for k in sorted(amin_dist):
        print(f"    a_min = {k:>2}: {amin_dist[k]} values of n")

    print("\nNOTE: everything above is finite computation (register B). 'No a=3' is")
    print("      bounded-search evidence, NOT a proof.")


if __name__ == "__main__":
    main()
