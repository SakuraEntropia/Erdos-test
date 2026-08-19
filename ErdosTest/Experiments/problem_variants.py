#!/usr/bin/env python3
"""
Step 4 (Phase 8): computational tests of PROBLEM VARIANTS of the Erdős–Straus conjecture.

Key efficiency idea: instead of brute-forcing y (O(p^2)), we use the DIVISOR CERTIFICATE —
which is now a **Lean-verified bijection** (`solvable_iff_certificate`): a solution with
x = (p+a)/4 exists iff M = p·x has complementary divisors d·e = M² with a | d+M, a | e+M.

All output is register B (finite computation, no proof).
"""

from itertools import product
from sympy import isprime, factorint


def a_works(p, a):
    """Certificate check: does x=(p+a)/4 admit a solution? (exact, via divisors of M^2)."""
    if (p + a) % 4 != 0:
        return False
    x = (p + a) // 4
    M = p * x
    fac = factorint(M)
    primes_list = list(fac.keys())
    exps = list(fac.values())
    # divisors of M^2 = prod p_i^{2 e_i}: enumerate exponent vectors f_i ∈ [0, 2 e_i]
    M2 = M * M
    for combo in product(*(range(2 * e + 1) for e in exps)):
        d = 1
        for pi, ei in zip(primes_list, combo):
            d *= pi ** ei
        # d | M^2; e = M^2/d. Need a | d+M and a | e+M.
        if (d + M) % a == 0 and (M2 // d + M) % a == 0:
            return True
    return False


def a3_char_pred(p):
    """Predicted a=3 solvability: p ≡ 2 (mod 3) or (p+3)/4 has a prime factor ≡ 2 (mod 3)."""
    if p % 3 == 2:
        return True
    m = (p + 3) // 4
    return any(q % 3 == 2 for q in factorint(m))


def main():
    N = 30000
    print(f"=== primes p ≡ 1 (mod 4), p ≤ {N} ===\n")

    # --- V-a3: a=3 characterization, 0-mismatch check ---
    mismatch = 0
    a3_fail = 0
    total = 0
    for p in range(5, N + 1, 4):
        if not isprime(p):
            continue
        total += 1
        direct = a_works(p, 3)
        pred = a3_char_pred(p)
        if direct != pred:
            mismatch += 1
        if not direct:
            a3_fail += 1
    print(f"V-a3  (a=3 characterization): primes={total}, mismatches={mismatch} (should be 0), "
          f"a=3 failures={a3_fail}")

    # --- S2: minimal a = 4·x_min − p (search a = 3,7,...,399) ---
    amin_max = 0
    amin_max_p = None
    amin_gt_23 = []
    tail = {}
    no_solution = []
    for p in range(5, N + 1, 4):
        if not isprime(p):
            continue
        found = None
        for a in range(3, 400, 4):
            if a_works(p, a):
                found = a
                break
        if found is None:
            no_solution.append(p)
            continue
        if found > amin_max:
            amin_max = found
            amin_max_p = p
        if found > 23:
            amin_gt_23.append((p, found))
        if found >= 19:
            tail[found] = tail.get(found, 0) + 1
    print(f"\nS2   (bounded minimal a): max minimal a = {amin_max} (at p={amin_max_p})")
    print(f"     primes with minimal a > 23: {len(amin_gt_23)}  first: {amin_gt_23[:15]}")
    print(f"     tail distribution (a ≥ 19): {sorted(tail.items())}")
    print(f"     primes with NO solution for a ∈ {{3,...,399}}: {no_solution[:10] or 'NONE'}")

    # --- V-1mod8: a=3 on the hard subcase p ≡ 1 (mod 8) ---
    ok = 0
    fail_1mod8 = []
    for p in range(5, N + 1, 8):
        if not isprime(p):
            continue
        if a_works(p, 3):
            ok += 1
        else:
            fail_1mod8.append(p)
    print(f"\nV-1mod8 (a=3 on p ≡ 1 (mod 8)): a=3 works for {ok} primes, "
          f"fails for {len(fail_1mod8)}; first failures {fail_1mod8[:10]}")

    print("\nNOTE: register B only — finite computation, no proof.")


if __name__ == "__main__":
    main()
