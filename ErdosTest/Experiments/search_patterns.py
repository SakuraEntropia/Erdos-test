#!/usr/bin/env python3
"""
Search for modular / parametric patterns in Erdős–Straus solutions.

We test a set of *candidate parametric identities* — closed-form (x, y, z)
valid for every n in a given residue class mod m — verifying each exactly with
Fraction arithmetic over a finite range of n.

A candidate is "CONFIRMED (empirically)" iff it passes for every applicable
n ∈ [2, N]; this is numerical evidence, NOT a proof.

Also reports:
  - the residue classes mod 12 left UNCOVERED by these simple identities,
  - the lexicographically-smallest solution for those (hard) n,
  - all solutions for the small exceptional n = 2..12.

Usage:  python3 search_patterns.py [N]     (default N = 300)
"""

import sys
from fractions import Fraction


def solutions(n: int):
    """Exhaustive enumerator (same as brute_force.py); sorted triples."""
    sols = set()
    for x in range(n // 4 + 1, (3 * n) // 4 + 1):
        a = 4 * x - n
        if a <= 0:
            continue
        b = n * x
        for y in range(b // a + 1, (2 * b) // a + 1):
            num = a * y - b
            if num <= 0:
                continue
            den = b * y
            if den % num == 0:
                z = den // num
                if z >= y:
                    sols.add(tuple(sorted((x, y, z))))
    return sorted(sols)


def ok(n: int, xyz) -> bool:
    x, y, z = xyz
    return (x > 0 and y > 0 and z > 0 and
            Fraction(4, n) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z))


# Candidate parametric identities: (name, predicate n in class, formula n -> (x,y,z))
CANDIDATES = [
    ("n ≡ 0 (mod 2)   even n=2k    -> (k, 2k, 2k)",
     lambda n: n % 2 == 0,
     lambda n: (n // 2, n, n)),

    ("n ≡ 3 (mod 4)   n=4k+3       -> (k+1, 2(k+1)n, 2(k+1)n)",
     lambda n: n % 4 == 3,
     lambda n: ((n + 1) // 4, n * (n + 1) // 2, n * (n + 1) // 2)),

    ("n ≡ 0 (mod 3)   n=3k         -> (2k, 2k, 3k)",
     lambda n: n % 3 == 0,
     lambda n: (2 * (n // 3), 2 * (n // 3), n)),

    ("n ≡ 2 (mod 3)   n=3k+2       -> (k+1, n, (k+1)n)",
     lambda n: n % 3 == 2,
     lambda n: ((n + 1) // 3, n, n * (n + 1) // 3)),
]


def main(N: int) -> None:
    print("=== 1. Parametric identities: finite verification ===")
    print(f"range n ∈ [2, {N}]\n")
    all_pass = True
    for name, pred, formula in CANDIDATES:
        tested = 0
        bad = []
        for n in range(2, N + 1):
            if pred(n):
                tested += 1
                if not ok(n, formula(n)):
                    bad.append(n)
        status = "OK" if not bad else f"FAIL at {bad}"
        if bad:
            all_pass = False
        print(f"[{status:12s}] {name}   (tested {tested} values)")

    print("\n=== 2. Residue coverage mod 12 ===")
    # A residue r mod 12 is "covered" if some identity applies to every n ≡ r.
    covered = set()
    for r in range(12):
        # does some candidate's predicate hold for all n ≡ r (mod 12)?
        # (identity classes are all unions of mod-12 residues, so test n = r+12k)
        for _, pred, _ in CANDIDATES:
            if all(pred(r + 12 * k) for k in range(3)):  # 3 samples suffice to see a residue class
                covered.add(r)
                break
    uncovered = sorted(set(range(12)) - covered)
    print("residue classes mod 12 covered by the 4 elementary identities:")
    print("   ", sorted(covered))
    print("residue classes mod 12 NOT covered (the 'hard' core):")
    print("   ", uncovered)

    print("\n=== 3. Smallest solution for the hard residue class n ≡ 1 (mod 12) ===")
    hard = [n for n in range(2, N + 1) if n % 12 == 1]
    for n in hard:
        s = solutions(n)
        print(f"  n = {n:4d}: {s[0] if s else 'NO SOLUTION'}")

    print("\n=== 4. All solutions for small exceptional n = 2..12 ===")
    for n in range(2, 13):
        print(f"  n = {n:2d}: {solutions(n)}")

    print("\nNOTE: empirical checks above are NOT proofs of the conjecture.")


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    main(N)
