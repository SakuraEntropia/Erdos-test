#!/usr/bin/env python3
"""
Symbolic search for PARAMETRIC POLYNOMIAL IDENTITIES for 4/n = 1/x + 1/y + 1/z.

A *parametric identity* for a residue class r (mod m) is a triple of polynomials
x(k), y(k), z(k) in Z[k] such that
    4/(m·k + r) = 1/x(k) + 1/y(k) + 1/z(k)
holds IDENTICALLY (as rational functions in k), with x,y,z positive for all k>=1.

This is an EXACT symbolic check, not a finite numerical test: we use polynomial
arithmetic over the integers. For candidate (x, y) we FORCE
    z = n·x·y / (4·x·y - n·(x+y)),   n = m·k + r,
and require z to be a polynomial in k with nonnegative integer coefficients
(i.e. the exact polynomial division of nxy by 4xy - n(x+y) has remainder 0 and a
nonnegative integer quotient).

If a FINITE set of such identities covered every residue class mod some M, the
conjecture would be PROVEN. The goal here is to see which classes bounded-degree
identities can cover, and in particular whether the "hard core" n ≡ 1 (mod 4) is
reachable.

Polynomials are lists of integer coefficients: p[d] = coefficient of k^d.
"""

import sys
from itertools import product


# ---------- polynomial helpers over Z ----------

def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] += a * b
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [ (p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
             for i in range(n) ]


def psub(p, q):
    n = max(len(p), len(q))
    return [ (p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0)
             for i in range(n) ]


def pscale(c, p):
    return [c * a for a in p]


def pdivmod(num, den):
    """Exact long division num/den over Z. Returns (q, r) with num = q*den + r,
       deg r < deg den, or None if some step is not exactly divisible."""
    num = trim(num[:])
    den = trim(den[:])
    if all(c == 0 for c in den):
        return None
    ddeg = len(den) - 1
    dlead = den[-1]
    q = [0] * max(1, len(num) - len(den) + 1)
    r = trim(num[:])
    while len(r) >= len(den):
        if r[-1] == 0:
            r.pop()
            continue
        if r[-1] % dlead != 0:
            return None
        f = r[-1] // dlead
        tdeg = len(r) - 1 - ddeg
        q[tdeg] = f
        for i in range(len(den)):
            r[tdeg + i] -= f * den[i]
        while len(r) > 1 and r[-1] == 0:
            r.pop()
    return trim(q), trim(r)


def poly_ok(p):
    """nonnegative integer coeffs, constant term >= 1 (=> positive for k>=1)."""
    return p and p[0] >= 1 and all(c >= 0 for c in p)


def z_of(x, y, n):
    """z = n·x·y / (4·x·y - n·(x+y)); return polynomial list, or None if invalid."""
    num = pmul(n, pmul(x, y))
    den = psub(pscale(4, pmul(x, y)), pmul(n, padd(x, y)))
    res = pdivmod(num, den)
    if res is None:
        return None
    q, r = res
    if trim(r) != [0]:
        return None
    if not poly_ok(q):
        return None
    return trim(q)


def poly_str(p):
    if not p:
        return "0"
    terms = []
    for d in range(len(p) - 1, -1, -1):
        c = p[d]
        if c == 0:
            continue
        if d == 0:
            terms.append(str(c))
        elif d == 1:
            terms.append(("k" if c == 1 else f"{c}*k"))
        else:
            terms.append((f"k^{d}" if c == 1 else f"{c}*k^{d}"))
    return " + ".join(terms)


def poly_candidates(deg, hi):
    """coeffs c_i in [0..hi], constant term in [1..hi]."""
    for coeffs in product(range(hi + 1), repeat=deg + 1):
        if coeffs[-1] == 0:      # constant term positive
            continue
        yield list(reversed(coeffs))   # [c_deg, ..., c_0] -> list index = degree


def verify_identity(m, r, xyz):
    """Independently verify 4/n = 1/x+1/y+1/z identically (via cleared form)."""
    from fractions import Fraction
    x, y, z = xyz
    for kk in range(1, 6):
        n = m * kk + r
        xv = sum(c * kk**d for d, c in enumerate(x))
        yv = sum(c * kk**d for d, c in enumerate(y))
        zv = sum(c * kk**d for d, c in enumerate(z))
        if Fraction(4, n) != Fraction(1, xv) + Fraction(1, yv) + Fraction(1, zv):
            return False
    return True


def search(m, r, degx, degy, hi):
    n = [r, m]
    for x in poly_candidates(degx, hi):
        for y in poly_candidates(degy, hi):
            z = z_of(x, y, n)
            if z is not None:
                return (x, y, z)
    return None


def main():
    hi = 12
    print("=== 1. AFFINE identities (deg x,y <= 1, coeffs 0..%d), m = 2..%d ===\n" % (hi, 12))
    covered = {}
    for m in range(2, 13):
        for r in range(m):
            res = search(m, r, 1, 1, hi)
            if res is not None:
                assert verify_identity(m, r, res), (m, r)
                covered[(m, r)] = res

    # print one example per residue class, compactly
    seen = set()
    for m in range(2, 13):
        for r in range(m):
            if (m, r) in covered:
                x, y, z = covered[(m, r)]
                print(f"  n ≡ {r:2d} (mod {m:2d}):  x={poly_str(x)}, y={poly_str(y)}, z={poly_str(z)}")

    print(f"\nTotal residue classes (m,r), m<=12, covered by an affine identity: {len(covered)}")

    # does any affine identity cover a class r ≡ 1 (mod 4)?
    bad = [(m, r) for (m, r) in covered if r % 4 == 1]
    print(f"Classes r ≡ 1 (mod 4) covered by affine identities (m<=12): {sorted(bad)}")

    print("\n=== 2. Larger-coefficient affine search over r ≡ 1 (mod 4) only ===")
    hi2 = 60
    hit = []
    for m in (4, 8, 12, 16):
        for r in range(1, m, 4):
            res = search(m, r, 1, 1, hi2)
            if res is not None:
                hit.append((m, r, res))
    print(f"  (coeffs 0..{hi2}); affine identities found for r ≡ 1 (mod 4): {hit or 'NONE'}")

    print("\n=== 3. QUADRATIC identities (deg x<=1, deg y<=2) for n ≡ 1 (mod 4) ===")
    hi3 = 8
    found = []
    for m in (4, 8, 12, 16):
        for r in range(1, m, 4):
            res = search(m, r, 1, 2, hi3)
            if res is not None:
                assert verify_identity(m, r, res), (m, r)
                x, y, z = res
                found.append((m, r, x, y, z))
                print(f"  n ≡ {r:2d} (mod {m:2d}):  x={poly_str(x)}, y={poly_str(y)}, z={poly_str(z)}")
    if not found:
        print("  (none found with coeffs 0..%d)" % hi3)

    print("\nNOTE: identities found here are PROVEN (exact division). 'NONE found' is")
    print("      bounded-search evidence, not a proof of impossibility.")


if __name__ == "__main__":
    main()
