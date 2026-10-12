#!/usr/bin/env python3
"""Integer-only verification route for the G/GA certificate families.

This is a new verifier, not a claim that the archived complete run was repeated.
All classification uses outward rational bounds with denominator 2**32; undecided
comparisons use an exact polynomial predicate. No floating-point comparison can
cause acceptance. The supported domain is 1 <= n,x <= 100_000_000, 0 <= w <= 8,
0 < f <= r <= 100_000_000, and 0 <= P/Q <= 4.

Python >= 3.9 and NumPy are required. CLI examples:
  python integer_replay.py points 4000 4025 4029 4035 4100 10000 30000
  python integer_replay.py pern 4000 30000 --output integer_pern.jsonl
  python integer_replay.py blocks exact_blocks.jsonl --output integer_blocks.jsonl
A failed sufficient criterion is NOT a counterexample to the original theorem.
"""
import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
import numpy as np

LIMIT = 100_000_000
SCALE = 1 << 32
MASK = np.uint64(SCALE - 1)


def le_exact(f: int, r: int, w: int, x: int, P: int, Q: int) -> bool:
    """Decide f/r - 2**w/sqrt(2*x) <= sqrt(P/Q) by integer arithmetic."""
    f, r, w, x, P, Q = map(int, (f, r, w, x, P, Q))
    if not (0 < f <= r and 0 <= w and x > 0 and P >= 0 and Q > 0):
        raise ValueError('Invalid exact-comparison arguments')
    X = 2*x*Q*f*f - 2*x*P*r*r - (4**w)*Q*r*r
    return X <= 0 or X*X <= (4**(w+1))*(r**4)*2*x*P*Q


def arrays(N: int):
    if not 1 <= N <= LIMIT:
        raise ValueError('N outside the proved fixed-width domain')
    nv = (N+1)//2
    rad = np.ones(nv, dtype=np.uint64)
    phi = np.ones(nv, dtype=np.uint64)
    omega = np.zeros(nv, dtype=np.uint8)
    sieve = np.ones(N+1, dtype=np.bool_)
    sieve[:2] = False
    for p in range(2, math.isqrt(N)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    for p0 in np.flatnonzero(sieve):
        p = int(p0)
        if p == 2:
            continue
        sl = slice((p-1)//2, nv, p)
        rad[sl] *= p
        phi[sl] *= p-1
        omega[sl] += 1
    validate(rad, phi, omega)
    return rad, phi, omega


def validate(rad, phi, omega):
    if not (rad.shape == phi.shape == omega.shape):
        raise ValueError('Array shapes differ')
    if len(rad) and (np.any(rad < 1) or np.any(rad > LIMIT)
                    or np.any(phi < 1) or np.any(phi > rad)
                    or np.any(omega > 8)):
        raise ValueError('Input outside proved arithmetic domain')


def weight_bounds(rad, phi, omega, x: int):
    validate(rad, phi, omega)
    if not 1 <= x <= LIMIT:
        raise ValueError('x outside proved arithmetic domain')
    # phi*2**32 < 2**59. Signed differences below have size < 2**40.
    glo = ((phi*np.uint64(SCALE))//rad).astype(np.int64)
    ghi = glo+1
    a = math.isqrt(2*x*SCALE*SCALE)
    elo, ehi = [], []
    for w in range(9):
        num = (1 << w)*SCALE*SCALE
        elo.append(num//(a+1))
        ehi.append((num+a-1)//a)
    lo = glo-np.asarray(ehi, dtype=np.int64)[omega]
    hi = ghi-np.asarray(elo, dtype=np.int64)[omega]
    return lo, hi


def ceil_scaled_square(w, x: int):
    """ceil(x*(w/2**32)**2), without overflowing a 64-bit product."""
    if np.any(w < 0) or np.any(w >= SCALE):
        raise ValueError('Scaled positive weight outside [0,2**32)')
    w = w.astype(np.uint64)
    z = w*w                 # z < 2**64
    p0 = np.uint64(x)*(z & MASK)   # p0 < 2**59
    p1 = np.uint64(x)*(z >> np.uint64(32)) + (p0 >> np.uint64(32))
    rem = ((p1 & MASK) != 0) | ((p0 & MASK) != 0)
    return ((p1 >> np.uint64(32))+rem.astype(np.uint64)).astype(np.int64)


def kappa_all(rad, phi, omega, x: int):
    lo, hi = weight_bounds(rad, phi, omega, x)
    lower = ceil_scaled_square(np.maximum(lo, 0), x)
    upper = ceil_scaled_square(np.maximum(hi, 0), x)
    if np.any(lower > upper):
        raise AssertionError('Invalid directed interval')
    out = lower.copy()
    idx = np.flatnonzero(lower != upper)
    for i0 in idx:
        i = int(i0)
        left, right = int(lower[i]), int(upper[i])
        while left < right:
            mid = (left+right)//2
            if le_exact(phi[i], rad[i], omega[i], x, mid, x):
                right = mid
            else:
                left = mid+1
        out[i] = left
    return out, len(idx)


def count_le(rad, phi, omega, x: int, P: int, Q: int):
    if not (P >= 0 and Q > 0 and P <= 4*Q):
        raise ValueError('Threshold outside the supported domain')
    lo, hi = weight_bounds(rad, phi, omega, x)
    tlo = math.isqrt((P*SCALE*SCALE)//Q)
    thi = tlo+1
    accepted = hi <= tlo
    rejected = lo > thi
    idx = np.flatnonzero(~(accepted | rejected))
    count = int(np.count_nonzero(accepted))
    for i0 in idx:
        i = int(i0)
        count += int(le_exact(phi[i], rad[i], omega[i], x, P, Q))
    return count, len(idx)


def y1_from_kappa(kap, nodd: int):
    if np.any(kap == 0):
        return 0
    counts = np.bincount(np.minimum(kap, nodd+1), minlength=nodd+2)
    cumulative = np.cumsum(counts, dtype=np.int64)
    hits = np.flatnonzero((np.arange(len(cumulative)) >= 1)
                         & (cumulative >= np.arange(len(cumulative))))
    if not len(hits):
        raise AssertionError('No first failure: invalid inputs or implementation')
    return int(hits[0])


def check_n(n: int, data):
    if n < 6:
        return {'n': n, 'vacuous': True, 'criterion_ok': True}
    q, m = n//2, n//6
    T = q+n//3-m
    nodd = (n+1)//2
    rad, phi, omega = (a[:nodd] for a in data)
    kap, nk = kappa_all(rad, phi, omega, q)
    y1 = y1_from_kappa(kap, nodd)
    nga, ng = count_le(rad, phi, omega, n, n-T+2*m-1, n)
    return {'n': n, 'y1': y1, 'NGA': nga, 'm': m,
            'criterion_ok': nga <= y1-m, 'exact_fallbacks': nk+ng,
            'arithmetic': 'integer-only'}


def check_block(Nlo: int, Nhi: int, data, chunk: int = 1_000_000):
    if not 6 <= Nlo <= Nhi <= LIMIT:
        raise ValueError('Invalid block')
    qlo, mhi, nodd = Nlo//2, Nhi//6, (Nhi+1)//2
    threshold = Fraction(1, 3)+Fraction(7, 6*Nlo)+Fraction(2*mhi-1, Nlo)
    counts = np.zeros(nodd+2, dtype=np.int64)
    nga = fallbacks = 0
    for start in range(0, nodd, chunk):
        stop = min(nodd, start+chunk)
        rad, phi, omega = (a[start:stop] for a in data)
        kap, nk = kappa_all(rad, phi, omega, qlo)
        counts += np.bincount(np.minimum(kap, nodd+1), minlength=nodd+2)
        c, nc = count_le(rad, phi, omega, Nlo,
                         threshold.numerator, threshold.denominator)
        nga += c
        fallbacks += nk+nc
    if counts[0]:
        y1 = 0
    else:
        cumulative = np.cumsum(counts, dtype=np.int64)
        hit = np.flatnonzero((np.arange(len(counts)) >= 1)
                            & (cumulative >= np.arange(len(counts))))
        if not len(hit):
            raise AssertionError('Invalid block first failure')
        y1 = int(hit[0])
    return {'Nlo': Nlo, 'Nhi': Nhi, 'y1': y1, 'NGA': nga, 'mhi': mhi,
            'criterion_ok': nga <= y1-mhi, 'exact_fallbacks': fallbacks,
            'arithmetic': 'integer-only'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['points', 'pern', 'blocks'])
    parser.add_argument('args', nargs='+')
    parser.add_argument('--output', type=Path)
    ns = parser.parse_args()
    if ns.mode == 'blocks':
        rows = [json.loads(s) for s in Path(ns.args[0]).read_text().splitlines() if s.strip()]
        data = arrays(max(int(r['Nhi']) for r in rows))
        results = (check_block(int(r['Nlo']), int(r['Nhi']), data) for r in rows)
    else:
        numbers = list(map(int, ns.args))
        if ns.mode == 'pern':
            if len(numbers) != 2 or numbers[0] > numbers[1]:
                parser.error('pern requires increasing LO HI')
            numbers = range(numbers[0], numbers[1]+1)
        data = arrays(max(numbers))
        results = (check_n(n, data) for n in numbers)
    stream = ns.output.open('w') if ns.output else sys.stdout
    try:
        for result in results:
            stream.write(json.dumps(result, sort_keys=True)+'\n')
            stream.flush()
    finally:
        if ns.output:
            stream.close()

if __name__ == '__main__':
    main()
