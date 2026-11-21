"""Independent coverage audit of the basic residual set using arithmetic progressions."""

from array import array
from itertools import combinations
from math import isqrt, prod

from check_sieve_exceptions import check


WHEEL = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
OUTSIDE = (47, 53, 59, 61, 67, 71, 73, 79, 83)
CAPS = (0, 0, 23409, 149304, 756900, 3552471, 16054446, 74142432, 324108009, 1406805054)


def progressions():
    for k in range(2, len(CAPS)):
        for j in range(1, k + 1):
            floor = prod(OUTSIDE[:k-j])
            for indices in combinations(range(1, len(WHEEL)), j - 1):
                d = 2 * prod(WHEEL[i] for i in indices)
                hi = (CAPS[k] - 1) // d
                if floor <= hi:
                    yield k, 1 + sum(1 << i for i in indices), d, k-j, floor, hi


def wheel_primes():
    bands = list(progressions())
    limit = max(hi for _, _, _, _, _, hi in bands)
    masks = array("H", [0]) * (limit + 1)
    outside = bytearray(limit + 1)
    divisors = []
    for q in range(2, limit + 1):
        if masks[q] or outside[q]:
            continue
        if q <= isqrt(CAPS[-1]):
            divisors.append(q)
        if q in WHEEL:
            bit = 1 << WHEEL.index(q)
            for t in range(q, limit + 1, q):
                masks[t] |= bit
        else:
            for t in range(q, limit + 1, q):
                outside[t] += 1

    def prime(p):
        for q in divisors:
            if q*q > p:
                break
            if p % q == 0:
                return False
        return True

    print("largest multiplier", limit, "multiplier-table bytes", (masks.itemsize + 1)*(limit+1))
    for k, mask, d, needed, low, hi in bands:
        for t in range(low, hi + 1):
            if outside[t] != needed or masks[t] & ~mask:
                continue
            p = d*t + 1
            if p > 2791 and 25*p <= ((150 + 7*p.bit_length())*(2**k - 1))**2 and prime(p):
                yield p


if __name__ == "__main__":
    remaining = set()
    check(False, lambda p, _q, _factors: remaining.add(p))
    original = len(remaining)
    for p in wheel_primes():
        remaining.remove(p)
    if remaining:
        raise ArithmeticError(("missing wheel moduli", len(remaining)))
    print("identical residual prime sets", original)
