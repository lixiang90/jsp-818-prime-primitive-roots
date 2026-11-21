"""Enumerate only the even prime predecessors that pass the dyadic error test.

The returned witnesses are unconditional. Using the test to omit other primes
requires the analytic and character-sieve inequalities described in PROOF.md.
Uses integer arithmetic, exact fractions, and the Python standard library.
"""

from argparse import ArgumentParser
from array import array
from fractions import Fraction
from math import isqrt, prod


FIRST_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
LOWER, UPPER = 2791, 2**36


def sieve(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = bytes(2)
    for d in range(2, isqrt(limit) + 1):
        if prime[d]:
            start = d * d
            prime[start::d] = bytes((limit - start) // d + 1)
    return [i for i, marked in enumerate(prime) if marked]


def coefficient(factors, refined):
    """Minimize the error by keeping an initial segment in the character sieve."""
    k = len(factors)
    best = Fraction(2**k - 1)
    if refined:
        delta = Fraction(1)
        for i in range(k - 1, -1, -1):
            delta -= Fraction(1, factors[i])
            if delta <= 0:
                break
            best = min(best, 2**i * (2 + (k - i - 1) / delta) - 1)
    return best


def dyadic_limit(bits, error):
    """Largest modulus which can fail the strict sufficient test at this bit length."""
    return ((150 + 7 * bits) * error.numerator) ** 2 // (5 * error.denominator) ** 2


def cap(error):
    bounds = []
    for bits in range(LOWER.bit_length(), UPPER.bit_length()):
        stop = min(2**bits - 1, dyadic_limit(bits, error))
        if stop >= max(LOWER + 1, 2 ** (bits - 1)):
            bounds.append(stop)
    return max(bounds, default=0)


def factorizations(limit, count, primes):
    """Generate even n <= limit with exactly count distinct prime factors once."""
    def extend(value, first, left, factors):
        if left == 0:
            yield value, factors
            return
        for i in range(first, len(primes) - left + 1):
            q = primes[i]
            smallest_tail = prod(primes[i + 1:i + left])
            next_value = value * q
            if next_value * smallest_tail > limit:
                break
            while next_value * smallest_tail <= limit:
                yield from extend(next_value, i + 1, left - 1, factors + (q,))
                next_value *= q

    power = 2
    while power * prod(FIRST_PRIMES[1:count]) <= limit:
        yield from extend(power, 1, count - 1, (2,))
        power *= 2


def prime_modulus(p, primes):
    for r in primes:
        if r * r > p:
            return True
        if p % r == 0:
            return False
    # The prime table contains every prime through the square root of the cap.
    return True


def least_witness(p, factors, primes):
    for q in primes:
        if q >= p:
            break
        if all(pow(q, (p - 1) // r, p) != 1 for r in factors):
            if pow(q, p - 1, p) != 1:
                raise ArithmeticError((p, q, "Fermat test failed"))
            return q
    raise ArithmeticError((p, "prime primitive root not found in the candidate table"))


def check(refined):
    assert prod(FIRST_PRIMES) > UPPER
    rows = []
    for k in range(1, len(FIRST_PRIMES)):
        bound = cap(coefficient(FIRST_PRIMES[:k], refined))
        if bound > prod(FIRST_PRIMES[:k]):
            rows.append((k, bound))
    # The largest last factor is bounded by dividing out the other k-1 primes.
    table_limit = max(max(isqrt(b), b // prod(FIRST_PRIMES[:k-1])) for k, b in rows)
    primes = sieve(table_limit)
    print("prime table limit", table_limit)
    print("omega | modulus cap | moduli checked | largest checked p | largest least q")
    total = 0
    for k, bound in rows:
        count = largest_p = largest_q = 0
        for n, factors in factorizations(bound - 1, k, primes):
            p = n + 1
            if p <= LOWER or not prime_modulus(p, primes):
                continue
            if p > dyadic_limit(p.bit_length(), coefficient(factors, refined)):
                continue
            q = least_witness(p, factors, primes)
            count += 1
            largest_p, largest_q = max(largest_p, p), max(largest_q, q)
        total += count
        print(k, bound, count, largest_p, largest_q, sep=" | ", flush=True)
    print("total verified", total)


def check_all_through(limit):
    """Independent exhaustive check. Each odd composite has a stored prime divisor."""
    if not 3 <= limit <= 2**32 - 1:
        raise ValueError("limit must be between 3 and 2^32-1")
    divisor = array("H", [0]) * ((limit + 1) // 2)
    for r in range(3, isqrt(limit) + 1, 2):
        if divisor[r // 2] == 0:
            start = r * r // 2
            divisor[start::r] = array("H", [r]) * ((len(divisor) - 1 - start) // r + 1)
    candidates = sieve(min(1024, limit))
    count = largest = largest_at = 0
    for p in range(3, limit + 1, 2):
        if divisor[p // 2]:
            continue
        remain = p - 1
        factors = [2]
        while remain % 2 == 0:
            remain //= 2
        while remain > 1:
            r = divisor[remain // 2] or remain
            factors.append(r)
            while remain % r == 0:
                remain //= r
        q = least_witness(p, factors, candidates)
        count += 1
        if q > largest:
            largest, largest_at = q, p
    print("odd primes verified", count, "through", limit)
    print("largest least prime primitive root", largest, "first attained at", largest_at)
    print("factor table bytes", divisor.itemsize * len(divisor))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--basic", action="store_true", help="use only the full character sieve")
    mode.add_argument("--all-through", type=int, metavar="N", help="check every odd prime <= N")
    args = parser.parse_args()
    if args.all_through is None:
        check(not args.basic)
    else:
        check_all_through(args.all_through)
