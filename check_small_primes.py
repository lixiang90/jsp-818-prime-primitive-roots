"""Check the finite range of McGown–Treviño–Trudgian for Erdős #985."""

from math import isqrt


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n) + 1))


def least_prime_root(p: int, primes: list[int]) -> int:
    factors = [r for r in primes if (p - 1) % r == 0]
    for q in primes:
        if q >= p:
            break
        if all(pow(q, (p - 1) // r, p) != 1 for r in factors):
            return q
    raise ValueError(f"No prime primitive root below {p}")


def orbit_size(q: int, p: int) -> int:
    """Count distinct powers starting at 1 by repeated multiplication."""
    seen = set()
    residue = 1
    while residue not in seen:
        seen.add(residue)
        residue = residue * q % p
    if residue != 1:
        raise ValueError(f"Power orbit did not return to 1 modulo {p}")
    return len(seen)


def main() -> None:
    primes = [n for n in range(2, 2792) if is_prime(n)]
    witnesses = {}
    for p in primes:
        if p == 2:
            continue
        q = least_prime_root(p, primes)
        if orbit_size(q, p) != p - 1:
            raise ValueError(f"Incorrect witness {q} for modulus {p}")
        witnesses[p] = q

    largest = max(witnesses.values())
    moduli = [p for p, q in witnesses.items() if q == largest]
    print(f"Verified {len(witnesses)} odd prime moduli from 3 through 2791.")
    print(f"Largest least prime primitive root: {largest}, for p = {moduli}.")


if __name__ == "__main__":
    main()
