#!/usr/bin/env python3
"""
Exact N=1 obstruction test for
    I_1(t) = sum_{j>=1} (phi(t+j+1) - phi(j+1)) / 2^j

For each 1 <= t <= max_t, we search for some 1 <= J <= max_J such that
    delta_{t,J} > t + 2J + 6,
where delta_{t,J} is the distance from A_{t,J} mod 2^J to the nearest endpoint.
Such a J certifies that I_1(t) is not an integer.
"""

from __future__ import annotations
import argparse
import time
from typing import List, Optional, Tuple


def phi_sieve(n: int) -> List[int]:
    """Euler totient sieve up to n inclusive."""
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:  # p is prime
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


def first_witness_for_t(t: int, phi: List[int], max_J: int) -> Optional[Tuple[int, int, int]]:
    """
    Return the first witness (J, delta, bound) for a given t, if one exists.
    Here:
        A_{t,1} = phi[t+2] - 1
        A_{t,J+1} = 2*A_{t,J} + phi[t+J+2] - phi[J+2]
    and
        delta = min(r, 2^J - r), where r = A_{t,J} mod 2^J.
    """
    # J = 1
    A = phi[t + 2] - 1

    for J in range(1, max_J + 1):
        if J >= 2:
            # Update from A_{t,J-1} to A_{t,J}
            A = 2 * A + (phi[t + J + 1] - phi[J + 1])

        mod = 1 << J
        r = A & (mod - 1)  # same as A % mod, but faster for powers of 2
        delta = r if r <= mod - r else mod - r
        bound = t + 2 * J + 6

        if delta > bound:
            return (J, delta, bound)

    return None


def run_scan(max_t: int, max_J: int, report_every: int = 100000) -> None:
    sieve_limit = max_t + max_J + 2
    print(f"Building totient sieve up to {sieve_limit}...")
    t0 = time.time()
    phi = phi_sieve(sieve_limit)
    t1 = time.time()
    print(f"Sieve done in {t1 - t0:.3f} s")

    ruled_out = 0
    failures = []

    scan_start = time.time()
    for t in range(1, max_t + 1):
        witness = first_witness_for_t(t, phi, max_J)
        if witness is None:
            failures.append(t)
        else:
            ruled_out += 1

        if report_every and t % report_every == 0:
            elapsed = time.time() - scan_start
            rate = t / elapsed if elapsed > 0 else 0.0
            print(
                f"t={t:,}  ruled_out={ruled_out:,}  failures={len(failures):,}  "
                f"elapsed={elapsed:.2f}s  rate={rate:,.0f} t/s"
            )

    total = time.time() - scan_start
    print()
    print(f"Finished scan up to {max_t:,} in {total:.3f} s")
    print(f"Ruled out: {ruled_out:,}")
    print(f"Failures:  {len(failures):,}")

    if failures:
        print("First few failures:", failures[:20])
    else:
        print("Every t in the range was ruled out.")

    # Show a few sample witnesses
    print("\nSample witnesses:")
    for t in [1, 2, 3, 10, 100, 1000]:
        if t <= max_t:
            witness = first_witness_for_t(t, phi, max_J)
            print(f"t={t}: {witness}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-t", type=int, required=True, help="Scan 1 <= t <= max_t")
    parser.add_argument("--max-J", type=int, default=44, help="Search 1 <= J <= max_J")
    parser.add_argument("--report-every", type=int, default=100000)
    args = parser.parse_args()

    run_scan(args.max_t, args.max_J, args.report_every)


if __name__ == "__main__":
    main()