# JSP-000818 · Erdős 985

Every odd prime has a smaller **prime** primitive root, assuming Dirichlet GRH. This repository contains the [mathematical proof](PROOF.md), [Lean source](PrimePrimitiveRoot.lean) and an [independent numerical reproduction](check_small_primes.py) for [awards PR #5615](https://github.com/TheJustinSunPrize/awards/pull/5615).

| Lean declaration in namespace `JSP818` | What Lean checks |
| --- | --- |
| `finite_range` | Every odd prime through 2791 inclusive has the required witness. Kernel reduction checks the finite certificate. |
| `two_exception` | No prime smaller than 2 exists. |
| [`prime_power_predecessor` and `safe_prime_modulus`](ElementaryFamilies.lean) | For every prime with $p-1=r^{k+1}$ or $p-1=2r$ for prime $r$, Lean proves the full prime-witness conclusion without GRH or a size cutoff. |
| `odd_primes_of_mcgown_trevino_trudgian` | The published square-root bound and the finite certificate give the conclusion for every odd prime. |
| `erdos_985` | The original odd-prime target follows with two explicit inputs, Dirichlet GRH and the implication from GRH to the published bound. |
| [`prime_root_of_large_twist_bound`](SizeBound.lean) | For every prime at least $2^{36}$ the original conclusion follows from a bound on its nonprincipal smoothed character sums. Lean proves the principal sum lower bound and the size comparison. |
| [`grh_smoothed_zero_bound`](ZeroMassBound.lean) | Dirichlet GRH bounds the sum of the absolute zero kernels by $\frac43(\tfrac12\log p+6)$ for all nonprincipal characters of prime modulus, with analytic multiplicities. |
| [`logDeriv_grid_poles`](GridFormula.lean) | At $s=3/2+2m$, the change of logarithmic derivative of the Dirichlet $L$-function equals the sum of the changes from all its trivial and nontrivial zeros. |
| [`rootCertificate_sound`](FiniteWitness.lean) | A prime witness and a factorization of $p-1$ can be checked by binary modular exponentiation for $p\le 2^{36}$. The same kernel proof verifies the example $p=13{,}123{,}111$, $q=19$. |
| [`odd_primes_of_twist_envelope`](FiniteReduction.lean) | The explicit smoothed-sum bound and a finite input with an integer-only test imply Erdős 985. The basic sieve program checks the 111,011 prime moduli selected by this test. |

The remaining formal step is the proof of `DirichletGRH → McGownTrevinoTrudgianBound`. The top-level theorem takes it as an argument. The mathematical proof cites Theorem 1 of the 2016 paper. Alpöge's development is an external premise and the local build does not import or independently check it. The award PR submits mathematical evidence. [Paper](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2) · [Upstream GRH statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

## Reproduction

From this repository with Elan installed, run the following commands. The toolchain file selects Lean 4.34.1 and the Lake manifest pins mathlib and its transitive dependencies. The Hadamard support modules are included with their original notices. [Source revisions](vendor/SOURCES.md)

```sh
lake exe cache get
lake build
lake env lean PrimePrimitiveRoot.lean
lake env lean ElementaryFamilies.lean
lake env lean ZeroMassBound.lean
lake env lean SizeBound.lean
python check_small_primes.py
```

The source prints the transitive axiom dependencies of each listed theorem. The checked declarations use `propext`, `Classical.choice` and `Quot.sound`. Explicit hypotheses remain visible in the types even when only these standard axioms are printed.

## Reproducing the larger finite checks

The exhaustive run checks every odd prime up to $2^{24}$ with the Python standard library. It found 1,077,870 witnesses in about 9 seconds locally, using a 16 MiB factor table. The largest least prime primitive root in this range is 211, first attained at 4,022,911.

```sh
python check_sieve_exceptions.py --all-through 16777216
python check_sieve_exceptions.py
python check_sieve_exceptions.py --basic
lake env lean FiniteWitness.lean
```

The second and third commands enumerate only the residual moduli for two character-sieve inequalities. The refined inequality leaves 23,667 prime moduli above 2791 (about 2 seconds locally). The basic one leaves 111,011 (about 4 seconds). All reported witnesses satisfy the full order test. Using either sieve to discharge the complementary moduli in the direct Lean proof still requires the smoothed-sum estimate. [Derivation and coverage](PROOF.md#reducing-the-larger-finite-check)
