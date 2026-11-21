# JSP-000818 · Erdős 985

Assuming Dirichlet GRH, every odd prime $p$ has a prime $q<p$ of multiplicative order $p-1$ modulo $p$. The [mathematical proof](PROOF.md) and Lean developments support [awards PR #5615](https://github.com/TheJustinSunPrize/awards/pull/5615).

**The direct Lean theorem `erdos_985_of_grh_and_finite` takes two inputs.** The first is Dirichlet GRH. The second is a finite Boolean check on small prime witnesses. Lean proves the uniform smoothed character estimate from GRH, the sieve implication, its application to every large modulus, and the correctness of each finite certificate. The basic Python verifier enumerates the 111,011 residual prime moduli and finds a witness at most 193 for each in about four seconds. [Direct theorem](ExplicitTwist.lean) · [Definition of the finite input](FiniteReduction.lean) · [Witness checker](FiniteWitness.lean)

| Lean declaration in namespace `JSP818` | What Lean checks |
| --- | --- |
| [`grh_twist_envelope` and `erdos_985_of_grh_and_finite`](ExplicitTwist.lean) | Dirichlet GRH alone implies the nonprincipal twist estimate. Combining it with the finite Boolean input proves the original odd-prime target. |
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
| [`residual_wheel` and `wheelFiniteInput_iff`](FiniteCaps.lean) | Every basic residual has $p-1=dt$, where $d$ is the product of its distinct prime factors up to 43 and $t\le592{,}078$. Lean proves that testing the resulting progressions suffices. |

There is also a shorter deduction from McGown, Treviño and Trudgian's stronger bound $q<\sqrt p-2$. It needs just 405 odd primes checked in the kernel. Its Lean theorem `erdos_985` takes the published large-prime implication as an explicit argument. Both routes accept the Dirichlet GRH statement used by Alpöge as a premise. [Paper, Theorem 1](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2) · [Upstream GRH statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

## Reproduction

Import `PrimePrimitiveRoot` for the direct theorems. With Elan installed, the following commands build the project and reproduce the small certificate. The toolchain file selects Lean 4.34.1 and the Lake manifest pins mathlib and its transitive dependencies. The Hadamard support modules are included with their original notices. [Source revisions](vendor/SOURCES.md)

```sh
lake exe cache get
lake build
lake env lean ExplicitTwist.lean
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
python check_sieve_exceptions.py --basic --lean-replay
python check_wheel.py
lake env lean FiniteWitness.lean
```

The second and third commands enumerate the residual moduli for two character-sieve inequalities. The refined inequality leaves 23,667 prime moduli above 2791 (about 2 seconds locally). The basic one leaves 111,011 (about 4 seconds). The direct Lean theorem uses the basic inequality. Its input `BasicFiniteInput` asks whether a prime up to 193 passes the full order test at each residual modulus.

The optional `--lean-replay` command invokes the ordinary Lean kernel on each enumerated modulus. It supplies a factorization and a single witness, processes independent declarations in temporary batches of 2,048, and discards each batch after checking. All 111,011 individual Boolean theorems passed in 55 batches, in about 52 minutes locally. The all-moduli theorem still takes the universally quantified finite input. Connecting the executable enumeration to this universal Lean proposition is the remaining formal step. [Run record for the selected proof commit](verification/finite-kernel.txt) · [Derivation and coverage](PROOF.md#reducing-the-larger-finite-check)

`check_wheel.py` audits coverage independently by arithmetic progressions. The two algorithms produce exactly the same 111,011 integers. The wheel's multiplier tables occupy 1,776,237 bytes. [Proof of the wheel bounds](PROOF.md#independent-coverage-by-arithmetic-progressions)
