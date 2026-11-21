# JSP-000818 · Erdős 985

Assuming Dirichlet GRH, every odd prime $p$ has a prime $q<p$ of multiplicative order $p-1$ modulo $p$. The [mathematical proof](PROOF.md) and Lean developments support [awards PR #5615](https://github.com/TheJustinSunPrize/awards/pull/5615).

**The main theorem `JSP818.erdos_985_of_grh` takes Dirichlet GRH as its only mathematical premise.** Its conclusion gives a prime primitive root strictly below every odd prime modulus. Lean proves the character estimate, the sieve implication, and the universally quantified finite calculation `JSP818.basicFiniteInput_verified`. The default build generates and checks the finite certificates. [Main theorem](PrimePrimitiveRoot.lean) · [Finite theorem](FiniteCases.lean) · [Proof of exhaustive coverage](FiniteEnumeration.lean)

| Lean declaration in namespace `JSP818` | What Lean checks |
| --- | --- |
| [`erdos_985_of_grh`](PrimePrimitiveRoot.lean) | The original odd-prime conclusion follows from Dirichlet GRH. |
| [`basicFiniteInput_verified`](FiniteCases.lean) | Every residual prime modulus passes the bounded order test, with complete coverage proved in Lean. |
| [`grh_twist_envelope` and `erdos_985_of_grh_and_finite`](ExplicitTwist.lean) | Dirichlet GRH alone implies the nonprincipal twist estimate. Combining it with the finite Boolean input proves the original odd-prime target. |
| `finite_range` | Every odd prime through 2791 inclusive has the required witness. Kernel reduction checks the finite certificate. |
| `two_exception` | No prime smaller than 2 exists. |
| [`prime_power_predecessor` and `safe_prime_modulus`](ElementaryFamilies.lean) | For every prime with $p-1=r^{k+1}$ or $p-1=2r$ for prime $r$, Lean proves the full prime-witness conclusion without GRH or a size cutoff. |
| `odd_primes_of_mcgown_trevino_trudgian` | The published square-root bound and the finite certificate give the conclusion for every odd prime. |
| [`erdos_985` (published-bound route)](PublishedBound.lean) | The historical wrapper accepts Dirichlet GRH and the published large-prime implication. |
| [`prime_root_of_large_twist_bound`](SizeBound.lean) | For every prime at least $2^{36}$ the original conclusion follows from a bound on its nonprincipal smoothed character sums. Lean proves the principal sum lower bound and the size comparison. |
| [`grh_smoothed_zero_bound`](ZeroMassBound.lean) | Dirichlet GRH bounds the sum of the absolute zero kernels by $\frac43(\tfrac12\log p+6)$ for all nonprincipal characters of prime modulus, with analytic multiplicities. |
| [`logDeriv_grid_poles`](GridFormula.lean) | At $s=3/2+2m$, the change of logarithmic derivative of the Dirichlet $L$-function equals the sum of the changes from all its trivial and nontrivial zeros. |
| [`rootCertificate_sound`](FiniteWitness.lean) | A prime witness and a factorization of $p-1$ can be checked by binary modular exponentiation for $p\le 2^{36}$. The same kernel proof verifies the example $p=13{,}123{,}111$, $q=19$. |
| [`odd_primes_of_twist_envelope`](FiniteReduction.lean) | The explicit smoothed-sum bound and a finite input with an integer-only test imply Erdős 985. The basic sieve program checks the 111,011 prime moduli selected by this test. |
| [`residual_wheel` and `wheelFiniteInput_iff`](FiniteCaps.lean) | Every basic residual has $p-1=dt$, where $d$ is the product of its distinct prime factors up to 43 and $t\le592{,}078$. Lean proves that testing the resulting progressions suffices. |

There is also a shorter deduction from McGown, Treviño and Trudgian's stronger bound $q<\sqrt p-2$. It needs just 405 odd primes checked in the kernel. Its Lean theorem `erdos_985` takes the published large-prime implication as an explicit argument. Both routes accept the Dirichlet GRH statement used by Alpöge as a premise. [Paper, Theorem 1](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2) · [Upstream GRH statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

## Reproduction

Import `PrimePrimitiveRoot` for the GRH-only result. With Elan installed, the following commands build the project and inspect the proof. The toolchain file selects Lean 4.34.1 and the Lake manifest pins mathlib and its transitive dependencies. The Hadamard support modules are included with their original notices. [Source revisions](vendor/SOURCES.md)

```sh
lake exe cache get
lake build
lake env lean FiniteCases.lean
lake env lean PrimePrimitiveRoot.lean
```

The modules `FiniteCases.K2` through `FiniteCases.K9` can be built individually, for example with `lake build FiniteCases.K5`. The largest case, `K5`, has five independently cached intervals. A low-memory build can run each of those five targets individually and then build the eight factor-count modules one at a time. [Five-factor intervals](FiniteCases/Five)

All targets share the same certificate generator and coverage proof. The verification record gives the types of the finite and final theorems, the counts for all eight cases, and the transitive axiom audit. Both theorems use `propext`, `Classical.choice` and `Quot.sound`. The final theorem's type records its explicit Dirichlet GRH hypothesis. [Verification record](verification/grh-exhaustion.txt)

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

The second and third commands enumerate the residual moduli for two character-sieve inequalities. The refined inequality leaves 23,667 prime moduli above 2791 (about 2 seconds locally). The basic one leaves 111,011 (about 4 seconds). The direct Lean theorem uses the basic inequality. The proved proposition `BasicFiniteInput` says that a prime up to 193 passes the full order test at each residual modulus.

The optional `--lean-replay` command invokes the ordinary Lean kernel on each enumerated modulus. It supplies a factorization and a single witness, processes independent declarations in temporary batches of 2,048, and discards each batch after checking. All 111,011 individual Boolean theorems passed in 55 batches, in about 52 minutes locally. The default Lean build separately proves the universal proposition by exhausting the possible ordered prime factors and final cofactor. This computation runs inside the normal build and uses Lean kernel reduction on small pages of checked hints. [Earlier pointwise run](verification/finite-kernel.txt) · [Universal proof](PROOF.md#kernel-checked-exhaustion)

`check_wheel.py` audits coverage independently by arithmetic progressions. The two algorithms produce exactly the same 111,011 integers. The wheel's multiplier tables occupy 1,776,237 bytes. [Proof of the wheel bounds](PROOF.md#independent-coverage-by-arithmetic-progressions)
