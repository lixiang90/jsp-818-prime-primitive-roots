# JSP-000818 · Erdős 985

Every odd prime has a smaller **prime** primitive root, assuming Dirichlet GRH. This repository contains the [mathematical proof](PROOF.md), [Lean source](PrimePrimitiveRoot.lean) and an [independent numerical reproduction](check_small_primes.py) for [awards PR #5615](https://github.com/TheJustinSunPrize/awards/pull/5615).

| Lean declaration in namespace `JSP818` | What Lean checks |
| --- | --- |
| `finite_range` | Every odd prime through 2791 inclusive has the required witness. Kernel reduction checks the finite certificate. |
| `two_exception` | No prime smaller than 2 exists. |
| [`prime_power_predecessor` and `safe_prime_modulus`](ElementaryFamilies.lean) | For every prime with $p-1=r^{k+1}$ or $p-1=2r$ for prime $r$, Lean proves the full prime-witness conclusion without GRH or a size cutoff. |
| `odd_primes_of_mcgown_trevino_trudgian` | The published square-root bound and the finite certificate give the conclusion for every odd prime. |
| `erdos_985` | The original odd-prime target follows with two explicit inputs, Dirichlet GRH and the implication from GRH to the published bound. |

The remaining formal step is the proof of `DirichletGRH → McGownTrevinoTrudgianBound`. The top-level theorem takes it as an argument. The mathematical proof cites Theorem 1 of the 2016 paper. Alpöge's development is an external premise and the local build does not import or independently check it. The award PR submits mathematical evidence. [Paper](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2) · [Upstream GRH statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

## Reproduction

From this repository with Elan installed, run the following commands. The toolchain file selects Lean 4.22.0-rc4 and the Lake manifest pins mathlib and its transitive dependencies. The cache command downloads precompiled upstream mathlib packages.

```sh
lake exe cache get
lake build
lake env lean PrimePrimitiveRoot.lean
lake env lean ElementaryFamilies.lean
python check_small_primes.py
```

The source prints the transitive axiom dependencies of each listed theorem. The checked declarations use `propext`, `Classical.choice` and `Quot.sound`. Explicit hypotheses remain visible in the types even when only these standard axioms are printed.
