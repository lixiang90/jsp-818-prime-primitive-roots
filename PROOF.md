# A prime primitive root below every odd prime

Assume the generalized Riemann hypothesis for Dirichlet $L$-functions. For every odd prime $p$, there is a prime $q<p$ whose multiplicative order modulo $p$ is $p-1$. This is the odd-prime formulation of Erdős problem 985. At $p=2$ there is no smaller prime. [Erdős, printed p. 233](https://www.renyi.hu/~p_erdos/1965-17.pdf) · [Corresponding Lean problem statement](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/ErdosProblems/985.lean#L27-L33)

## Large primes

Write $\widehat g(p)$ for the least **prime** primitive root modulo $p$. For every prime $p>2791$, Theorem 1 of McGown, Treviño and Trudgian gives $\widehat g(p)<\sqrt p-2$ on GRH. Its analytic input concerns the Riemann zeta function and Dirichlet characters modulo $p$. Since $p\ge1$ gives $\sqrt p\le p$, we may take $q=\widehat g(p)$. The strict threshold leaves $p=2791$ in the finite check. [McGown, Treviño and Trudgian, Theorem 1 and §2](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2)

## The finite range

For each odd prime $p\le2791$, test primes $q<p$ for the two conditions

$$q^{p-1}\equiv1\pmod p,\qquad q^{(p-1)/r}\not\equiv1\pmod p\quad\text{for every prime }r\mid p-1.$$

The first condition makes the order a divisor of $p-1$. If its value $d$ were a proper divisor, a prime factor $r$ of $(p-1)/d$ would give $d\mid(p-1)/r$, contrary to the second condition. The Lean certificate supplies a witness at each modulus. To check the exponents it suffices to consider small divisors and their complements, since $54^2>2791$. The separate Python calculation enumerates all primes in increasing order and verifies each selected witness again by counting its full orbit.

There are 405 odd prime moduli in the range. The largest of their least prime primitive roots is 53, attained only for $p=2791$. Combining the two ranges proves the stated implication. Prior computations already included this finite range. [Oliveira e Silva's primitive-root computations](https://sweet.ua.pt/tos/p_roots.html)

## Attribution and input

The analytic bound is the 2016 result of McGown, Treviño and Trudgian. Levent Alpöge announced the upstream GRH development with Claude. This repository accepts the indicated Dirichlet theorem as a premise. The submitting account lixiang90 used OpenAI Codex for the downstream write-up, witness checks and Lean code. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Upstream theorem](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Main.lean#L8)
