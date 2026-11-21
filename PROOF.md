# A prime primitive root below every odd prime

Assume the generalized Riemann hypothesis for Dirichlet $L$-functions. For every odd prime $p$, there is a prime $q<p$ whose multiplicative order modulo $p$ is $p-1$. This is the odd-prime formulation of Erdős problem 985. At $p=2$ there is no smaller prime. [Erdős, printed p. 233](https://www.renyi.hu/~p_erdos/1965-17.pdf) · [Corresponding Lean problem statement](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/ErdosProblems/985.lean#L27-L33)

## Large primes

Write $\widehat g(p)$ for the least **prime** primitive root modulo $p$. For every prime $p>2791$, Theorem 1 of McGown, Treviño and Trudgian gives $\widehat g(p)<\sqrt p-2$ on GRH. Its analytic input concerns the Riemann zeta function and Dirichlet characters modulo $p$. Since $p\ge1$ gives $\sqrt p\le p$, we may take $q=\widehat g(p)$. The strict threshold leaves $p=2791$ in the finite check. [McGown, Treviño and Trudgian, Theorem 1 and §2](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2)

## The finite range

For each odd prime $p\le2791$, test primes $q<p$ for the two conditions

$$q^{p-1}\equiv1\pmod p,\qquad q^{(p-1)/r}\not\equiv1\pmod p\quad\text{for every prime }r\mid p-1.$$

The first condition makes the order a divisor of $p-1$. If its value $d$ were a proper divisor, a prime factor $r$ of $(p-1)/d$ would give $d\mid(p-1)/r$, contrary to the second condition. The Lean certificate supplies a witness at each modulus. To check the exponents it suffices to consider small divisors and their complements, since $54^2>2791$. The separate Python calculation enumerates all primes in increasing order and verifies each selected witness again by counting its full orbit.

There are 405 odd prime moduli in the range. The largest of their least prime primitive roots is 53, attained only for $p=2791$. Combining the two ranges proves the stated implication. Prior computations already included this finite range. [Oliveira e Silva's primitive-root computations](https://sweet.ua.pt/tos/p_roots.html)

## Two unconditional families with no size cutoff

Fix a prime $p$ and $0<e<p-1$. The group $(\mathbb Z/p\mathbb Z)^\times$ is cyclic of order $p-1$, so it contains an element $a$ with $a^e\ne1$. Take its representative $m$ in $[1,p-1]$. If every prime factor of $m$ had $e$th power one, multiplying those powers would give $a^e=1$. Thus some prime $q\mid m$ satisfies $q<p$ and $q^e\ne1$.

* If $p-1=r^{k+1}$ with $r$ prime, take $e=r^k$. Every proper divisor of $p-1$ divides $e$, so the selected prime has order $p-1$.
* If $p-1=2r$ with $r$ prime, take $e=r$. A proper order dividing $2r$ divides $r$ or $2$. The former is excluded by construction. In the latter case $q^2=1\bmod p$, which forces $q=1$ or $q=p-1$ as an integer in $[1,p-1]$. The first value is below 2 and the second is the composite $2r$.

Both arguments give the original prime witness for all moduli in their families independently of GRH. [Lean proofs](ElementaryFamilies.lean)

For safe primes, Ramesh and Makeshwari proved the stronger statement that the least positive primitive root is prime. Joshua Bald published a Lean formalization of this result in October 2026. The short factorization argument above independently checks the existence conclusion used here. [Bald’s paper and source repository](https://zenodo.org/records/23653561)

## A direct route using the weaker cutoff

For a nonprincipal Dirichlet character $\chi$ modulo a prime $p$ put

$$T_\chi(p)=\sum_{1\le n<p}\Lambda(n)\chi(n)(1-n/p).$$

If $\lVert T_\chi(p)\rVert\le B$ for every such character and the principal mass exceeds $(2^{\omega(p-1)}-1)B$, the character sieve finds a term of full multiplicative order. Its nonzero von Mangoldt weight makes it a prime power. Its underlying prime has full order as well and lies below $p$. Lean proves the principal mass is at least $p/3$ for $p\ge1024$. The inequality $16^{\omega(n)}\le560n$ follows by accounting for the six primes below 16. It gives $3(2^{\omega(p-1)}-1)\log p<\sqrt p$ for $p\ge2^{36}$. In that range a proof of $\lVert T_\chi(p)\rVert\le\sqrt p\log p$ suffices. [Character sieve](CharacterSieve.lean) · [Prime extraction](SmoothedSums.lean) · [Principal mass](PrincipalMass.lean) · [Cutoff](SizeBound.lean)

Write $b=3/2$, and let $D_\chi$ be the logarithmic derivative of the conductor-normalized completed $L$-function. Subtracting the Hadamard expansions at $b$ and $1-b$ removes their constant. The functional equation relates the second value to $-D_{\chi^{-1}}(b)$. Under Dirichlet GRH every completed zero has real part $1/2$, so taking real parts yields the following identity with analytic multiplicities.

$$\sum_\rho\frac1{|b-\rho|^2}=\frac12\Re\bigl(D_\chi(b)+D_{\chi^{-1}}(b)\bigr)\le\tfrac12\log p+6.$$

For the upper bound, the tangent inequality for $\log\Gamma$ on $[u,u+1]$ gives $\Re\psi(u)\le\log u$, using $\Gamma(u+1)=u\Gamma(u)$. This bounds the archimedean term for both parities. The absolutely convergent Euler series satisfies $|L'/L(3/2,\chi)|\le6$. Indeed $\Lambda(n)\le\log n\le\tfrac32 n^{1/4}$ and $\sum_{n\ge2} n^{-5/4}\le4$. Since $|\rho(\rho+1)|^{-1}\le\tfrac43|b-\rho|^{-2}$, the total zero kernel is at most $\tfrac43(\tfrac12\log p+6)$. [Hadamard subtraction](BachZeros.lean) · [Archimedean factor](GammaFactors.lean) · [Euler factor](EulerBound.lean) · [Combined bound](ZeroMassBound.lean)

The grid identity expresses $L'/L(s,\chi)-L'/L(b,\chi)$ as the sum of $(s-\rho)^{-1}-(b-\rho)^{-1}$ over the nontrivial and trivial zeros at $s=b+2m$. The gamma recurrence telescopes the trivial-zero contribution. For $\rho\ne0,-1$ the corresponding inverse kernel after division by $s(s+1)$ is

$$G_\rho(y)=\frac{y^{-\rho}}{\rho(\rho+1)}
 -\frac{b}{\rho(b-\rho)}
 +\frac{y(b+1)}{(\rho+1)(b-\rho)}.$$

Write $a=0$ for even characters and $a=1$ for odd characters. The first trivial zero has kernel $G_0(y)=-\log y-\tfrac53(1-y)$ or $G_{-1}(y)=\tfrac35(1-y)+y\log y$. At $y=1/p$ either has absolute value at most $\log p+2$. For the remaining trivial zeros $-k$, $k=a+2j+2$, one has $|G_{-k}(y)|\le5/[k(k-1)]$ on $0\le y\le1$. Their total is at most 5 by telescoping. The nontrivial kernels have total norm at most $(\tfrac43y^{-1/2}+3+\tfrac52y)(\tfrac12\log p+6)$ under GRH. [Grid identity](GridFormula.lean) · [Nontrivial kernels](ZeroSide.lean) · [First trivial kernel](FirstPole.lean) · [Trivial tail](TrivialTail.lean)

To identify the sum with the arithmetic quantity, multiply both sides by $y^{5/2}$. The resulting functions are continuous on $[0,1]$. Their moments against $y^{2m}$ agree for every $m\ge0$ by the logarithmic-derivative grid identity and termwise integration against summable uniform majorants. Polynomials in $y^2$ are dense in the continuous functions on $[0,1]$, by applying polynomial approximation to the function composed with $\sqrt{\cdot}$. Thus the normalized functions agree pointwise. At $y=1/p$ the arithmetic side is exactly $p^{-5/2}T_\chi(p)$. Lean obtains this estimate using Dirichlet GRH alone.

$$|T_\chi(p)|\le\big(\tfrac23\log p+8\big)\sqrt p+3\log p+37 \qquad(p>2791).$$

The constant 37 follows from the first trivial kernel's additive 2, the tail bound 5, the Euler bound 6, and $4\cdot6$ from the nontrivial zeros. The remaining linear term is bounded by $|L'/L(b)|(1-1/p)\le6$. [Arithmetic moments](ArithmeticMoments.lean) · [Pole moments](PoleMoments.lean) · [Uniqueness](MomentUniqueness.lean) · [Explicit formula and final estimate](ExplicitTwist.lean)

## Reducing the larger finite check

The deduction from the published square-root bound needs only the 405 odd primes through 2791. The independent direct proof uses the weaker target $q<p$ and the following finite calculation.

For $2791<p<2^{36}$ let $b$ be the bit length of $p$ and $k=\omega(p-1)$. Before rounding the lower-order terms, the explicit formula bounds the smoothed twist by

$$
 B(p)=\left(\tfrac43\sqrt p+3+\tfrac5{2p}\right)
       \left(\tfrac12\log p+6\right)+\log p+13.
$$

For $p>2791$ this expression is at most $((2/3)\log p+8)\sqrt p+3\log p+37$. Also $3\log p+37\le2\sqrt p$, since the difference is increasing for $p>9$ and positive at 2048 (use $\log 2<0.7$). Hence $B(p)\le(7b/15+10)\sqrt p$. For a sieve error coefficient $C$, the lower bound $p/3$ for the principal mass now wins whenever

$$25p>(150+7b)^2 C^2.$$

* **Full character sieve.** Put $C=2^k-1$. Applying the integer comparison leaves 111,011 prime moduli above 2791, the largest being 1,402,927,891. The program finds a prime primitive root for each in about 4 seconds on the development machine. The largest least witness is 193. At each residual prime the bounded search over $q<194$ succeeds, using every prime divisor of $p-1$. The universal finite theorem below and the formalized analytic estimates together give the original conclusion from Dirichlet GRH alone. [Character sieve](CharacterSieve.lean) · [Exact finite predicate](FiniteReduction.lean) · [Direct theorem](ExplicitTwist.lean)
* **Fewer cases with a core of prime factors.** Choose a subset $S$ of the prime factors of $p-1$ and let $R$ be the remaining factors. Put $\delta=1-\sum_{r\in R}1/r$. If $R$ is nonempty and $\delta>0$, one can take $C=2^{|S|}(2+(|R|-1)/\delta)-1$. To see this, normalize the indicator of avoiding the $s$th powers for $s\in S$ by dividing by $\prod_{s\in S}(1-1/s)$. Its sum against the nonnegative weights is $W_S$. Character orthogonality gives $W_S\ge M-(2^{|S|}-1)B$ for principal mass $M$. For $r\in R$, the total weight lost among these survivors is at most $W_S/r+(1-1/r)2^{|S|}B$. Indeed the normalized $r$-indicator has constant coefficient one, and its nonconstant coefficients have total absolute value one. Multiplication by the normalized $S$-indicator gives exclusively nonprincipal twists in this difference, since their character orders have a factor $r$. The union bound gives surviving weight at least $\delta W_S-2^{|S|}(|R|-1+\delta)B$, as asserted. For a fixed core size, choosing the smallest factors for $S$ maximizes $\delta$. Taking the better of all these choices and the full sieve leaves the following cases. This refinement is a paper argument. [Related prime-divisor sieve in McGown, Treviño and Trudgian, §3](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf)

| Distinct factors of $p-1$ | Prime moduli checked | Largest such $p$ | Largest least prime root |
| ---: | ---: | ---: | ---: |
| 2 | 385 | 23,399 | 23 |
| 3 | 3,701 | 138,241 | 61 |
| 4 | 8,958 | 555,661 | 107 |
| 5 | 8,000 | 1,456,561 | 149 |
| 6 | 2,436 | 3,513,511 | 139 |
| 7 | 186 | 6,846,841 | 137 |
| 8 | 1 | 13,123,111 | 19 |
| **Total** | **23,667** | **13,123,111** | **149** |

The enumerator first bounds $C$ using the first $k$ primes, because increasing the ordered prime factors can only improve $\delta$. It computes the largest possible residual modulus in each bit range by exact rational arithmetic. It enumerates even predecessors below that cap by adjoining positive prime powers with strictly increasing primes. Unique factorization supplies completeness, and the product of the smallest possible subsequent primes allows early termination. Trial division establishes primality of $p$. For each surviving prime, modular exponentiation checks every prime divisor of $p-1$. The eleven smallest primes have product greater than $2^{36}$, so there are no additional factor counts to visit. The refined run took about 2 seconds locally. [Reproduction script](check_sieve_exceptions.py)

For an alternative finite input with simpler coverage, use every odd prime below $2^{24}$. For $2^{24}\le p<2^{26}$ there are at most eight prime factors, as the ninth primorial exceeds $2^{26}$. The two smallest factors as core give $C\le60$ by using the first eight primes to bound $\delta$. This also holds for $k\le2$ by the full sieve. Throughout this band $\sqrt p\ge4096>60(30+7\cdot26/5)$. For $2^{26}\le p<2^{36}$ the first ten primes give $C\le101$ by the same argument, and $\sqrt p\ge8192>101(30+7\cdot36/5)$. Thus the displayed twist bound and the refined sieve suffice for both bands.

Independently of this analytic reasoning, a separate exhaustive pass checked all 1,077,870 odd primes through $2^{24}$ in about 9 seconds. For each odd composite its factor table stores one prime divisor, permitting exact factorization of every $p-1$. The table uses 16 MiB. The largest least prime primitive root is 211, attained first at $p=4,022,911$. A generated witness can be checked in the Lean kernel using binary modular exponentiation and the prime divisors of $p-1$ with multiplicities. For example, the unique eight-factor case in the table has witness 19 and predecessor $2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot19\cdot23$. [Lean certificate checker](FiniteWitness.lean)

## Independent coverage by arithmetic progressions

For the basic sieve, Lean proves $2\le k\le9$ and a per-$k$ cap on $p$. The greatest cap is 1,406,805,054. Every prime divisor of a residual $p-1$ is at most 25,230, and testing primality of $p$ by trial division requires primes only through 37,507. These bounds follow by comparing products of distinct primes with initial segments of the primes and checking 36 possible bit lengths. [Formal bounds](FiniteCaps.lean)

Let $A$ be the set of primes up to 43 dividing $p-1$, let $d=\prod_{r\in A}r$, and put $t=(p-1)/d$. Each prime in $A$ is removed exactly once. If $j=|A|$, the remaining $k-j$ distinct primes outside the wheel are at least $47,53,59,\ldots$ in order. Their product gives a lower bound on $t$, and the first $j$ primes give a lower bound on $d$. Combining these with the per-$k$ cap gives **$t\le592{,}078$ for every residual modulus**. Lean proves this and proves that the finite input indexed by $(k,A,t)$ is equivalent to the original finite input. [Wheel reduction](FiniteCaps.lean)

The second Python enumerator sieves the multipliers once. For each $t$ it records which of the fourteen small primes divide it and how many distinct primes above 43 divide it. It visits $p=dt+1$ only when the small-prime mask of $t$ is contained in $A$ and the large-prime count equals $k-j$. This specifies a unique $A$ for each generated $p$. The multiplier tables use 1,776,237 bytes. Comparing the actual sets of integers gave exact agreement with the prime-power recursion on all 111,011 residual prime moduli. [Independent coverage audit](check_wheel.py)

## Kernel-checked exhaustion

Let $k=\omega(p-1)$ and let $c_k$ be the proved cap for a residual prime. The formal bounds give $2\le k\le9$. Start with the factor 2. After choosing the smallest distinct factors once each, write $d$ for their product and $S$ for the set of remaining distinct factors. The radical of $p-1$ divides $p-1$, so $p-1=d(\prod_{s\in S}s)t$ for a positive integer $t$. For $r=\min S$ and $\ell=|S|$, this gives $dr^\ell\le p-1<c_k$. Once $d b^\ell\ge c_k$, every possible choice of $r$ is below $b$. Lean splits the resulting integer interval, rejects composite choices by a proper divisor, and continues with $S\setminus\{r\}$ and lower endpoint $r+1$. [Branch and interval proofs](FiniteEnumeration.lean)

After choosing $k-1$ factors the last unknown prime $r$ is absorbed into $m=rt$, so $p=dm+1$. The integer $m$ has a prime factor at least the current lower endpoint and satisfies $m\le\lfloor(c_k-1)/d\rfloor$. Taking the product of the first $k-1$ primes for the smallest possible $d$ gives the following upper bounds.

| $k$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Largest cofactor bound | 11,704 | 24,883 | 25,229 | 16,916 | 6,949 | 2,468 | 634 | 145 |

The largest entry occurs at $k=4$, where $c_4=756{,}900$ and $d\ge2\cdot3\cdot5=30$. Across the eight cases there are 1,311,857 terminal interval positions, counted separately by factor prefix. Exactly 111,011 require a prime primitive root certificate.

For the largest computation, $k=5$, the inequalities $2\cdot37^4\ge c_5$ and $6\cdot84^3\ge c_5$ give stopping points after selecting 2 and after selecting 2 and 3. Five independently cached intervals are joined by the same coverage lemma. [Five-factor assembly](FiniteCases/K5.lean)

Lean checks every integer in each resulting interval. A row can be discharged by the size inequality, a proper divisor of $p$, a prime factor count different from $k$, or a complete factorization of $m$ showing all its prime factors are too small. Every surviving row must supply a prime $q\le193$ passing the modular order tests. Whenever a factorization is used, the checker verifies both its product and the primality of its entries. The elaborator packs one sixteen-bit hint per row. The kernel evaluates each small page and checks that adjacent pages cover the whole interval. The eight factor-count cases give an unconditional proof of the exact proposition `BasicFiniteInput`. [Certificate generator](CertifyEnumeration.lean) · [Finite theorem](FiniteCases.lean) · [Final theorem](PrimePrimitiveRoot.lean)

## Attribution and input

McGown, Treviño and Trudgian proved the stronger square-root bound used in the short published deduction. The direct Lean proof above derives its smoothed character estimate from Dirichlet GRH. Levent Alpöge announced the upstream GRH development with Claude. This repository accepts the indicated Dirichlet theorem as a premise. The submitting account lixiang90 used OpenAI Codex for the downstream write-up, witness checks and Lean code. [Published bound](https://campus.lakeforest.edu/trevino/GrosswaldGRH.pdf#page=2) · [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Upstream theorem](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Main.lean#L8)
