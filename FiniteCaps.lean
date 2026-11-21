import FiniteReduction

namespace JSP818

open Finset

/-- Coarse caps used before enumerating the exact factorizations. -/
def basicCap (k : ℕ) : ℕ :=
  [0, 0, 23409, 149304, 756900, 3552471, 16054446, 74142432, 324108009,
    1406805054, 6076607846].getD k 0

private def threshold (k : ℕ) : ℕ :=
  max 1 (([2,3,5,7,11,13,17,19,23,29,31,37] : List ℕ).getD k 1)

private def prefixPrimes (k : ℕ) : Finset ℕ := (range (threshold k)).filter Nat.Prime

private theorem initial_prod_le (P S : Finset ℕ) {T : ℕ} (hT : 1 ≤ T)
    (small : ∀ r ∈ P, r ≤ T) (outside : ∀ r ∈ S, r ∉ P → T ≤ r) (size : P.card ≤ S.card) :
    (∏ r ∈ P, r) ≤ ∏ r ∈ S, r := by
  have card : (P \ S).card ≤ (S \ P).card := by
    have h₁ := card_sdiff_add_card_inter P S
    have h₂ := card_sdiff_add_card_inter S P
    rw [inter_comm S P] at h₂
    omega
  have lower : (∏ r ∈ P \ S, r) ≤ T^(P \ S).card := by
    rw [← prod_const]
    apply prod_le_prod'
    intro r hr
    exact small r (mem_sdiff.mp hr).1
  have upper : T^(S \ P).card ≤ ∏ r ∈ S \ P, r := by
    rw [← prod_const]
    apply prod_le_prod'
    intro r hr
    exact outside r (mem_sdiff.mp hr).1 (mem_sdiff.mp hr).2
  have side := lower.trans ((Nat.pow_le_pow_right hT card).trans upper)
  change (∏ r ∈ P, r) ≤ ∏ r ∈ S, r
  rw [← prod_inter_mul_prod_sdiff P S (fun r : ℕ => r), ← prod_inter_mul_prod_sdiff S P (fun r : ℕ => r),
    inter_comm S P]
  exact Nat.mul_le_mul_left _ side

private theorem prefix_prod_le (k : ℕ) (S : Finset ℕ) (prime : ∀ r ∈ S, Nat.Prime r)
    (size : (prefixPrimes k).card ≤ S.card) :
    (∏ r ∈ prefixPrimes k, r) ≤ ∏ r ∈ S, r := by
  apply initial_prod_le _ _ (T := threshold k) (le_max_left ..) _ _ size
  · exact fun _ hr => (mem_range.mp (mem_filter.mp hr).1).le
  · intro r hr no
    by_contra! h
    exact no (mem_filter.mpr ⟨mem_range.mpr h, prime r hr⟩)

private def bandCap (b k : ℕ) : ℕ :=
  min (2^b-1) ((((150+7*b)*(2^k-1))^2)/25)

private theorem cap_table :
    (List.range 11).all (fun k => (List.range 37).all (fun b =>
      decide (max 2792 (2^(b-1)) ≤ bandCap b k → bandCap b k ≤ basicCap k))) = true := by
  decide +kernel

/-- The dyadic test automatically excludes ten or more distinct factors and
places every remaining modulus below the stated per-factor-count cap. -/
theorem residual_cap {p : ℕ} (hl : 2791 < p) (hu : p < 2^36)
    (res : 25*p ≤ ((150+7*(p.log2+1)) * (2 ^ (p-1).primeFactors.card-1))^2) :
    2 ≤ (p-1).primeFactors.card ∧ (p-1).primeFactors.card ≤ 9 ∧
      p ≤ basicCap (p-1).primeFactors.card := by
  let S := (p-1).primeFactors
  let k := S.card
  let b := p.log2+1
  have sprod : (∏ r ∈ S, r) ≤ p-1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  have primes (r : ℕ) (hr : r ∈ S) : r.Prime := Nat.prime_of_mem_primeFactors hr
  have k10 : k ≤ 10 := by
    by_contra! h
    have card : (prefixPrimes 11).card = 11 := by decide +kernel
    have bound := prefix_prod_le 11 S primes (card ▸ (show 11 ≤ S.card from h))
    have nval : (∏ r ∈ prefixPrimes 11, r) = 200560490130 := by decide +kernel
    rw [nval] at bound; omega
  have low : 2^(b-1) ≤ p := by simpa [b] using Nat.log2_self_le (by omega : p ≠ 0)
  have b36 : b ≤ 36 := by
    by_contra! high
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 36 ≤ b-1 by omega)
    omega
  have below : p ≤ bandCap b k := by
    apply le_min
    · have h := Nat.lt_log2_self (n := p); change p ≤ 2^(p.log2+1)-1; omega
    · apply (Nat.le_div_iff_mul_le (by decide)).mpr
      simpa only [Nat.mul_comm p 25] using res
  have rule := List.all_eq_true.mp (List.all_eq_true.mp cap_table k
    (List.mem_range.mpr (by omega))) b (List.mem_range.mpr (by omega))
  have capped := below.trans ((of_decide_eq_true rule) (max_le (by omega) (low.trans below)))
  have notTen : k ≠ 10 := by
    intro eq
    have card : (prefixPrimes 10).card = 10 := by decide +kernel
    have bound := prefix_prod_le 10 S primes (card ▸ eq.ge)
    have nval : (∏ r ∈ prefixPrimes 10, r) = 6469693230 := by decide +kernel
    rw [nval] at bound
    rw [eq] at capped
    change p ≤ 6076607846 at capped
    omega
  have least : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> simp [basicCap] at capped <;> omega
  exact ⟨least, by change k ≤ 9; omega, capped⟩

#print axioms residual_cap

/-- Every prime divisor the sparse enumerator can need is small. The trial
division for the modulus itself only needs primes up to 37507. -/
theorem residual_search_limits {p : ℕ} (hl : 2791 < p) (hu : p < 2^36)
    (res : 25*p ≤ ((150+7*(p.log2+1)) * (2 ^ (p-1).primeFactors.card-1))^2) :
    p ≤ 1406805054 ∧ p.sqrt ≤ 37507 ∧ ∀ r ∈ (p-1).primeFactors, r ≤ 25230 := by
  let S := (p-1).primeFactors
  let k := S.card
  obtain ⟨klo, khi, capped⟩ := residual_cap hl hu res
  change 2 ≤ k at klo
  change k ≤ 9 at khi
  change p ≤ basicCap k at capped
  have table : (List.range 10).all (fun i => decide
      (basicCap i ≤ 1406805054 ∧ (prefixPrimes i).card = i ∧
        (2 ≤ i → basicCap i ≤ 25230 * ∏ r ∈ prefixPrimes (i-1), r))) = true := by decide +kernel
  have row (i : ℕ) (hi : i < 10) := of_decide_eq_true
    (List.all_eq_true.mp table i (List.mem_range.mpr hi))
  have rk := row k (by omega)
  have hpmax := capped.trans rk.1
  have smax : (1406805054 : ℕ).sqrt ≤ 37507 := by
    apply Nat.le_of_lt_succ
    exact Nat.sqrt_lt'.mpr (by decide)
  refine ⟨hpmax, (Nat.sqrt_le_sqrt hpmax).trans smax, ?_⟩
  intro r hr
  change r ∈ S at hr
  have card : (prefixPrimes (k-1)).card ≤ (S.erase r).card := by
    rw [(row (k-1) (by omega)).2.1, card_erase_of_mem hr]
  have qprod := prefix_prod_le (k-1) (S.erase r)
    (fun t ht => Nat.prime_of_mem_primeFactors (mem_of_mem_erase ht)) card
  have sr : (∏ t ∈ S, t) ≤ p-1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  have rp := Nat.mul_le_mul_left r qprod
  rw [mul_prod_erase S (fun t : ℕ => t) hr] at rp
  have final := (rp.trans sr).trans_lt (show p-1 < p by omega)
  by_contra! high
  have bad := Nat.mul_le_mul_right (∏ t ∈ prefixPrimes (k-1), t) high.le
  omega

#print axioms residual_search_limits

def wheelFactors (p : ℕ) : Finset ℕ := (p-1).primeFactors.filter (· ≤ 43)

def wheelDivisor (p : ℕ) : ℕ := ∏ r ∈ wheelFactors p, r

private def outsideThreshold (i : ℕ) :=
  max 1 (([47,53,59,61,67,71,73,79,83,89] : List ℕ).getD i 1)

def outsidePrimes (i : ℕ) : Finset ℕ :=
  (range (outsideThreshold i)).filter (fun r => r.Prime ∧ 43 < r)

/-- A second representation of every residual. Strip the distinct prime
divisors up to 43 once. The remaining multiplier fits in a range of 592078
integers and its required large-prime factors impose a lower endpoint. -/
theorem residual_wheel {p : ℕ} (hp : p.Prime) (hl : 2791 < p) (hu : p < 2^36)
    (res : 25*p ≤ ((150+7*(p.log2+1)) * (2 ^ (p-1).primeFactors.card-1))^2) :
    2 ∈ wheelFactors p ∧ wheelDivisor p ∣ p-1 ∧
      (∏ r ∈ outsidePrimes ((p-1).primeFactors.card-(wheelFactors p).card), r) ≤ (p-1)/wheelDivisor p ∧
      (p-1)/wheelDivisor p ≤ 592078 := by
  let S := (p-1).primeFactors
  let A := wheelFactors p
  let B := S \ A
  let k := S.card
  let j := A.card
  let d := wheelDivisor p
  have sub : A ⊆ S := filter_subset ..
  have sj : j ≤ k := card_le_card sub
  have bc : B.card = k-j := card_sdiff_of_subset sub
  obtain ⟨kl, kh, capped⟩ := residual_cap hl hu res
  change 2 ≤ k at kl
  change k ≤ 9 at kh
  change p ≤ basicCap k at capped
  have numeric : (List.range 10).all (fun u => decide ((prefixPrimes u).card = u ∧
      (outsidePrimes u).card = u) && (List.range (u+1)).all (fun v => decide
      ((∏ r ∈ prefixPrimes v, r) * (∏ r ∈ outsidePrimes (u-v), r) < basicCap u →
        basicCap u - 1 < 592079 * (∏ r ∈ prefixPrimes v, r)))) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at numeric
  have cardinfo (u : ℕ) (ub : u < 10) := (numeric u ub).1
  have lower := prefix_prod_le j A (fun r h => Nat.prime_of_mem_primeFactors (sub h))
    (by rw [(cardinfo j (by omega)).1])
  change (∏ r ∈ prefixPrimes j, r) ≤ d at lower
  have largeLower : (∏ r ∈ outsidePrimes (k-j), r) ≤ ∏ r ∈ B, r := by
    apply initial_prod_le _ _ (T := outsideThreshold (k-j)) (le_max_left ..)
    · exact fun _ h => (mem_range.mp (mem_filter.mp h).1).le
    · intro r h no
      obtain ⟨hs, missing⟩ := mem_sdiff.mp h
      have gt : 43 < r := by
        by_contra! small
        exact missing (mem_filter.mpr ⟨hs, small⟩)
      by_contra! bound
      exact no (mem_filter.mpr ⟨mem_range.mpr bound, Nat.prime_of_mem_primeFactors hs, gt⟩)
    · rw [(cardinfo (k-j) (by omega)).2, bc]
  have parts : d * (∏ r ∈ B,r) = ∏ r ∈ S,r := by
    have h := prod_inter_mul_prod_sdiff S A (fun r : ℕ => r)
    rwa [inter_eq_right.mpr sub] at h
  have dvd : d ∣ p-1 := (dvd_trans (show d ∣ ∏ r ∈ S,r from ⟨_, parts.symm⟩)
    (Nat.prod_primeFactors_dvd _))
  have dp : 0 < d := Nat.pos_of_dvd_of_pos dvd (by omega)
  have rad : (∏ r ∈ S,r) ≤ p-1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  have avail := Nat.mul_le_mul_left d largeLower
  rw [parts] at avail
  have fits := (Nat.mul_le_mul_right (∏ r ∈ outsidePrimes (k-j), r) lower).trans (avail.trans rad)
  have cond := (numeric k (by omega)).2 j (by omega)
  have cap := cond (fits.trans_lt ((show p-1 < p by omega).trans_le capped))
  obtain ⟨z, hz⟩ := hp.odd_of_ne_two (by omega)
  have divides : 2 ∣ p-1 := ⟨z, by omega⟩
  refine ⟨mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two, divides, by omega⟩, by decide⟩,
    dvd, (Nat.le_div_iff_mul_le dp).mpr (by simpa only [Nat.mul_comm d] using avail.trans rad), ?_⟩
  change (p-1)/d ≤ 592078
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul dp).mpr
  have lim := Nat.mul_le_mul_left 592079 lower
  omega

#print axioms residual_wheel

/-- The same finite calculation indexed by a subset of the fourteen primes
up to 43 and a multiplier of at most 592078. -/
def WheelFiniteInput : Prop :=
  ∀ k ∈ Icc 2 9, ∀ A ∈ ((range 44).filter Nat.Prime).powerset, 2 ∈ A → A.card ≤ k →
    ∀ t ∈ Icc (∏ r ∈ outsidePrimes (k-A.card),r)
      (min 592078 ((basicCap k-1)/(∏ r ∈ A,r))),
      let p := (∏ r ∈ A,r)*t+1
      p.Prime → 2791 < p → p < 2^36 → wheelFactors p = A → (p-1).primeFactors.card = k →
      25*p ≤ ((150+7*(p.log2+1))*(2^k-1))^2 → finiteModulusCheck p = true

theorem wheelFiniteInput_iff : WheelFiniteInput ↔ BasicFiniteInput := by
  constructor
  · intro wheel p hp hl hu res
    let A := wheelFactors p
    let k := (p-1).primeFactors.card
    let d := wheelDivisor p
    let t := (p-1)/d
    obtain ⟨tw, dvd, tmin, tmax⟩ := residual_wheel hp hl hu res
    obtain ⟨kmin, kmax, pmax⟩ := residual_cap hl hu res
    have hlift : A ∈ ((range 44).filter Nat.Prime).powerset := by
      apply mem_powerset.mpr; intro r hr
      obtain ⟨prime, bound⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors prime⟩
    have jle : A.card ≤ k := card_le_card (filter_subset ..)
    have back : d*t+1 = p := by
      dsimp only [t, d]
      rw [Nat.mul_div_cancel' dvd]; omega
    have ht : t ≤ (basicCap k-1)/d :=
      Nat.div_le_div_right (Nat.sub_le_sub_right pmax 1)
    have h := wheel k (mem_Icc.mpr ⟨kmin, kmax⟩) A hlift tw jle t
      (mem_Icc.mpr ⟨tmin, le_min tmax ht⟩)
    change (d*t+1).Prime → 2791 < d*t+1 → d*t+1 < 2^36 → wheelFactors (d*t+1) = A →
      (d*t+1-1).primeFactors.card = k →
      25*(d*t+1) ≤ ((150+7*((d*t+1).log2+1))*(2^k-1))^2 → finiteModulusCheck (d*t+1) = true at h
    rw [back] at h
    exact h hp hl hu rfl rfl res
  · intro basic k _ A _ _ _ t _ p hp hl hu _ count res
    apply basic p hp hl hu
    rwa [count]

#print axioms wheelFiniteInput_iff

end JSP818
