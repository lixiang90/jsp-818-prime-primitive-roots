import PrincipalMass

noncomputable section

namespace JSP818.CharacterSieve

open Finset Real
open scoped NNReal

private def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

private theorem mem_small {r : ℕ} (hr : r.Prime) (hlt : r < 16) : r ∈ smallPrimes := by
  interval_cases r <;> norm_num [smallPrimes] at *

private theorem prime_factor_count_aux (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    (16 : ℝ≥0) ^ S.card ≤ 560 * ∏ r ∈ S, (r : ℝ≥0) := by
  let w (r : ℕ) : ℝ≥0 := if r ∈ smallPrimes then 16 / r else 1
  have point (r : ℕ) (hr : r ∈ S) : (16 : ℝ≥0) ≤ w r * r := by
    by_cases h : r ∈ smallPrimes
    · simp only [w, if_pos h]
      rw [div_mul_cancel₀ _ (by exact_mod_cast (hS r hr).ne_zero)]
    · simp only [w, if_neg h, one_mul]
      exact_mod_cast (show 16 ≤ r from le_of_not_gt (fun hlt => h (mem_small (hS r hr) hlt)))
  have extra : ∏ r ∈ S, w r ≤ 560 := by
    change (∏ r ∈ S, if r ∈ smallPrimes then (16 : ℝ≥0) / r else 1) ≤ 560
    rw [prod_ite_mem]
    apply le_trans (prod_le_prod_of_subset_of_one_le' (Finset.inter_subset_right : S ∩ smallPrimes ⊆ smallPrimes) ?_)
    · rw [← NNReal.coe_le_coe, NNReal.coe_prod]
      norm_num [smallPrimes, Finset.prod_insert, NNReal.coe_div]
    · intro r hr _
      simp only [smallPrimes, mem_insert, mem_singleton] at hr
      rw [← NNReal.coe_le_coe, NNReal.coe_div]
      rcases hr with h | h | h | h | h | h <;> subst r <;> norm_num
  calc
    (16 : ℝ≥0) ^ S.card = ∏ _r ∈ S, 16 := by simp
    _ ≤ ∏ r ∈ S, (w r * r) := prod_le_prod' point
    _ = (∏ r ∈ S, w r) * ∏ r ∈ S, (r : ℝ≥0) := prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right extra zero_le

/-- The six primes below 16 give a uniform numerical version of the
subpolynomial growth of the number of squarefree divisors. -/
theorem prime_factor_count_bound {n : ℕ} (hn : 0 < n) :
    (16 : ℝ) ^ n.primeFactors.card ≤ 560 * n := by
  have h := prime_factor_count_aux n.primeFactors (fun _ hr => Nat.prime_of_mem_primeFactors hr)
  have hrad := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hr : (∏ r ∈ n.primeFactors, (r : ℝ≥0)) ≤ (n : ℝ≥0) := by
    rw [← Nat.cast_prod (fun r : ℕ => r)]
    exact_mod_cast hrad
  exact_mod_cast h.trans (mul_le_mul_of_nonneg_left hr (show 0 ≤ (560 : ℝ≥0) from zero_le))

/-- At this explicit cutoff the elementary size condition in the character sieve
holds for every modulus, regardless of the factorization of its predecessor. -/
theorem sqrt_dominates_sieve {p : ℕ} (hp : 2 ^ 36 ≤ p) :
    3 * ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * log p < √(p : ℝ) := by
  have hpR : (2 : ℝ) ^ 36 ≤ p := by exact_mod_cast hp
  let u : ℝ := (p : ℝ) ^ (1 / 4 : ℝ)
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hu : 0 < u := Real.rpow_pos_of_pos hp0 _
  have up : u ^ 4 = p := by
    rw [show u ^ 4 = ((p : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) by norm_cast,
      ← Real.rpow_mul hp0.le]
    norm_num
  have us : u ^ 2 = √(p : ℝ) := by
    rw [Real.sqrt_eq_rpow, show u ^ 2 = ((p : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_mul hp0.le]
    norm_num
  have h512 : 512 ≤ u := by
    by_contra! h
    have le := pow_lt_pow_left₀ h hu.le (by decide : (4 : ℕ) ≠ 0)
    rw [up] at le
    norm_num at hpR le
    linarith
  have hlog : log p ≤ u / 16 := by
    have ht := Real.log_le_sub_one_of_pos (show 0 < u / 512 by positivity)
    rw [Real.log_div hu.ne' (by norm_num), show (512 : ℝ) = 2 ^ 9 by norm_num,
      Real.log_pow, show log u = (1 / 4 : ℝ) * log p by exact Real.log_rpow hp0 _] at ht
    linarith [Real.log_two_lt_d9]
  let A : ℝ := 2 ^ (p - 1).primeFactors.card
  have hA : A ^ 4 ≤ 560 * p := by
    have h := prime_factor_count_bound (n := p - 1) (by omega)
    have he : A ^ 4 = (16 : ℝ) ^ (p - 1).primeFactors.card := by
      dsimp [A]
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [he]
    exact h.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le p 1) (by norm_num))
  have hA' : A ≤ 5 * u := by
    by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by positivity) (by decide : (4 : ℕ) ≠ 0)
    rw [mul_pow, up] at hh'
    nlinarith
  have hlog0 : 0 ≤ log p := Real.log_nonneg (by linarith)
  change 3 * (A - 1) * log p < _
  rw [← us]
  calc
    _ ≤ 3 * (5 * u) * log p := mul_le_mul_of_nonneg_right (by linarith) hlog0
    _ ≤ 3 * (5 * u) * (u / 16) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ < _ := by nlinarith [sq_pos_of_pos hu]

#print axioms sqrt_dominates_sieve

/-- In this range the nonprincipal estimate alone implies the original
primitive-root conclusion. There is no additional factor-count assumption. -/
theorem prime_root_of_large_twist_bound {p : ℕ} [Fact p.Prime] (hp : 2 ^ 36 ≤ p)
    (hχ : ∀ χ : Character p, χ ≠ 1 → ‖mangoldtTwist χ‖ ≤ √(p : ℝ) * log p) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  prime_root_of_sqrt_log_bound (by omega) hχ (sqrt_dominates_sieve hp)

#print axioms prime_root_of_large_twist_bound

end JSP818.CharacterSieve
