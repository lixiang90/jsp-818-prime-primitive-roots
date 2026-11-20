import SmoothedSums
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Complex.ExponentialBounds

/-! An elementary lower bound for the principal sum. Every prime power
dividing a binomial coefficient in row `n` is at most `n`. The largest entry
in that row therefore gives a lower bound for the Chebyshev function. -/

noncomputable section

open Finset Real

namespace JSP818.CharacterSieve

private def psiNat (n : ℕ) : ℝ := ∑ j ∈ range (n + 1), ArithmeticFunction.vonMangoldt j

private theorem log_choose_le_psi {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    log (n.choose k) ≤ psiNat n := by
  classical
  let Λ := ArithmeticFunction.vonMangoldt
  rw [← ArithmeticFunction.vonMangoldt_sum]
  change ∑ j ∈ (n.choose k).divisors, Λ j ≤ ∑ j ∈ range (n + 1), Λ j
  rw [← sum_filter_ne_zero (s := (n.choose k).divisors) (f := fun j => Λ j)]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  intro m hm
  obtain ⟨hd, hw⟩ := mem_filter.mp hm
  obtain ⟨q, a, hq, _, rfl⟩ := (isPrimePow_nat_iff m).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hw)
  have he := (hq.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hk)).mp
    (Nat.dvd_of_mem_divisors hd)
  exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.pow_le_pow_right hq.pos he).trans
    (Nat.pow_factorization_choose_le hn)))

private theorem psiNat_lower (n : ℕ) : (n : ℝ) * log 2 - log (n + 1) ≤ psiNat n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [psiNat]
  have hk : n / 2 ≤ n := Nat.div_le_self ..
  have hc : 0 < n.choose (n / 2) := Nat.choose_pos hk
  have peak : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := calc
    _ = ∑ k ∈ range (n + 1), n.choose k := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _k ∈ range (n + 1), n.choose (n / 2) := sum_le_sum fun k _ => Nat.choose_le_middle k n
    _ = _ := by simp
  have logPeak := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ n)
    (show (2 : ℝ) ^ n ≤ (n + 1) * (n.choose (n / 2) : ℝ) by exact_mod_cast peak)
  rw [Real.log_pow, Real.log_mul (by positivity) (by exact_mod_cast hc.ne')] at logPeak
  linarith [log_choose_le_psi hn hk]

private theorem cumulative_psi (N : ℕ) :
    ∑ d ∈ range N, ArithmeticFunction.vonMangoldt d * ((N : ℝ) - d) =
    ∑ k ∈ range N, psiNat k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ (f := psiNat)]
    simp only [Nat.cast_succ]
    have hs : ∑ d ∈ range N, ArithmeticFunction.vonMangoldt d * ((N : ℝ) + 1 - d) =
        ∑ d ∈ range N, (ArithmeticFunction.vonMangoldt d * ((N : ℝ) - d) + ArithmeticFunction.vonMangoldt d) := by
      apply sum_congr rfl; intros; ring
    rw [hs, sum_add_distrib, ih, psiNat, sum_range_succ]
    ring

private theorem total_weight_mul {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ Ico 1 N, mangoldtWeight N d) * N = ∑ k ∈ range N, psiNat k := by
  have sub : Ico 1 N ⊆ range N := fun _ h => mem_range.mpr (mem_Ico.mp h).2
  have hz : ∑ d ∈ Ico 1 N, mangoldtWeight N d = ∑ d ∈ range N, mangoldtWeight N d := by
    apply sum_subset sub
    intro d hd hx
    have hlt := mem_range.mp hd
    have : d = 0 := by contrapose! hx; exact mem_Ico.mpr ⟨Nat.pos_of_ne_zero hx, hlt⟩
    simp [this, mangoldtWeight]
  rw [hz, sum_mul, ← cumulative_psi]
  apply sum_congr rfl
  intro d _
  unfold mangoldtWeight
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']

private theorem twice_sum_indices (N : ℕ) :
    (∑ k ∈ range N, (k : ℝ)) * 2 = (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, Nat.cast_succ]; linarith

/-- An unconditional lower bound for the exact smoothed principal character sum. -/
theorem principal_mass_lower {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) - 1) * log 2 / 2 - log N ≤ ∑ d ∈ Ico 1 N, mangoldtWeight N d := by
  have hr : 0 < (N : ℝ) := by exact_mod_cast hN
  have each (k : ℕ) (hk : k ∈ range N) : (k : ℝ) * log 2 - log N ≤ psiNat k := by
    have hlog := Real.log_le_log (by positivity : 0 < (k : ℝ) + 1)
      (show (k : ℝ) + 1 ≤ N by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hk))
    linarith [psiNat_lower k]
  have hsum := sum_le_sum each
  have triangle := twice_sum_indices N
  rw [sum_sub_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul,
    ← total_weight_mul hN] at hsum
  apply (le_of_mul_le_mul_right _ hr)
  calc
    _ = (∑ k ∈ range N, (k : ℝ)) * log 2 - (N : ℝ) * log N := by linear_combination (-(log 2)/2) * triangle
    _ ≤ _ := hsum

theorem principal_mass_ge_third {N : ℕ} (hN : 1024 ≤ N) :
    (N : ℝ) / 3 ≤ ∑ d ∈ Ico 1 N, mangoldtWeight N d := by
  have hn : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by linarith
  have hs := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / 1024 by positivity)
  rw [Real.log_div hpos.ne' (by norm_num), show (1024 : ℝ) = 2 ^ 10 by norm_num,
    Real.log_pow] at hs
  have hlog : 0.69 < log 2 := by linarith [Real.log_two_gt_d9]
  apply le_trans _ (principal_mass_lower (show 0 < N by omega))
  nlinarith [Real.log_two_lt_d9, mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ N by linarith))
    (sub_nonneg.mpr hlog.le)]

#print axioms principal_mass_ge_third

/-- The large-modulus reduction uses only the nonprincipal part of Bach's
estimate and an elementary size comparison. The principal sum is proved above. -/
theorem prime_root_of_sqrt_log_bound {p : ℕ} [Fact p.Prime] (hp : 1024 ≤ p)
    (hχ : ∀ χ : Character p, χ ≠ 1 → ‖mangoldtTwist χ‖ ≤ √(p : ℝ) * log p)
    (hsize : 3 * ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * log p < √(p : ℝ)) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  apply prime_primitive_root_of_mangoldtTwists _ hχ
  apply lt_of_lt_of_le _ (principal_mass_ge_third hp)
  have hs : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < p by omega))
  have h := mul_lt_mul_of_pos_right hsize hs
  rw [← sq, Real.sq_sqrt (Nat.cast_nonneg p)] at h
  linarith

#print axioms prime_root_of_sqrt_log_bound

end JSP818.CharacterSieve
