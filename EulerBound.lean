import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

noncomputable section

namespace JSP818

open MeasureTheory Real ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-- A quantitative bound convenient for the absolutely convergent Euler sum.
Use the tangent to log at e, after replacing x by its fourth root. -/
theorem log_le_three_halves_fourth_root {x : ℝ} (hx : 0 < x) :
    log x ≤ 3 / 2 * x ^ (1 / 4 : ℝ) := by
  have hp := rpow_pos_of_pos hx (1 / 4 : ℝ)
  have h := Real.log_le_sub_one_of_pos (div_pos hp (Real.exp_pos 1))
  rw [Real.log_div hp.ne' (Real.exp_pos 1).ne', Real.log_rpow hx, Real.log_exp] at h
  have h' : (1 / 4 : ℝ) * log x ≤ x ^ (1 / 4 : ℝ) / Real.exp 1 := by linarith
  have e : 8 / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h'' : x ^ (1 / 4 : ℝ) / Real.exp 1 ≤ 3 / 8 * x ^ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left e hp.le]
  linarith

private theorem tail_rpow_le_four :
    ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) ≤ 4 := by
  have mono : AntitoneOn (fun x : ℝ => x ^ (-(5 / 4 : ℝ))) (Set.Ici (1 : ℝ)) :=
    fun x hx _ _ h => rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) h (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-(5 / 4 : ℝ))) 1
    (by simpa using mono) (by simpa using (integrableOn_Ioi_rpow_of_lt
      (show -(5 / 4 : ℝ) < -1 by norm_num) zero_lt_one))
    (fun x hx => rpow_nonneg (by simp at hx; linarith) _)
  rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one] at h
  norm_num at h
  simpa [add_assoc, one_add_one_eq_two] using h

/-- Absolute convergence gives a numerical bound independent of the character and modulus. -/
theorem logDeriv_LFunction_three_halves_le {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p) :
    ‖logDeriv (LFunction χ) ((3 / 2 : ℝ) : ℂ)‖ ≤ 6 := by
  let b : ℂ := (3 / 2 : ℝ)
  have hb : 1 < b.re := by norm_num [b]
  let f := LSeries.term (↗χ * ↗Λ) b
  have hf : Summable f := LSeriesSummable_twist_vonMangoldt χ hb
  have eqnorm : ‖logDeriv (LFunction χ) b‖ = ‖∑' n, f n‖ := by
    change ‖deriv (LFunction χ) b / LFunction χ b‖ = ‖LSeries (↗χ * ↗Λ) b‖
    rw [LSeries_twist_vonMangoldt_eq χ hb, deriv_LFunction_eq_deriv_LSeries χ hb,
      LFunction_eq_LSeries χ hb]
    simp [neg_div]
  have bound (n : ℕ) (hn : 0 < n) :
      ‖f n‖ ≤ 3 / 2 * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hΛ : ‖(↗χ * ↗Λ) n‖ ≤ log (n : ℝ) := by
      calc
        _ ≤ ‖(↗Λ n : ℂ)‖ := by
          simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
            (χ.norm_le_one (n : ZMod p))
        _ = vonMangoldt n := Complex.norm_of_nonneg vonMangoldt_nonneg
        _ ≤ _ := vonMangoldt_le_log
    rw [show ‖f n‖ = ‖(↗χ * ↗Λ) n‖ / (n : ℝ) ^ (3 / 2 : ℝ) by
      simp only [f, LSeries.norm_term_eq, ite_eq_right hn.ne', b, Complex.ofReal_re]]
    calc
      _ ≤ (3 / 2 * (n : ℝ) ^ (1 / 4 : ℝ)) / (n : ℝ) ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (hΛ.trans (log_le_three_halves_fourth_root hnR))
          (Real.rpow_nonneg hnR.le _)
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_sub hnR]
        norm_num
  have htail : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  have hle := ((summable_nat_add_iff 2).mpr hf.norm).tsum_le_tsum
    (fun n => bound (n + 2) (by omega)) (htail.mul_left (3 / 2 : ℝ))
  rw [tsum_mul_left] at hle
  have hsplit := hf.norm.sum_add_tsum_nat_add 2
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 0 := by simp [f]
  simp [Finset.sum_range_succ, h0, h1] at hsplit
  rw [eqnorm]
  apply (norm_tsum_le_tsum_norm hf.norm).trans
  linarith [tail_rpow_le_four]

#print axioms logDeriv_LFunction_three_halves_le

end JSP818
