import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

noncomputable section

namespace JSP818

open Set MeasureTheory

abbrev unitExponent : ℝ := 5 / 2

/-- Absolute uniform majorants allow termwise integration on the unit interval. -/
theorem unit_hasSum_integral {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {w : ι → ℝ}
    (cont : ∀ i, ContinuousOn (F i) (Icc 0 1)) (hw : Summable w)
    (bound : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖F i x‖ ≤ w i) :
    HasSum (fun i => ∫ x : ℝ in 0..1, F i x) (∫ x : ℝ in 0..1, ∑' i, F i x) := by
  have hi (i : ι) := (cont i).intervalIntegrable_of_Icc zero_le_one (μ := volume)
  have hb (i : ι) : (∫ x : ℝ in 0..1, ‖F i x‖) ≤ w i := by
    have h := intervalIntegral.integral_mono_on zero_le_one (hi i).norm
      (intervalIntegrable_const (c := w i)) (bound i)
    simpa using h
  have hn (i : ι) : 0 ≤ ∫ x : ℝ in 0..1, ‖F i x‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have sm := Summable.of_nonneg_of_le hn hb hw
  simp_rw [intervalIntegral.integral_of_le zero_le_one] at sm ⊢
  exact hasSum_integral_of_summable_integral_norm (fun i => (hi i).1) sm

/-- A single term of the linearly smoothed von Mangoldt sum. The weight
vanishes continuously at the positive endpoint. -/
def cutoffWeight (n : ℕ) (x : ℝ) : ℝ := max (1 - n * x) 0

theorem cutoffWeight_continuous (n : ℕ) : Continuous (cutoffWeight n) := by
  unfold cutoffWeight
  fun_prop

theorem cutoff_moment {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in 0..1, x ^ (s - 1) * cutoffWeight n x) =
      ((n : ℝ)⁻¹) ^ s / (s * (s + 1)) := by
  let t := (n : ℝ)⁻¹
  have np : (0 : ℝ) < n := by exact_mod_cast hn
  have tp : 0 < t := inv_pos.mpr np
  have t1 : t ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have nt : (n : ℝ) * t = 1 := mul_inv_cancel₀ np.ne'
  have hcont : Continuous (fun x : ℝ => x ^ (s - 1) * cutoffWeight n x) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).mul (cutoffWeight_continuous n)
  have front : (∫ x : ℝ in 0..t, x ^ (s - 1) * cutoffWeight n x) =
      ∫ x : ℝ in 0..t, (x ^ (s - 1) - (n : ℝ) * x ^ s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x
    intro hx
    rw [Set.uIoc_of_le tp.le] at hx
    have hn1 : (n : ℝ) * x ≤ 1 := (mul_le_mul_of_nonneg_left hx.2 np.le).trans_eq nt
    rw [cutoffWeight, max_eq_left (sub_nonneg.mpr hn1)]
    have power : x ^ (s - 1) * x = x ^ s := by
      rw [← Real.rpow_add_one hx.1.ne', sub_add_cancel]
    linear_combination (-n : ℝ) * power
  have back : (∫ x : ℝ in t..1, x ^ (s - 1) * cutoffWeight n x) = 0 := by
    trans ∫ _x : ℝ in t..1, (0 : ℝ)
    · apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le t1] at hx
      have hx1 := mul_le_mul_of_nonneg_left hx.1 np.le
      rw [nt] at hx1
      change x ^ (s - 1) * cutoffWeight n x = 0
      rw [cutoffWeight, max_eq_right (sub_nonpos.mpr hx1), mul_zero]
    · simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 t)
    (hcont.intervalIntegrable t 1), front, back, add_zero]
  have s0 : 0 < s := by linarith
  have s1 : 0 < s + 1 := by linarith
  rw [intervalIntegral.integral_sub
    ((Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).intervalIntegrable 0 t)
    (((Real.continuous_rpow_const s0.le).const_mul (n : ℝ)).intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < s - 1)),
    integral_rpow (Or.inl (by linarith : -1 < s)), sub_add_cancel,
    Real.zero_rpow s0.ne', Real.zero_rpow s1.ne', sub_zero, sub_zero, Real.rpow_add_one tp.ne']
  change t ^ s / s - (n : ℝ) * (t ^ s * t / (s + 1)) = t ^ s / (s * (s + 1))
  rw [show (n : ℝ) * (t ^ s * t / (s + 1)) = t ^ s / (s + 1) by
    rw [show (n : ℝ) * (t ^ s * t / (s + 1)) = ((n : ℝ) * t) * t ^ s / (s + 1) by ring, nt, one_mul]]
  field_simp [s0.ne', s1.ne']
  ring

#print axioms cutoff_moment

end JSP818
