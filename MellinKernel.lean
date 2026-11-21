import ZeroKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Inverse Mellin kernel for a pole after subtracting its value at (3/2).
The cancellations in the two constant terms make the sum over zeros absolutely
convergent. -/

noncomputable section

namespace JSP818

open MeasureTheory intervalIntegral

/-- Inverse Mellin transform of the anchored simple pole divided by (s(s+1)).
The formula applies to every pole distinct from the two smoothing poles. -/
def anchoredKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (-ρ) * (ρ * (ρ + 1))⁻¹ - bachRightPoint / (ρ * (bachRightPoint - ρ)) +
    (y : ℂ) * ((bachRightPoint + 1) / ((ρ + 1) * (bachRightPoint - ρ)))

theorem integral_unit_cpow {z : ℂ} (hz : 0 < z.re) :
    (∫ y : ℝ in 0..1, (y : ℂ) ^ (z - 1)) = z⁻¹ := by
  have hne : z ≠ 0 := by rintro rfl; simp at hz
  rw [integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))]
  simp [hne, one_div]

private theorem anchored_partial_fractions {s ρ b : ℂ}
    (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) (hρ : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0)
    (hsρ : s - ρ ≠ 0) (hbρ : b - ρ ≠ 0) :
    (s - ρ)⁻¹ * (ρ * (ρ + 1))⁻¹ - s⁻¹ * (b / (ρ * (b - ρ))) +
      (s + 1)⁻¹ * ((b + 1) / ((ρ + 1) * (b - ρ))) =
        ((s - ρ)⁻¹ - (b - ρ)⁻¹) / (s * (s + 1)) := by
  have h1 : b / (ρ * (b - ρ)) = ρ⁻¹ + (b - ρ)⁻¹ := by
    field_simp [hρ, hbρ]
    ring
  have h2 : (b + 1) / ((ρ + 1) * (b - ρ)) = (ρ + 1)⁻¹ + (b - ρ)⁻¹ := by
    field_simp [hρ1, hbρ]
    ring
  have h3 : s⁻¹ - (s + 1)⁻¹ = (s * (s + 1))⁻¹ := by
    field_simp [hs, hs1]
    ring
  have h4 : (s - ρ)⁻¹ * (ρ * (ρ + 1))⁻¹ - s⁻¹ * ρ⁻¹ + (s + 1)⁻¹ * (ρ + 1)⁻¹ =
      (s - ρ)⁻¹ * (s * (s + 1))⁻¹ := by
    have gap {a c : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) (hd : c - a ≠ 0) :
        (c - a)⁻¹ * (a⁻¹ - c⁻¹) = a⁻¹ * c⁻¹ := by
      rw [inv_sub_inv' ha hc]
      calc
        _ = ((c - a)⁻¹ * (c - a)) * (a⁻¹ * c⁻¹) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]
    have d := gap hsρ hs (by simpa using hρ)
    have d' := gap hsρ hs1 (by rwa [show s + 1 - (s - ρ) = ρ + 1 by ring])
    rw [show s - (s - ρ) = ρ by ring] at d
    rw [show s + 1 - (s - ρ) = ρ + 1 by ring] at d'
    have e : ρ⁻¹ - (ρ + 1)⁻¹ = (ρ * (ρ + 1))⁻¹ := by
      field_simp [hρ, hρ1]
      ring
    rw [← e, ← h3]
    linear_combination d - d'
  rw [h1, h2, div_eq_mul_inv]
  linear_combination h4 - (b - ρ)⁻¹ * h3

/-- Exact moment of the zero contribution in the explicit formula. -/
theorem integral_anchoredKernel {s ρ : ℂ} (hs : 0 < s.re) (hρs : ρ.re < s.re)
    (hρ : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0) (hbρ : bachRightPoint - ρ ≠ 0) :
    (∫ y : ℝ in 0..1, (y : ℂ) ^ (s - 1) * anchoredKernel ρ y) =
      ((s - ρ)⁻¹ - (bachRightPoint - ρ)⁻¹) / (s * (s + 1)) := by
  have hsρ : 0 < (s - ρ).re := by simpa only [Complex.sub_re, sub_pos] using hρs
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have intg {z : ℂ} (hz : 0 < z.re) :
      IntervalIntegrable (fun y : ℝ => (y : ℂ) ^ (z - 1)) volume 0 1 :=
    intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have ieq : (∫ y : ℝ in 0..1, (y : ℂ) ^ (s - 1) * anchoredKernel ρ y) =
      ∫ y : ℝ in 0..1, (y : ℂ) ^ (s - ρ - 1) * (ρ * (ρ + 1))⁻¹ -
        (y : ℂ) ^ (s - 1) * (bachRightPoint / (ρ * (bachRightPoint - ρ))) +
        (y : ℂ) ^ (s + 1 - 1) * ((bachRightPoint + 1) / ((ρ + 1) * (bachRightPoint - ρ))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y
    intro hy
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.1.ne'
    have powers : (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-ρ) = (y : ℂ) ^ (s - ρ - 1) := by
      rw [← Complex.cpow_add _ _ hy0]; congr 1; ring
    have linear : (y : ℂ) ^ (s - 1) * (y : ℂ) = (y : ℂ) ^ (s + 1 - 1) := by
      rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
    simp only [anchoredKernel, mul_add, mul_sub, ← mul_assoc, powers, linear]
  rw [ieq, integral_add (((intg hsρ).mul_const _).sub ((intg hs).mul_const _))
    ((intg hs1).mul_const _), integral_sub ((intg hsρ).mul_const _) ((intg hs).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, integral_unit_cpow hsρ,
    integral_unit_cpow hs, integral_unit_cpow hs1]
  have ne {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by rintro rfl; simp at hz
  exact anchored_partial_fractions (ne hs) (ne hs1) hρ hρ1 (ne hsρ) hbρ

#print axioms integral_anchoredKernel

end JSP818
