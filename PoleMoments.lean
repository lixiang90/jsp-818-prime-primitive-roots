import ArithmeticMoments
import ZeroSide

noncomputable section

namespace JSP818

open Set MeasureTheory Real DirichletCharacter

theorem normalizedKernel_moment (m : ℕ) {ρ : ℂ} (hr : ρ.re < unitExponent)
    (h0 : ρ ≠ 0) (h1 : ρ + 1 ≠ 0) (hb : bachRightPoint - ρ ≠ 0) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • normalizedKernel ρ x) =
      (((mellinPoint (m+1) : ℂ) - ρ)⁻¹ - (bachRightPoint - ρ)⁻¹) /
        ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ) + 1)) := by
  let s : ℂ := mellinPoint (m+1)
  have hs : unitExponent < s.re := by
    dsimp [s, mellinPoint, unitExponent]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  apply Eq.trans _ (integral_anchoredKernel (lt_trans (by norm_num : 0 < unitExponent) hs)
    (hr.trans hs) h0 h1 hb)
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x
  intro hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  rw [normalizedKernel, smul_smul, Complex.real_smul, grid_power m hx.1,
    Complex.ofReal_cpow hx.1.le]
  push_cast
  rfl

private theorem zeros_countable (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) : Countable (LZeros χ) := by
  have h := (hasSum_zero_mass grh hχ).summable.countable_support
  have ne (i : LZeros χ) : bachRightPoint - zeroValue i ≠ 0 := by
    intro eq
    have := congrArg Complex.re eq
    norm_num [bachRightPoint, Complex.sub_re, zeroValue_on_line grh hχ i] at this
  have all : Function.support (fun i : LZeros χ => (Complex.normSq (bachRightPoint - zeroValue i))⁻¹) =
      Set.univ := Set.eq_univ_of_forall fun i => inv_ne_zero (Complex.normSq_pos.mpr (ne i)).ne'
  rw [all] at h
  exact Set.countable_univ_iff.mp h

theorem normalizedZeros_moment (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (m : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • normalizedZeros χ x) =
      (∑' i : LZeros χ, (((mellinPoint (m+1) : ℂ) - zeroValue i)⁻¹ -
        (bachRightPoint - zeroValue i)⁻¹)) /
        ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ) + 1)) := by
  let : Countable (LZeros χ) := zeros_countable grh hχ
  have hr (i : LZeros χ) := zeroValue_on_line grh hχ i
  have he (i : LZeros χ) : (zeroValue i).re < unitExponent := by rw [hr i]; norm_num
  have eq := unit_hasSum_integral
    (F := fun (i : LZeros χ) x => x ^ (2*m) • normalizedKernel (zeroValue i) x)
    (fun i => (continuous_id.pow (2*m)).continuousOn.smul (normalizedKernel_continuousOn (he i)))
    ((hasSum_zero_mass grh hχ).summable.mul_left (7 : ℝ))
    (fun i x hx => by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx.1 _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hx.1 hx.2)).trans
        (normalizedKernel_bound (hr i) hx))
  have term (i : LZeros χ) := normalizedKernel_moment m (he i)
    (by intro e; have := hr i; rw [e] at this; norm_num at this)
    (by intro e; have h := congrArg Complex.re e; norm_num [Complex.add_re, hr i] at h)
    (by intro e; have h := congrArg Complex.re e; norm_num [Complex.sub_re, bachRightPoint, hr i] at h)
  simp_rw [term] at eq
  rw [← tsum_div_const, eq.tsum_eq]
  apply intervalIntegral.integral_congr
  intro x _
  exact (tsum_const_smul'' (f := fun i : LZeros χ => normalizedKernel (zeroValue i) x)
    (x ^ (2*m))).symm

#print axioms normalizedZeros_moment

end JSP818
