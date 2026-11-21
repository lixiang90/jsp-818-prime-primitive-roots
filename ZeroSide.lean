import ZeroMassBound
import KernelBounds
import UnitMoments
import GridFormula

noncomputable section

namespace JSP818

open Real DirichletCharacter Set MeasureTheory

def normalizedKernel (ρ : ℂ) (x : ℝ) : ℂ := x ^ unitExponent • anchoredKernel ρ x

theorem normalizedKernel_continuousOn {ρ : ℂ} (hr : ρ.re < unitExponent) :
    ContinuousOn (normalizedKernel ρ) (Icc 0 1) := by
  have he : 0 < ((unitExponent : ℂ) - ρ).re := by simpa using sub_pos.mpr hr
  let v (x : ℝ) : ℂ := (x ^ unitExponent : ℝ)
  have cv : Continuous v :=
    Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num : 0 ≤ unitExponent))
  have cont := (((Complex.continuous_ofReal_cpow_const he).mul_const ((ρ * (ρ + 1))⁻¹)).sub
    (cv.mul_const (bachRightPoint / (ρ * (bachRightPoint - ρ))))).add
    ((cv.mul Complex.continuous_ofReal).mul_const ((bachRightPoint + 1) / ((ρ + 1) * (bachRightPoint - ρ))))
  apply cont.continuousOn.congr
  intro x hx
  change v x * anchoredKernel ρ x =
    (x : ℂ) ^ ((unitExponent : ℂ)-ρ) * (ρ*(ρ+1))⁻¹ -
      v x * (bachRightPoint / (ρ*(bachRightPoint-ρ))) +
      (v x*(x : ℂ)) * ((bachRightPoint+1)/((ρ+1)*(bachRightPoint-ρ)))
  by_cases zero : x = 0
  · subst x
    have ne : (unitExponent : ℂ) - ρ ≠ 0 := by intro bad; rw [bad] at he; exact (lt_irrefl 0) he
    simp only [v, Real.zero_rpow (by norm_num : unitExponent ≠ 0), Complex.ofReal_zero,
      Complex.zero_cpow ne, zero_mul, sub_zero, add_zero]
  have hpow : (v x) * (x : ℂ) ^ (-ρ) = (x : ℂ) ^ ((unitExponent : ℂ)-ρ) := by
    dsimp [v]
    rw [Complex.ofReal_cpow hx.1, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr zero)]
    congr 1
  simp only [anchoredKernel, mul_add, mul_sub, ← mul_assoc, hpow]

theorem normalizedKernel_bound {ρ : ℂ} (hr : ρ.re = 1 / 2) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖normalizedKernel ρ x‖ ≤ 7 * (Complex.normSq (bachRightPoint - ρ))⁻¹ := by
  let v := x ^ unitExponent
  have v0 : 0 ≤ v := Real.rpow_nonneg hx.1 _
  have v1 : v ≤ 1 := Real.rpow_le_one hx.1 hx.2 (by norm_num : 0 ≤ unitExponent)
  have vx : v*x ≤ 1 := (mul_le_of_le_one_right v0 hx.2).trans v1
  have vn : v * x ^ (-(1/2 : ℝ)) ≤ 1 := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x; simp [v, Real.zero_rpow (by norm_num : unitExponent ≠ 0)]
    dsimp [v]
    rw [← Real.rpow_add h, show unitExponent + -(1 / 2 : ℝ) = 2 by norm_num]
    exact Real.rpow_le_one hx.1 hx.2 (by norm_num)
  rw [normalizedKernel, norm_smul, Real.norm_of_nonneg v0]
  have h := mul_le_mul_of_nonneg_left (anchoredKernel_le hr hx.1) v0
  change v * ‖anchoredKernel ρ x‖ ≤ _ at h ⊢
  apply h.trans
  rw [div_eq_mul_inv, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Complex.normSq_nonneg _))
  nlinarith

def normalizedZeros {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p) (x : ℝ) : ℂ :=
  ∑' i : LZeros χ, normalizedKernel (zeroValue i) x

theorem normalizedZeros_continuousOn (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    ContinuousOn (normalizedZeros χ) (Icc 0 1) := by
  have hr (i : LZeros χ) := zeroValue_on_line grh hχ i
  exact continuousOn_tsum (fun i => normalizedKernel_continuousOn (by rw [hr i]; norm_num))
    ((hasSum_zero_mass grh hχ).summable.mul_left (7 : ℝ))
    (fun i _ hx => normalizedKernel_bound (hr i) hx)

/-- GRH controls the whole sum of anchored kernels, including the two lower
order terms. All zeros are taken with their analytic multiplicities. -/
theorem grh_anchored_sum_le (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun i : LZeros χ => anchoredKernel (zeroValue i) y) ∧
    ‖∑' i : LZeros χ, anchoredKernel (zeroValue i) y‖ ≤
      (4 / 3 * y ^ (-(1 / 2 : ℝ)) + 3 + 5 / 2 * y) * (log p / 2 + 6) := by
  let A := 4 / 3 * y ^ (-(1 / 2 : ℝ)) + 3 + 5 / 2 * y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have mass := (hasSum_zero_mass grh hχ).mul_left A
  have le (i : LZeros χ) : ‖anchoredKernel (zeroValue i) y‖ ≤
      A * (Complex.normSq (bachRightPoint - zeroValue i))⁻¹ := by
    simpa only [A, div_eq_mul_inv] using anchoredKernel_le (zeroValue_on_line grh hχ i) hy
  have sm := Summable.of_nonneg_of_le (fun i => norm_nonneg (anchoredKernel (zeroValue i) y))
    le mass.summable
  refine ⟨sm.of_norm, (norm_tsum_le_tsum_norm sm).trans ?_⟩
  exact (sm.tsum_le_tsum le mass.summable).trans
    (mass.tsum_eq.le.trans (mul_le_mul_of_nonneg_left (reflectedMass_le hχ) hA))

#print axioms grh_anchored_sum_le

end JSP818
