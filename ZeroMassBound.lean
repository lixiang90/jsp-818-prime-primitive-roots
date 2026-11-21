import BachZeros
import EulerBound
import GammaFactors

noncomputable section

namespace JSP818

open Complex DirichletCharacter Filter OAI.SiegelZeros.WeightedTorusJets
open scoped Topology

/-- The shift at the real place is zero for even characters and one for odd characters. -/
def parityShift {p : ℕ} (χ : DirichletCharacter ℂ p) : ℝ := by
  classical
  exact if χ.Even then 0 else 1

theorem parityShift_cases {p : ℕ} (χ : DirichletCharacter ℂ p) :
    parityShift χ = 0 ∨ parityShift χ = 1 := by
  classical
  by_cases h : χ.Even <;> simp [parityShift, h]

theorem parityShift_nonneg {p : ℕ} (χ : DirichletCharacter ℂ p) : 0 ≤ parityShift χ := by
  rcases parityShift_cases χ with h | h
  · exact h.ge
  · exact zero_le_one.trans_eq h.symm

theorem character_gammaFactor {p : ℕ} (χ : DirichletCharacter ℂ p) :
    gammaFactor χ = fun z => Gammaℝ (z + (parityShift χ : ℂ)) := by
  classical
  funext z
  rcases χ.even_or_odd with h | h
  · simp [h.gammaFactor_def, parityShift, h]
  · simp [h.gammaFactor_def, parityShift, h.not_even]

private theorem differentiableAt_gammaR {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gammaℝ z := by
  have h : DifferentiableAt ℂ (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) z :=
    (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
  simpa only [inv_inv] using h

/-- The conductor, archimedean, and Euler factors on the half-plane of absolute convergence. -/
theorem completed_logDeriv_factors {p : ℕ} [NeZero p] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (conductorCompletedL χ) s = Complex.log (p : ℂ) / 2 +
      (logDeriv (LFunction χ) s + logDeriv Gammaℝ (s + (parityShift χ : ℂ))) := by
  have hp : 0 < s.re := zero_lt_one.trans hs
  have ha := parityShift_nonneg χ
  have ht : 0 < (s + (parityShift χ : ℂ)).re := by simp only [add_re, ofReal_re]; linarith
  rw [conductorCompletedL_logDeriv χ hχ (completedL_ne_zero_of_one_le_re χ hχ hs.le)]
  congr 1
  have eqg : completedLFunction χ =ᶠ[𝓝 s]
      fun z => LFunction χ z * Gammaℝ (z + (parityShift χ : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hp] with z hz
    rw [completedL_eq_mul_gammaFactor χ hz, character_gammaFactor]
  rw [(logDeriv_congr_nhds eqg).eq_of_nhds,
    logDeriv_fun_mul (f := LFunction χ) (g := fun z => Gammaℝ (z + (parityShift χ : ℂ))) s
      (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le) (Gammaℝ_ne_zero_of_re_pos ht)
      (differentiableAt_LFunction χ s (Or.inr hχ))
      ((differentiableAt_gammaR ht).comp s (differentiableAt_id.add_const _)),
    logDeriv_fun_comp (f := Gammaℝ) (g := fun z : ℂ => z + (parityShift χ : ℂ))
      (differentiableAt_gammaR ht) (differentiableAt_id.add_const _)]
  simp

private theorem completed_logDeriv_re_bound {p : ℕ} [NeZero p] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : (logDeriv (conductorCompletedL χ) bachRightPoint).re ≤ Real.log p / 2 + 6 := by
  rw [completed_logDeriv_factors hχ (by norm_num [bachRightPoint]), add_re, add_re,
    div_ofNat_re, ← Complex.natCast_log, ofReal_re]
  have e := (Complex.re_le_norm _).trans (logDeriv_LFunction_three_halves_le χ)
  have g : (logDeriv Gammaℝ (bachRightPoint + (parityShift χ : ℂ))).re ≤ 0 := by
    rw [show bachRightPoint + (parityShift χ : ℂ) = ((3 / 2 + parityShift χ : ℝ) : ℂ) by rw [ofReal_add]]
    apply gammaR_logDeriv_re_nonpos
    · rcases parityShift_cases χ with h | h <;> rw [h] <;> norm_num
    · rcases parityShift_cases χ with h | h <;> rw [h] <;> linarith [Real.pi_gt_three]
  change (logDeriv (LFunction χ) bachRightPoint).re ≤ 6 at e
  linarith

/-- The zero mass grows at most logarithmically in the prime modulus. -/
theorem reflectedMass_le {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : reflectedMass χ ≤ Real.log p / 2 + 6 := by
  unfold reflectedMass
  rw [add_re]
  linarith [completed_logDeriv_re_bound hχ, completed_logDeriv_re_bound (inv_ne_one.mpr hχ)]

theorem grh_smoothed_zero_bound (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    ∑' i : LZeros χ, ‖(zeroValue i * (zeroValue i + 1))⁻¹‖ ≤
      4 / 3 * (Real.log p / 2 + 6) := by
  apply (smoothed_zero_sum_le_mass grh hχ).2.trans
  exact mul_le_mul_of_nonneg_left (reflectedMass_le hχ) (by norm_num)

#print axioms grh_smoothed_zero_bound

end JSP818
