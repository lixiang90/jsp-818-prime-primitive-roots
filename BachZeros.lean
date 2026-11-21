import ZeroKernel
import OAI.NumberTheory.SiegelZeros.Characters.ConductorCompletedL

/-! The Hadamard expansion of a primitive Dirichlet L-function supplies the
actual zero sum. Zeros are counted with the analytic multiplicities of the
normalized completed function. Both logarithmic derivatives on the right are
evaluated in the half-plane of absolute convergence. -/

noncomputable section

namespace JSP818

open DirichletCharacter OAI.SiegelZeros.WeightedTorusJets
open _root_.SiegelZeros.Complex.Hadamard

abbrev LZeros {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p) :=
  divisorZeroIndex₀ (conductorCompletedL χ) Set.univ

abbrev zeroValue {p : ℕ} [NeZero p] {χ : DirichletCharacter ℂ p} (i : LZeros χ) : ℂ :=
  divisorZeroIndex₀Val i

def reflectedMass {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p) : ℝ :=
  (logDeriv (conductorCompletedL χ) bachRightPoint +
   logDeriv (conductorCompletedL χ⁻¹) bachRightPoint).re / 2

variable {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p}

theorem zeroValue_on_line (grh : DirichletGRH) (hχ : χ ≠ 1) (i : LZeros χ) :
    (zeroValue i).re = 1 / 2 :=
  completed_zero_on_line grh hχ <| (conductorCompletedL_zero_iff χ _).mp
    (conductorCompletedL_zeroIndex_vanishes χ hχ i)

/-- Subtraction eliminates the unknown constant in the Hadamard logarithmic derivative. -/
theorem hasSum_anchored_poles (hχ : χ ≠ 1) {s t : ℂ}
    (hs : conductorCompletedL χ s ≠ 0) (ht : conductorCompletedL χ t ≠ 0) :
    HasSum (fun i : LZeros χ => (s - zeroValue i)⁻¹ - (t - zeroValue i)⁻¹)
      (logDeriv (conductorCompletedL χ) s - logDeriv (conductorCompletedL χ) t) := by
  obtain ⟨B, expansion⟩ := conductorCompletedL_logDeriv_hasSum χ
    (primitive_of_prime_modulus Fact.out hχ) hχ
  convert (expansion s hs).sub (expansion t ht) using 1
  · ext i
    simp only [one_div, zeroValue]
    ring
  · ring

private theorem completed_ne_off_line (grh : DirichletGRH) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s.re ≠ 1 / 2) : conductorCompletedL χ s ≠ 0 :=
  fun hz => hs <| completed_zero_on_line grh hχ ((conductorCompletedL_zero_iff _ _).mp hz)

/-- The positive reciprocal-square mass is exactly the reflected logarithmic derivative. -/
theorem hasSum_zero_mass (grh : DirichletGRH) (hχ : χ ≠ 1) :
    HasSum (fun i : LZeros χ => (Complex.normSq (bachRightPoint - zeroValue i))⁻¹)
      (reflectedMass χ) := by
  have right := completed_ne_off_line (χ := χ) grh hχ (s := bachRightPoint) (by norm_num [bachRightPoint])
  have left := completed_ne_off_line (χ := χ) grh hχ (s := bachLeftPoint) (by norm_num [bachLeftPoint])
  have poles := Complex.hasSum_re (hasSum_anchored_poles hχ right left)
  have reflected := logDeriv_conductorCompletedL_one_sub (primitive_of_prime_modulus Fact.out hχ) hχ bachRightPoint
  rw [show 1 - bachRightPoint = bachLeftPoint by norm_num [bachRightPoint, bachLeftPoint]] at reflected
  rw [reflected, sub_neg_eq_add] at poles
  convert poles.mul_left (1 / 2 : ℝ) using 1
  · ext i
    rw [reflected_pole_difference (zeroValue_on_line grh hχ i)]
    ring
  · unfold reflectedMass
    ring

theorem smoothed_zero_sum_le_mass (grh : DirichletGRH) (hχ : χ ≠ 1) :
    Summable (fun i : LZeros χ => ‖(zeroValue i * (zeroValue i + 1))⁻¹‖) ∧
    ∑' i : LZeros χ, ‖(zeroValue i * (zeroValue i + 1))⁻¹‖ ≤ 4 / 3 * reflectedMass χ := by
  have H := (hasSum_zero_mass grh hχ).mul_left (4 / 3 : ℝ)
  have le (i : LZeros χ) := smoothed_zero_kernel_le (zeroValue_on_line grh hχ i)
  simp only [div_eq_mul_inv] at le
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) le H.summable
  exact ⟨hs, (hs.tsum_le_tsum le H.summable).trans_eq H.tsum_eq⟩

#print axioms hasSum_zero_mass
#print axioms smoothed_zero_sum_le_mass

end JSP818
