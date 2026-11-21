import TrivialTail
import FirstPole
import MomentUniqueness
import FiniteReduction

noncomputable section

namespace JSP818

open Real Set MeasureTheory DirichletCharacter CharacterSieve

private def moment (m : ℕ) (f : ℝ → ℂ) := ∫ x : ℝ in 0..1, x^(2*m) • f x

private theorem moment_add (m : ℕ) {f g : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) : moment m (f+g) = moment m f + moment m g := by
  unfold moment
  simp only [Pi.add_apply, smul_add]
  exact intervalIntegral.integral_add
    (((continuous_id.pow (2*m)).continuousOn.smul hf).intervalIntegrable_of_Icc zero_le_one)
    (((continuous_id.pow (2*m)).continuousOn.smul hg).intervalIntegrable_of_Icc zero_le_one)

def linearSide (d : ℂ) (x : ℝ) : ℂ := ((x^unitExponent * (1-x) : ℝ) : ℂ) * d
def firstSide (a x : ℝ) : ℂ := (x^unitExponent * firstTrivialKernel a x : ℝ)

private theorem linear_moment (m : ℕ) (d : ℂ) :
    moment m (linearSide d) = d / ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ)+1)) := by
  have hs : 1 < mellinPoint (m+1) := by dsimp [mellinPoint]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  unfold moment linearSide
  simp only [← smul_mul_assoc]
  rw [intervalIntegral.integral_mul_const, normalizedReal_moment m (fun x => 1-x), unit_weight_moment hs]
  push_cast
  ring

private theorem first_moment {a : ℝ} (ha : a = 0 ∨ a = 1) (m : ℕ) :
    moment m (firstSide a) = (((mellinPoint (m+1) : ℂ) + a)⁻¹ - (bachRightPoint + a)⁻¹) /
      ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ)+1)) := by
  have hs : 1 < mellinPoint (m+1) := by dsimp [mellinPoint]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  unfold moment firstSide
  rw [normalizedReal_moment m (firstTrivialKernel a), firstTrivial_moment hs ha]
  push_cast
  norm_num [bachRightPoint]

/-- The complete anchored explicit formula, recovered on the positive real
axis from an absolutely convergent moment grid and polynomial approximation. -/
theorem normalized_explicit_formula (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    arithmeticSide χ x + linearSide (logDeriv (LFunction χ) bachRightPoint) x +
      normalizedZeros χ x + firstSide (parityShift χ) x + normalizedTail (parityShift χ) x = 0 := by
  let a := parityShift χ
  let d := logDeriv (LFunction χ) bachRightPoint
  let F := arithmeticSide χ + linearSide d + normalizedZeros χ + firstSide a + normalizedTail a
  have ca := arithmeticSide_continuousOn χ
  have cl : ContinuousOn (linearSide d) (Icc 0 1) :=
    ((Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by norm_num : 0 ≤ unitExponent)).mul
      (continuous_const.sub continuous_id))).mul_const d).continuousOn
  have cz := normalizedZeros_continuousOn grh hχ
  have cf : ContinuousOn (firstSide a) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn (firstTrivial_continuousOn a)
  have ct := normalizedTail_continuousOn (parityShift_nonneg χ)
  have cont : ContinuousOn F (Icc 0 1) := (((ca.add cl).add cz).add cf).add ct
  apply complex_eq_zero_of_even_moments cont _ x hx
  intro m
  change moment m (arithmeticSide χ + linearSide d + normalizedZeros χ + firstSide a + normalizedTail a) = 0
  rw [moment_add m (((ca.add cl).add cz).add cf) ct, moment_add m ((ca.add cl).add cz) cf,
    moment_add m (ca.add cl) cz, moment_add m ca cl, linear_moment, first_moment (parityShift_cases χ)]
  unfold moment
  rw [arithmeticSide_moment, normalizedZeros_moment grh hχ, normalizedTail_moment (parityShift_nonneg χ)]
  have grid := logDeriv_grid_poles hχ (m+1)
  rw [trivial_grid_split (parityShift_nonneg χ)] at grid
  have same (s : ℂ) (j : ℕ) : s - -(trivialOrder (parityShift χ) j : ℂ) =
      s + (parityShift χ : ℂ) + 2*((j : ℂ)+1) := by
    dsimp only [trivialOrder]; push_cast; ring
  dsimp only [a, d]
  simp_rw [same]
  simp only [div_eq_mul_inv]
  linear_combination -(((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ)+1))⁻¹) * grid

/-- GRH alone bounds every nonprincipal twist in the whole range required by
the finite sieve. -/
theorem grh_twist_envelope (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    (hp : 2791 < p) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    ‖mangoldtTwist χ‖ ≤ twistEnvelope p := by
  have pp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  let y := (p : ℝ)⁻¹
  have y0 : 0 < y := inv_pos.mpr pp
  have y1 : y ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ p by omega))
  have hy : y ∈ Icc (0 : ℝ) 1 := ⟨y0.le, y1⟩
  let v : ℂ := (y^unitExponent : ℝ)
  have vn : v ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos y0 _).ne'
  let d := logDeriv (LFunction χ) bachRightPoint
  let a := parityShift χ
  let Z := ∑' i : LZeros χ, anchoredKernel (zeroValue i) y
  have zz : normalizedZeros χ y = v * Z :=
    tsum_const_smul'' (f := fun i : LZeros χ => anchoredKernel (zeroValue i) y) (y^unitExponent)
  have tt : normalizedTail a y = v * trivialTail a y :=
    tsum_const_smul'' (f := fun j => anchoredKernel (-(trivialOrder a j : ℂ)) y) (y^unitExponent)
  have ar : arithmeticSide χ y = v * mangoldtTwist χ := arithmeticSide_at_reciprocal (by omega) χ
  have eq := normalized_explicit_formula grh hχ y hy
  change arithmeticSide χ y + linearSide d y + normalizedZeros χ y + firstSide a y + normalizedTail a y = 0 at eq
  rw [ar, zz, tt] at eq
  have lc : linearSide d y = v * (((1-y : ℝ) : ℂ)*d) := by dsimp [linearSide, v]; push_cast; ring
  have fc : firstSide a y = v * (firstTrivialKernel a y : ℂ) := by dsimp [firstSide, v]; push_cast; ring
  rw [lc, fc] at eq
  have fact : v * (mangoldtTwist χ + ((1-y : ℝ) : ℂ)*d + Z +
      (firstTrivialKernel a y : ℂ) + trivialTail a y) = 0 := by linear_combination eq
  have raw := (mul_eq_zero.mp fact).resolve_left vn
  have rearr : mangoldtTwist χ =
      -((((1-y : ℝ) : ℂ)*d + Z) + (firstTrivialKernel a y : ℂ) + trivialTail a y) := by
    linear_combination raw
  have hd : ‖((1-y : ℝ) : ℂ)*d‖ ≤ 6 := by
    rw [norm_mul, Complex.norm_of_nonneg (sub_nonneg.mpr y1)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (logDeriv_LFunction_three_halves_le χ)
  have hf : ‖(firstTrivialKernel a y : ℂ)‖ ≤ log p + 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [y, Real.log_inv] using firstTrivial_bound a y0 y1
  have hsmall : y ≤ 2/5 := by
    change (p : ℝ)⁻¹ ≤ 2/5
    rw [← one_div, div_le_iff₀ pp]; linarith [show (3 : ℝ) ≤ p by exact_mod_cast (show 3 ≤ p by omega)]
  have sy : y ^ (-(1/2 : ℝ)) = √(p : ℝ) := by
    rw [Real.sqrt_eq_rpow, show y = (p : ℝ)⁻¹ from rfl, Real.inv_rpow pp.le, Real.rpow_neg pp.le, inv_inv]
  have hl : 0 ≤ log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hz := (grh_anchored_sum_le grh hχ y0.le).2
  rw [sy] at hz
  have hz' : ‖Z‖ ≤ (4/3*√(p : ℝ)+4)*(log p/2+6) :=
    hz.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  rw [rearr, norm_neg]
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hd hz')) hf)) (trivialTail_le (parityShift_nonneg χ) hy)).trans
  unfold twistEnvelope; linarith

/-- The only extra input beyond Dirichlet GRH is a bounded Boolean calculation. -/
theorem erdos_985_of_grh_and_finite (grh : DirichletGRH) (finite : BasicFiniteInput)
    (p : ℕ) (hp : p.Prime) (hne : p ≠ 2) : HasSmallPrimeRoot p :=
  odd_primes_of_twist_envelope finite (fun p prime lower χ nontrivial => by
    let : Fact p.Prime := ⟨prime⟩
    exact grh_twist_envelope grh lower nontrivial) p hp hne

#print axioms normalized_explicit_formula
#print axioms grh_twist_envelope
#print axioms erdos_985_of_grh_and_finite

end JSP818
