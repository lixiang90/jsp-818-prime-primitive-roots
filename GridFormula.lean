import ZeroMassBound

/-! On a grid with step two, the gamma factor gives a telescoping series over
the trivial zeros. This identifies the moments for Mellin inversion using only
the gamma recurrence and the Hadamard expansion. -/

noncomputable section

namespace JSP818

open Complex DirichletCharacter Filter Finset OAI.SiegelZeros.WeightedTorusJets
open scoped Topology

def mellinPoint (m : ℕ) : ℝ := 3 / 2 + 2 * m

theorem hasSum_shift_difference (f : ℕ → ℝ) (anti : Antitone f)
    (lim : Tendsto f atTop (𝓝 0)) (m : ℕ) :
    HasSum (fun j => f j - f (j + m)) (∑ k ∈ range m, f k) := by
  have step (k : ℕ) : HasSum (fun j => f (j + k) - f ((j + 1) + k)) (f k) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => sub_nonneg.mpr (anti (by omega))) _).mpr
    simp_rw [sum_range_sub' (fun j => f (j + k))]
    simpa using (tendsto_const_nhds (x := f k)).sub (lim.comp (tendsto_add_atTop_nat k))
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := ih.add (step m)
    convert h using 1
    ext j
    simp [Nat.add_assoc, Nat.add_comm 1 m]

private def trivialDifference (a : ℝ) (m j : ℕ) : ℂ :=
  ((mellinPoint m : ℂ) + a + 2 * j)⁻¹ - (bachRightPoint + a + 2 * j)⁻¹

private theorem trivial_poles_sum {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    HasSum (trivialDifference a m)
      (-(∑ k ∈ range m, (bachRightPoint + a + 2 * (k : ℂ))⁻¹)) := by
  let f (j : ℕ) : ℝ := (3 / 2 + a + 2 * (j : ℝ))⁻¹
  have anti : Antitone f := by
    intro i j hij
    change (3 / 2 + a + 2 * (j : ℝ))⁻¹ ≤ (3 / 2 + a + 2 * (i : ℝ))⁻¹
    apply inv_anti₀ (by positivity)
    gcongr
  have positive : Tendsto (fun j : ℕ => 2 * (j : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
  have lim : Tendsto f atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (3 / 2 + a) positive)
  have h := (Complex.hasSum_ofReal.mpr (hasSum_shift_difference f anti lim m)).neg
  convert h using 1
  · ext j
    dsimp [trivialDifference, mellinPoint, bachRightPoint, f]
    push_cast
    ring_nf
  · dsimp [f, bachRightPoint]
    push_cast
    ring_nf

private theorem gamma_grid_difference {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    logDeriv Gammaℝ ((mellinPoint m : ℂ) + a) - logDeriv Gammaℝ (bachRightPoint + a) =
      ∑ k ∈ range m, (bachRightPoint + a + 2 * (k : ℂ))⁻¹ := by
  let t := bachRightPoint + (a : ℂ)
  have hp : 0 < t.re := by dsimp [t, bachRightPoint]; linarith
  have hq : 0 < ((mellinPoint m : ℂ) + a).re := by
    simp [mellinPoint]
    positivity
  have hz (j : ℕ) : t / 2 ≠ -(j : ℂ) := by
    intro h
    have e := congrArg Complex.re h
    simp only [div_ofNat_re, neg_re, natCast_re] at e
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have shift : ((mellinPoint m : ℂ) + a) / 2 = t / 2 + m := by
    dsimp [t, mellinPoint, bachRightPoint]
    push_cast
    ring
  rw [logDeriv_gammaR hq, logDeriv_gammaR hp, shift, digamma_apply_add_nat hz]
  have hm : ∑ k ∈ range m, (t / 2 + (k : ℂ))⁻¹ =
      2 * ∑ k ∈ range m, (t + 2 * (k : ℂ))⁻¹ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [show t / 2 + (k : ℂ) = (t + 2 * k) / 2 by ring, inv_div, div_eq_mul_inv]
  rw [hm]
  dsimp only [t]
  ring

/-- Isolate the first trivial pole so its logarithmic smoothing term is
handled separately from the absolutely summable tail. -/
theorem trivial_grid_split {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (∑' j : ℕ, (((mellinPoint m : ℂ) + a + 2*j)⁻¹ - (bachRightPoint + a + 2*j)⁻¹)) =
      (((mellinPoint m : ℂ) + a)⁻¹ - (bachRightPoint + a)⁻¹) +
      ∑' j : ℕ, (((mellinPoint m : ℂ) + a + 2*((j : ℂ)+1))⁻¹ -
        (bachRightPoint + a + 2*((j : ℂ)+1))⁻¹) := by
  have h := ((trivial_poles_sum ha m).summable.sum_add_tsum_nat_add 1).symm
  simpa [trivialDifference] using h

private theorem grid_conductor_ne {p : ℕ} [NeZero p] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) {z : ℂ} (hz : 1 ≤ z.re) : conductorCompletedL χ z ≠ 0 :=
  fun h => completedL_ne_zero_of_one_le_re χ hχ hz ((conductorCompletedL_zero_iff _ _).mp h)

/-- The Euler logarithmic derivative is the sum of the two series of pole
differences. The unknown Hadamard constant and the logarithm of the conductor
cancel. This identity is unconditional for every nonprincipal prime-modulus character. -/
theorem logDeriv_grid_poles {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (m : ℕ) :
    logDeriv (LFunction χ) (mellinPoint m : ℂ) - logDeriv (LFunction χ) bachRightPoint =
      (∑' i : LZeros χ, (((mellinPoint m : ℂ) - zeroValue (χ := χ) i)⁻¹ -
        (bachRightPoint - zeroValue (χ := χ) i)⁻¹)) +
        ∑' j : ℕ, (((mellinPoint m : ℂ) + (parityShift χ : ℂ) + 2 * j)⁻¹ -
                   (bachRightPoint + (parityShift χ : ℂ) + 2 * j)⁻¹) := by
  have ha := parityShift_nonneg χ
  have hs : 1 < ((mellinPoint m : ℝ) : ℂ).re := by simp [mellinPoint]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : 1 < bachRightPoint.re := by norm_num [bachRightPoint]
  have hn := (hasSum_anchored_poles hχ (grid_conductor_ne hχ hs.le) (grid_conductor_ne hχ hb.le)).tsum_eq
  have ht := (trivial_poles_sum ha m).tsum_eq
  unfold trivialDifference at ht
  rw [hn, ht, completed_logDeriv_factors hχ hs,
    completed_logDeriv_factors hχ hb, ← gamma_grid_difference ha m]
  ring

#print axioms logDeriv_grid_poles

end JSP818
