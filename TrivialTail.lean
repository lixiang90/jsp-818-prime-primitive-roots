import PoleMoments

noncomputable section

namespace JSP818

open Filter Set Real MeasureTheory
open scoped Topology

def trivialOrder (a : ℝ) (j : ℕ) : ℝ := a + 2 * ((j : ℝ) + 1)

def tailMajorant (j : ℕ) : ℝ := 5 * (((j : ℝ)+1)⁻¹ - ((j : ℝ)+2)⁻¹)

theorem hasSum_tailMajorant : HasSum tailMajorant 5 := by
  let f (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹
  have anti : Antitone f := by
    intro i j hij; apply inv_anti₀ (by positivity : 0 < (i : ℝ) + 1); exact_mod_cast (Nat.add_le_add_right hij 1)
  have lim : Tendsto f atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h := (hasSum_shift_difference f anti lim 1).mul_left (5 : ℝ)
  convert h using 1
  · ext j; dsimp [tailMajorant, f]; push_cast; ring_nf
  · simp [f]

private theorem anchored_negative_real {x k : ℝ} (hk : 2 ≤ k) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖anchoredKernel (-(k : ℂ)) x‖ ≤ 5 / (k*(k-1)) := by
  have k0 : 0 < k := by linarith
  have k1 : 0 < k-1 := by linarith
  have d0 : 0 < k*(k-1) := mul_pos k0 k1
  have hn : ‖-(k : ℂ)‖ = k := by rw [norm_neg, Complex.norm_of_nonneg k0.le]
  have hn1 : ‖-(k : ℂ) + 1‖ = k-1 := by
    rw [show -(k : ℂ) + 1 = ((1-k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hnd : ‖bachRightPoint - -(k : ℂ)‖ = 3/2+k := by
    rw [show bachRightPoint - -(k : ℂ) = ((3/2+k : ℝ) : ℂ) by dsimp [bachRightPoint]; push_cast; ring,
      Complex.norm_of_nonneg (by linarith)]
  have hxk : ‖(x : ℂ) ^ (- -(k : ℂ))‖ ≤ 1 := by
    rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_nonneg hx.1 (by simpa using k0.ne'), Complex.ofReal_re]
    exact Real.rpow_le_one hx.1 hx.2 k0.le
  have bnorm : ‖bachRightPoint‖ = 3/2 := by norm_num [bachRightPoint]
  have b1norm : ‖bachRightPoint+1‖ = 5/2 := by
    rw [show bachRightPoint + 1 = ((5 / 2 : ℝ) : ℂ) by norm_num [bachRightPoint]]
    norm_num
  apply ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))).trans
  simp only [norm_mul, norm_inv, norm_div, hn, hn1, hnd, Complex.norm_of_nonneg hx.1, bnorm, b1norm]
  have h0 := mul_le_mul_of_nonneg_right hxk (inv_nonneg.mpr d0.le)
  have h1 := div_le_div_of_nonneg_left (by norm_num : 0 ≤ (3/2 : ℝ)) d0
    (mul_le_mul_of_nonneg_left (show k-1 ≤ 3/2+k by linarith) k0.le)
  have h2 := div_le_div_of_nonneg_left (by norm_num : 0 ≤ (5/2 : ℝ)) d0
    (show k*(k-1) ≤ (k-1)*(3/2+k) by nlinarith)
  have hx0 : 0 ≤ (5/2 : ℝ) / ((k-1)*(3/2+k)) := by positivity
  have hx2 := (mul_le_of_le_one_left hx0 hx.2).trans h2
  simp only [div_eq_mul_inv, one_mul] at h0 h1 hx2 ⊢
  linarith

theorem trivialTail_bound {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    ‖anchoredKernel (-(trivialOrder a j : ℂ)) x‖ ≤ tailMajorant j := by
  let k := trivialOrder a j
  have j0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : 2 ≤ k := by dsimp [k, trivialOrder]; linarith
  apply (anchored_negative_real hk hx).trans
  have hk' : ((j : ℝ)+1)*((j : ℝ)+2) ≤ k*(k-1) := by
    rw [mul_comm k]
    apply mul_le_mul <;> try dsimp [k, trivialOrder]
    all_goals nlinarith
  have h := div_le_div_of_nonneg_left (by norm_num : 0 ≤ (5 : ℝ)) (by positivity) hk'
  apply h.trans_eq
  unfold tailMajorant
  field_simp [show (j : ℝ)+1 ≠ 0 by positivity, show (j : ℝ)+2 ≠ 0 by positivity]
  ring

def trivialTail (a x : ℝ) : ℂ := ∑' j : ℕ, anchoredKernel (-(trivialOrder a j : ℂ)) x

theorem trivialTail_le {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (0 : ℝ) 1) : ‖trivialTail a x‖ ≤ 5 := by
  have sm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (trivialTail_bound ha hx)
    hasSum_tailMajorant.summable
  exact (norm_tsum_le_tsum_norm sm).trans
    ((sm.tsum_le_tsum (trivialTail_bound ha hx) hasSum_tailMajorant.summable).trans_eq hasSum_tailMajorant.tsum_eq)

def normalizedTail (a x : ℝ) : ℂ := ∑' j : ℕ, normalizedKernel (-(trivialOrder a j : ℂ)) x

private theorem trivial_re {a : ℝ} (ha : 0 ≤ a) (j : ℕ) : (-(trivialOrder a j : ℂ)).re ≤ -2 := by
  simp only [Complex.neg_re, Complex.ofReal_re, trivialOrder]
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem norm_trivial_normalized {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    ‖normalizedKernel (-(trivialOrder a j : ℂ)) x‖ ≤ tailMajorant j := by
  rw [normalizedKernel, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hx.1 _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one hx.1 hx.2 (by norm_num))).trans
    (trivialTail_bound ha hx j)

theorem normalizedTail_continuousOn {a : ℝ} (ha : 0 ≤ a) : ContinuousOn (normalizedTail a) (Icc 0 1) :=
  continuousOn_tsum (fun j => normalizedKernel_continuousOn ((trivial_re ha j).trans_lt (by norm_num)))
    hasSum_tailMajorant.summable (fun j _ hx => norm_trivial_normalized ha hx j)

theorem normalizedTail_moment {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • normalizedTail a x) =
      (∑' j : ℕ, (((mellinPoint (m+1) : ℂ) - -(trivialOrder a j : ℂ))⁻¹ -
        (bachRightPoint - -(trivialOrder a j : ℂ))⁻¹)) /
        ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ) + 1)) := by
  have he (j : ℕ) := (trivial_re ha j).trans_lt (show (-2 : ℝ) < unitExponent by norm_num)
  have eq := unit_hasSum_integral
    (F := fun j x => x^(2*m) • normalizedKernel (-(trivialOrder a j : ℂ)) x)
    (fun j => (continuous_id.pow (2*m)).continuousOn.smul (normalizedKernel_continuousOn (he j)))
    hasSum_tailMajorant.summable (fun j x hx => by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx.1 _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hx.1 hx.2)).trans
        (norm_trivial_normalized ha hx j))
  have term (j : ℕ) := normalizedKernel_moment m (he j)
    (by intro bad; have h := trivial_re ha j; rw [bad] at h; norm_num at h)
    (by intro bad; have h := congrArg Complex.re bad
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h; linarith [trivial_re ha j])
    (by intro bad; have h := congrArg Complex.re bad
        simp only [Complex.sub_re, bachRightPoint, Complex.ofReal_re, Complex.zero_re] at h; linarith [trivial_re ha j])
  simp_rw [term] at eq
  rw [← tsum_div_const, eq.tsum_eq]
  apply intervalIntegral.integral_congr
  intro x _
  exact (tsum_const_smul'' (f := fun j => normalizedKernel (-(trivialOrder a j : ℂ)) x)
    (x^(2*m))).symm

#print axioms trivialTail_le
#print axioms normalizedTail_moment

end JSP818
