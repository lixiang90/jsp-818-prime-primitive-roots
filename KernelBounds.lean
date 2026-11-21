import MellinKernel

noncomputable section

namespace JSP818

private theorem distance_bounds {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    0 < ‖bachRightPoint - ρ‖ ∧ ‖bachRightPoint - ρ‖ ≤ 2 * ‖ρ‖ ∧
    ‖bachRightPoint - ρ‖ ≤ ‖ρ + 1‖ := by
  have hd : ‖bachRightPoint - ρ‖ ^ 2 = 1 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [bachRightPoint, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hr]
    ring
  have h0 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr]; ring
  have h1 : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, hr]; ring
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg ρ.im, norm_nonneg (bachRightPoint - ρ)]
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith [sq_nonneg ρ.im]
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith

/-- All three terms of the anchored pole kernel decay quadratically in the
ordinate. This is also uniform in the character when the zero lies on the line. -/
theorem anchoredKernel_le {ρ : ℂ} (hr : ρ.re = 1 / 2) {y : ℝ} (hy : 0 ≤ y) :
    ‖anchoredKernel ρ y‖ ≤ (4 / 3 * y ^ (-(1 / 2 : ℝ)) + 3 + 5 / 2 * y) /
      Complex.normSq (bachRightPoint - ρ) := by
  let d := ‖bachRightPoint - ρ‖
  obtain ⟨hd, hr0, hr1⟩ := distance_bounds hr
  have hs : 0 < d := hd
  have h0 : 0 < ‖ρ‖ := by linarith
  have h1 : 0 < ‖ρ + 1‖ := lt_of_lt_of_le hd hr1
  have c : ‖bachRightPoint / (ρ * (bachRightPoint - ρ))‖ ≤ 3 / d ^ 2 := by
    rw [norm_div, norm_mul, show ‖bachRightPoint‖ = 3 / 2 by norm_num [bachRightPoint]]
    apply (div_le_div_iff₀ (mul_pos h0 hd) (sq_pos_of_pos hs)).mpr
    change (3 / 2 : ℝ) * d ^ 2 ≤ 3 * (‖ρ‖ * d)
    nlinarith [mul_le_mul_of_nonneg_right (show d ≤ 2 * ‖ρ‖ from hr0) hs.le]
  have c' : ‖(bachRightPoint + 1) / ((ρ + 1) * (bachRightPoint - ρ))‖ ≤ (5 / 2) / d ^ 2 := by
    rw [norm_div, norm_mul, show ‖bachRightPoint + 1‖ = 5 / 2 by
      rw [show bachRightPoint + 1 = ((5 / 2 : ℝ) : ℂ) by norm_num [bachRightPoint]]
      norm_num]
    apply (div_le_div_iff₀ (mul_pos h1 hd) (sq_pos_of_pos hs)).mpr
    change (5 / 2 : ℝ) * d ^ 2 ≤ (5 / 2) * (‖ρ + 1‖ * d)
    nlinarith [mul_le_mul_of_nonneg_right (show d ≤ ‖ρ + 1‖ from hr1) hs.le]
  have k := smoothed_zero_kernel_le hr
  rw [Complex.normSq_eq_norm_sq] at k ⊢
  change ‖(ρ * (ρ + 1))⁻¹‖ ≤ (4 / 3) / d ^ 2 at k
  have py : ‖(y : ℂ) ^ (-ρ)‖ = y ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_nonneg hy (by rw [Complex.neg_re, hr]; norm_num),
      Complex.neg_re, hr]
  calc
    ‖anchoredKernel ρ y‖ ≤
        ‖(y : ℂ) ^ (-ρ) * (ρ * (ρ + 1))⁻¹‖ + ‖bachRightPoint / (ρ * (bachRightPoint - ρ))‖ +
        ‖(y : ℂ) * ((bachRightPoint + 1) / ((ρ + 1) * (bachRightPoint - ρ)))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ y ^ (-(1 / 2 : ℝ)) * ((4 / 3) / d ^ 2) + 3 / d ^ 2 + y * ((5 / 2) / d ^ 2) := by
      rw [norm_mul, py, norm_mul, Complex.norm_of_nonneg hy]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left k (Real.rpow_nonneg hy _)) c)
        (mul_le_mul_of_nonneg_left c' hy)
    _ = _ := by dsimp [d]; ring

#print axioms anchoredKernel_le

end JSP818
