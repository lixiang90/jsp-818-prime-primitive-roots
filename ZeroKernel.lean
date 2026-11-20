import DirichletGRH

/-! Compare the zero kernel for the linearly smoothed von Mangoldt sum with
the real part of a difference of logarithmic derivatives at `3/2` and `-1/2`.
The comparison is pointwise and applies with analytic multiplicities. -/

noncomputable section

namespace JSP818

/-- The point of absolute convergence used to bound the completed logarithmic derivative. -/
abbrev bachRightPoint : ℂ := ((3 / 2 : ℝ) : ℂ)
/-- The reflection of `bachRightPoint` across the critical line. -/
abbrev bachLeftPoint : ℂ := ((-(1 / 2) : ℝ) : ℂ)

theorem reflected_pole_difference {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ((bachRightPoint - ρ)⁻¹ - (bachLeftPoint - ρ)⁻¹).re = 2 / Complex.normSq (bachRightPoint - ρ) := by
  simp only [Complex.sub_re, Complex.inv_re, Complex.normSq_apply, Complex.sub_im,
    bachRightPoint, bachLeftPoint, Complex.ofReal_re, Complex.ofReal_im, h]
  ring_nf

theorem smoothed_zero_kernel_le {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ‖(ρ * (ρ + 1))⁻¹‖ ≤ (4 / 3) / Complex.normSq (bachRightPoint - ρ) := by
  have hbase : Complex.normSq (bachRightPoint - ρ) = 1 + ρ.im ^ 2 := by
    simp only [bachRightPoint, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, h]; ring
  have ha : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h]; ring
  have hb : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, h]; ring
  have ap : 0 < ‖ρ‖ := by nlinarith [norm_nonneg ρ, sq_nonneg ρ.im]
  have bp : 0 < ‖ρ + 1‖ := by nlinarith [norm_nonneg (ρ + 1), sq_nonneg ρ.im]
  have hsq : (3 * (1 + ρ.im ^ 2)) ^ 2 ≤ (4 * ‖ρ‖ * ‖ρ + 1‖) ^ 2 := by
    rw [show (4 * ‖ρ‖ * ‖ρ + 1‖) ^ 2 = 16 * ‖ρ‖ ^ 2 * ‖ρ + 1‖ ^ 2 by ring, ha, hb]
    nlinarith [sq_nonneg ρ.im, sq_nonneg (ρ.im ^ 2)]
  have hh := (sq_le_sq₀ (by positivity : 0 ≤ 3 * (1 + ρ.im ^ 2)) (by positivity)).1 hsq
  rw [norm_inv, norm_mul, hbase, ← one_div]
  apply (div_le_div_iff₀ (mul_pos ap bp) (by positivity)).2
  linarith

/-- The contribution is bounded by `2/3` times the reflected sum. This
separates the elementary kernel calculation from the Hadamard formula. -/
theorem sum_smoothed_zero_kernel_le {ι : Type*} (zero : ι → ℂ)
    (onLine : ∀ i, (zero i).re = 1 / 2) {T : ℝ}
    (poles : HasSum (fun i => ((bachRightPoint - zero i)⁻¹ - (bachLeftPoint - zero i)⁻¹).re) T) :
    Summable (fun i => ‖(zero i * (zero i + 1))⁻¹‖) ∧
    ∑' i, ‖(zero i * (zero i + 1))⁻¹‖ ≤ (2 / 3) * T := by
  have rhs := poles.mul_left (2 / 3 : ℝ)
  have le (i : ι) : ‖(zero i * (zero i + 1))⁻¹‖ ≤
      2 / 3 * ((bachRightPoint - zero i)⁻¹ - (bachLeftPoint - zero i)⁻¹).re := by
    rw [reflected_pole_difference (onLine i)]
    convert smoothed_zero_kernel_le (onLine i) using 1; ring
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) le rhs.summable
  exact ⟨hs, (hs.tsum_le_tsum le rhs.summable).trans_eq rhs.tsum_eq⟩

end JSP818
