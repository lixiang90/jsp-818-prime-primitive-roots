import ArithmeticMoments
import SpecialMoments

noncomputable section

namespace JSP818

open Real MeasureTheory Set

/-- The pole of parity zero or one collides with a smoothing pole. -/
def firstTrivialKernel (a x : ℝ) : ℝ :=
  if a = 0 then -log x - 5/3*(1-x) else 3/5*(1-x) + x*log x

theorem firstTrivial_bound (a : ℝ) {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    |firstTrivialKernel a x| ≤ -log x+2 := by
  have hl := Real.log_nonpos h0.le h1
  have hxl := mul_nonneg h0.le (neg_nonneg.mpr hl)
  have hxl' := mul_nonneg (sub_nonneg.mpr h1) (neg_nonneg.mpr hl)
  unfold firstTrivialKernel
  split <;> apply abs_le.mpr <;> constructor <;> nlinarith

theorem firstTrivial_continuousOn (a : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ unitExponent * firstTrivialKernel a x) (Icc 0 1) := by
  have hlog := continuousOn_rpow_mul_log (by norm_num : 0 < unitExponent)
  have hw : ContinuousOn (fun x : ℝ => x^unitExponent * (1-x)) (Icc 0 1) :=
    ((Real.continuous_rpow_const (by norm_num : 0 ≤ unitExponent)).mul (continuous_const.sub continuous_id)).continuousOn
  by_cases h : a = 0
  · apply (hlog.neg.sub (hw.const_mul (5/3 : ℝ))).congr
    intro x _; simp only [firstTrivialKernel, if_pos h, Pi.sub_apply, Pi.neg_apply]; ring
  · apply ((hw.const_mul (3/5 : ℝ)).add (continuousOn_id.mul hlog)).congr
    intro x _; simp only [firstTrivialKernel, if_neg h, Pi.add_apply, Pi.mul_apply, id_eq]; ring

theorem unit_weight_moment {s : ℝ} (hs : 1 < s) :
    (∫ x : ℝ in 0..1, x^(s-1)*(1-x)) = (s*(s+1))⁻¹ := by
  have eq : (∫ x : ℝ in 0..1, x^(s-1)*(1-x)) =
      ∫ x : ℝ in 0..1, x^(s-1)*cutoffWeight 1 x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp [cutoffWeight, max_eq_left (sub_nonneg.mpr hx.2)]
  rw [eq, cutoff_moment hs (by decide : 0 < 1)]
  simp

theorem firstTrivial_moment {s a : ℝ} (hs : 1 < s) (ha : a = 0 ∨ a = 1) :
    (∫ x : ℝ in 0..1, x^(s-1)*firstTrivialKernel a x) =
      ((s+a)⁻¹-(3/2+a)⁻¹)/(s*(s+1)) := by
  let W (x : ℝ) := x^(s-1)*(1-x)
  have wi : IntervalIntegrable W volume 0 1 :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ s-1)).mul
      (continuous_const.sub continuous_id)).intervalIntegrable ..
  have we : (∫ x in (0 : ℝ)..1, W x) = (s*(s+1))⁻¹ := unit_weight_moment hs
  have sn : s ≠ 0 := by linarith
  have s1 : s+1 ≠ 0 := by linarith
  rcases ha with rfl | rfl
  · let L (x : ℝ) := x^(s-1)*log x
    have li : IntervalIntegrable L volume 0 1 :=
      (continuousOn_rpow_mul_log (by linarith : 0 < s-1)).intervalIntegrable_of_Icc zero_le_one
    have eq : (∫ x : ℝ in 0..1, x^(s-1)*firstTrivialKernel 0 x) =
        ∫ x : ℝ in 0..1, (-1)*L x - (5/3)*W x := by
      apply intervalIntegral.integral_congr; intro x _; simp [L, W, firstTrivialKernel] <;> ring
    rw [eq, intervalIntegral.integral_sub (li.const_mul (-1 : ℝ)) (wi.const_mul (5/3 : ℝ)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, we, show (∫ x : ℝ in 0..1, L x) = -(1/s^2) from integral_rpow_log_unit hs]
    simp only [add_zero]
    field_simp [sn, s1]; ring
  · let L (x : ℝ) := x^s*log x
    have li : IntervalIntegrable L volume 0 1 :=
      (continuousOn_rpow_mul_log (by linarith : 0 < s)).intervalIntegrable_of_Icc zero_le_one
    have leq := integral_rpow_log_unit (s := s+1) (by linarith)
    simp only [add_sub_cancel_right] at leq
    have eq : (∫ x : ℝ in 0..1, x^(s-1)*firstTrivialKernel 1 x) =
        ∫ x : ℝ in 0..1, (3/5)*W x + L x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x; intro hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have pw : x^(s-1)*x = x^s := by
        rw [← Real.rpow_add_one hx.1.ne']; congr 1; ring
      simp only [firstTrivialKernel, if_neg (one_ne_zero : (1 : ℝ) ≠ 0), W, L]
      linear_combination pw * log x
    rw [eq, intervalIntegral.integral_add (wi.const_mul _) li, intervalIntegral.integral_const_mul, we,
      show (∫ x : ℝ in 0..1, L x) = -(1/(s+1)^2) from leq]
    field_simp [sn, s1]; ring

theorem normalizedReal_moment (m : ℕ) (f : ℝ → ℝ) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • ((x ^ unitExponent * f x : ℝ) : ℂ)) =
      ((∫ x : ℝ in 0..1, x ^ (mellinPoint (m+1)-1) * f x : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x; intro hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  rw [Complex.real_smul, ← Complex.ofReal_mul, ← mul_assoc, grid_power m hx.1]

#print axioms firstTrivial_moment

end JSP818
