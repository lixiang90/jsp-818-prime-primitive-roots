import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

namespace JSP818

open MeasureTheory Set
open scoped Polynomial

/-- On the positive unit interval, moments of even degree determine a continuous
function. Approximate the function composed with square root by a polynomial. -/
theorem eq_zero_of_even_moments {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (mom : ∀ n : ℕ, (∫ x : ℝ in 0..1, f x * x ^ (2 * n)) = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
  have cont (P : ℝ[X]) : ContinuousOn (fun x : ℝ => f x * P.eval (x ^ 2)) (Icc 0 1) :=
    hf.mul ((P.continuous.comp (continuous_id.pow 2)).continuousOn)
  have poly (P : ℝ[X]) : (∫ x : ℝ in 0..1, f x * P.eval (x ^ 2)) = 0 := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simp_rw [Polynomial.eval_add, mul_add]
      rw [intervalIntegral.integral_add ((cont P).intervalIntegrable_of_Icc zero_le_one)
        ((cont Q).intervalIntegrable_of_Icc zero_le_one), hP, hQ, add_zero]
    | monomial n a =>
      simp_rw [Polynomial.eval_monomial, ← pow_mul,
        show ∀ x : ℝ, f x * (a * x ^ (2 * n)) = (f x * x ^ (2 * n)) * a by intro x; ring]
      rw [intervalIntegral.integral_mul_const, mom, zero_mul]
  let I := ∫ x : ℝ in 0..1, f x ^ 2
  let M := ∫ x : ℝ in 0..1, |f x|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg zero_le_one (fun x _ => abs_nonneg _)
  intro y hy
  by_contra yn
  have pos : 0 < I := intervalIntegral.integral_pos zero_lt_one (hf.pow 2)
    (fun _ _ => sq_nonneg _) ⟨y, hy, sq_pos_of_ne_zero yn⟩
  let ε := I / (M + 1)
  have epos : 0 < ε := div_pos pos (by linarith)
  have comp : ContinuousOn (fun u => f (Real.sqrt u)) (Icc 0 1) :=
    hf.comp Real.continuous_sqrt.continuousOn (fun x hx =>
      ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one.mpr hx.2)⟩)
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 _ comp ε epos
  have le : I ≤ ∫ x : ℝ in 0..1, (f x * P.eval (x ^ 2) + ε * |f x|) := by
    apply intervalIntegral.integral_mono_on zero_le_one ((hf.pow 2).intervalIntegrable_of_Icc zero_le_one)
      (((cont P).add (continuousOn_const.mul hf.abs)).intervalIntegrable_of_Icc zero_le_one)
    intro x hx
    have hx' : x ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, pow_le_one₀ hx.1 hx.2⟩
    have h := hP (x ^ 2) hx'
    rw [Real.sqrt_sq hx.1, abs_sub_comm] at h
    have main := (le_abs_self (f x * (f x - P.eval (x ^ 2)))).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h.le (abs_nonneg _) :
        |f x * (f x - P.eval (x ^ 2))| ≤ |f x| * ε)
    change f x ^ 2 ≤ f x * P.eval (x ^ 2) + ε * |f x|
    nlinarith
  have ei : IntervalIntegrable (fun x : ℝ => ε * |f x|) volume 0 1 :=
    ((continuousOn_const.mul hf.abs).intervalIntegrable_of_Icc zero_le_one)
  rw [intervalIntegral.integral_add ((cont P).intervalIntegrable_of_Icc zero_le_one) ei,
    poly, zero_add, intervalIntegral.integral_const_mul] at le
  have heq : ε * (M + 1) = I := div_mul_cancel₀ _ (by linarith)
  change I ≤ ε * M at le
  nlinarith

#print axioms eq_zero_of_even_moments

theorem complex_eq_zero_of_even_moments {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    (mom : ∀ n : ℕ, (∫ x : ℝ in 0..1, x ^ (2 * n) • f x) = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
  have test (L : ℂ →L[ℝ] ℝ) : ∀ x ∈ Icc (0 : ℝ) 1, L (f x) = 0 := by
    apply eq_zero_of_even_moments (L.continuous.comp_continuousOn hf)
    intro n
    have hi : IntervalIntegrable (fun x : ℝ => x ^ (2 * n) • f x) volume 0 1 :=
      (((continuous_id.pow (2 * n)).continuousOn.smul hf).intervalIntegrable_of_Icc zero_le_one)
    have h := L.intervalIntegral_comp_comm hi
    rw [mom, map_zero] at h
    change (∫ x : ℝ in 0..1, L (x ^ (2 * n) • f x)) = 0 at h
    simpa only [Function.comp_apply, map_smul, smul_eq_mul, mul_comm] using h
  intro x hx
  exact Complex.ext (test Complex.reCLM x hx) (test Complex.imCLM x hx)

#print axioms complex_eq_zero_of_even_moments

end JSP818
