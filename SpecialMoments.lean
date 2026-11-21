import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

namespace JSP818

open Set MeasureTheory Real

/-- Multiplication by a positive power removes the endpoint singularity of log. -/
theorem continuousOn_rpow_mul_log {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun x : ℝ => x ^ r * log x) (Icc 0 1) := by
  have h := ((Real.continuous_mul_log.comp (Real.continuous_rpow_const hr.le)).div_const r).continuousOn
    (s := Icc (0 : ℝ) 1)
  apply h.congr
  intro x hx
  change x ^ r * log x = (x ^ r * log (x ^ r)) / r
  rcases eq_or_lt_of_le hx.1 with he | hp
  · subst x; simp [Real.zero_rpow hr.ne']
  · rw [Real.log_rpow hp, eq_div_iff hr.ne']
    ring

/-- Logarithmic moment at the first repeated pole of the smoothing kernel. -/
theorem integral_rpow_log_unit {s : ℝ} (hs : 1 < s) :
    (∫ x : ℝ in 0..1, x ^ (s - 1) * log x) = -(1 / s ^ 2) := by
  have sp : 0 < s := by linarith
  let F (x : ℝ) := x ^ s * log x / s - x ^ s / s ^ 2
  have cont : ContinuousOn F (Icc 0 1) :=
    ((continuousOn_rpow_mul_log sp).div_const s).sub
      ((Real.continuous_rpow_const sp.le).continuousOn.div_const _)
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (x ^ (s - 1) * log x) x := by
    have X := Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.1.ne')
    have H := (((X.mul (Real.hasDerivAt_log hx.1.ne')).div_const s).sub (X.div_const (s ^ 2)))
    convert H using 1
    rw [show x ^ s = x ^ (s - 1) * x by rw [← Real.rpow_add_one hx.1.ne', sub_add_cancel]]
    field_simp [hx.1.ne', sp.ne']
    ring
  have ident := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one cont hd
    ((continuousOn_rpow_mul_log (by linarith : 0 < s-1)).intervalIntegrable_of_Icc zero_le_one)
  simpa [F, Real.zero_rpow sp.ne'] using ident

#print axioms integral_rpow_log_unit

end JSP818
