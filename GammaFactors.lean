import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic

noncomputable section

namespace JSP818

open Complex DirichletCharacter

/-- The tangent slope of log Gamma is bounded by the secant slope from x to x+1. -/
theorem digamma_re_le_log {x : ℝ} (hx : 0 < x) :
    (digamma (x : ℂ)).re ≤ Real.log x := by
  have hz : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have hm := congrArg Complex.re h
    simp only [ofReal_re, neg_re, natCast_re] at hm
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hd : HasDerivAt Real.Gamma (deriv Gamma (x : ℂ)).re x :=
    (differentiableAt_Gamma _ hz).hasDerivAt.real_of_complex
  have gp := Real.Gamma_pos_of_pos hx
  have hl : HasDerivAt (Real.log ∘ Real.Gamma)
      ((deriv Gamma (x : ℂ)).re / Real.Gamma x) x := hd.log gp.ne'
  have le := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt
    (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (show 0 < x + 1 by positivity))
    (show x < x + 1 by linarith) hl
  rw [slope_def_field] at le
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' gp.ne'] at le
  rw [digamma_def, logDeriv_apply, Gamma_ofReal, div_ofReal_re]
  convert le using 1; ring

/-- Exact logarithmic derivative of Deligne's real-place gamma factor. -/
theorem logDeriv_gammaR {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = (digamma (s / 2) - Complex.log (Real.pi : ℂ)) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have halfpos : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  have halfreg (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
    intro h
    rw [h] at halfpos
    simp only [neg_re, natCast_re] at halfpos
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s :=
    ((hasDerivAt_id' s).neg.div_const (2 : ℂ)).const_cpow (.inl hπ)
  have pow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hπ)
  have hg : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
    (differentiableAt_Gamma _ halfreg).comp s ((differentiableAt_id).div_const _)
  rw [show Gammaℝ = (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) by rfl,
    logDeriv_fun_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Gamma (z / 2)) s pow_ne (Gamma_ne_zero halfreg) hd.differentiableAt hg,
    ((hasDerivAt_id' s).div_const (2 : ℂ)).logDeriv_Gamma halfreg,
    logDeriv_apply, hd.deriv]
  field_simp [pow_ne]
  ring

/-- Both parities have a nonpositive archimedean contribution at 3/2. -/
theorem gammaR_logDeriv_re_nonpos {x : ℝ} (hx : 0 < x) (hπ : x / 2 ≤ Real.pi) :
    (logDeriv Gammaℝ (x : ℂ)).re ≤ 0 := by
  rw [logDeriv_gammaR (by simpa using hx), div_ofNat_re, sub_re,
    ← ofReal_log Real.pi_pos.le, ofReal_re, ← ofReal_ofNat, ← ofReal_div]
  have h := (digamma_re_le_log (x := x / 2) (by positivity)).trans
    (Real.log_le_log (by positivity) hπ)
  linarith

#print axioms gammaR_logDeriv_re_nonpos

end JSP818
