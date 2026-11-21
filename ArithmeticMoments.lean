import GridFormula
import UnitMoments
import SmoothedSums

noncomputable section

namespace JSP818

open MeasureTheory Set Real ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-- The normalization makes each arithmetic term continuous up to zero, with
a summable uniform majorant from the absolutely convergent Dirichlet series. -/
def arithmeticTerm {p : ℕ} (χ : DirichletCharacter ℂ p) (n : ℕ) (x : ℝ) : ℂ :=
  ((x ^ unitExponent * cutoffWeight n x : ℝ) : ℂ) * (↗χ * ↗Λ) n

def arithmeticSide {p : ℕ} (χ : DirichletCharacter ℂ p) (x : ℝ) : ℂ :=
  ∑' n, arithmeticTerm χ n x

private theorem arithmeticTerm_cont {p : ℕ} (χ : DirichletCharacter ℂ p) (n : ℕ) :
    Continuous (arithmeticTerm χ n) :=
  (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by norm_num : 0 ≤ unitExponent)).mul
    (cutoffWeight_continuous n))).mul continuous_const

private theorem arithmeticTerm_bound {p : ℕ} (χ : DirichletCharacter ℂ p) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖arithmeticTerm χ n x‖ ≤ ‖LSeries.term (↗χ * ↗Λ) (unitExponent : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n; simp [arithmeticTerm]
  have hp : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hw : 0 ≤ cutoffWeight n x := le_max_right _ _
  have cutoff : cutoffWeight n x ≤ 1 := by
    unfold cutoffWeight
    exact max_le (by nlinarith [mul_nonneg hp.le hx.1]) zero_le_one
  rw [arithmeticTerm, norm_mul, Complex.norm_of_nonneg (mul_nonneg (rpow_nonneg hx.1 _) hw),
    LSeries.norm_term_eq, ite_eq_right hn, Complex.ofReal_re]
  by_cases hlo : 1 ≤ (n : ℝ) * x
  · rw [show cutoffWeight n x = 0 from max_eq_right (by linarith)]
    simp only [mul_zero, zero_mul]
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hp.le _)
  have hle : x ≤ (n : ℝ)⁻¹ := by
    rw [← one_div, le_div_iff₀ hp]
    linarith [mul_comm x (n : ℝ)]
  have hpow := Real.rpow_le_rpow hx.1 hle (by norm_num : 0 ≤ unitExponent)
  rw [Real.inv_rpow hp.le] at hpow
  rw [div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_of_le_one_right (rpow_nonneg hx.1 _) cutoff).trans hpow

theorem arithmeticSide_continuousOn {p : ℕ} (χ : DirichletCharacter ℂ p) :
    ContinuousOn (arithmeticSide χ) (Icc 0 1) :=
  continuousOn_tsum (fun n => (arithmeticTerm_cont χ n).continuousOn)
    ((LSeriesSummable_twist_vonMangoldt χ (by norm_num : 1 < (unitExponent : ℂ).re)).norm)
    (fun n _ hx => arithmeticTerm_bound χ n hx)

theorem grid_power (m : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ (2*m) * x ^ unitExponent = x ^ (mellinPoint (m+1) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hx]
  congr 1
  dsimp [unitExponent, mellinPoint]
  push_cast
  ring

private theorem term_moment {p : ℕ} (χ : DirichletCharacter ℂ p) (m n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • arithmeticTerm χ n x) =
      LSeries.term (↗χ * ↗Λ) (mellinPoint (m+1) : ℂ) n /
        ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ) + 1)) := by
  let s := mellinPoint (m+1)
  have hs : 1 < s := by dsimp [s, mellinPoint]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  by_cases hn : n = 0
  · subst n; simp [arithmeticTerm]
  have hp : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have eq : (∫ x : ℝ in 0..1, x ^ (2*m) • arithmeticTerm χ n x) =
      ∫ x : ℝ in 0..1, ((x ^ (s-1) * cutoffWeight n x : ℝ) : ℂ) * (↗χ * ↗Λ) n := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x
    intro hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [arithmeticTerm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      ← mul_assoc, grid_power m hx.1]
  rw [eq, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    cutoff_moment hs (Nat.pos_of_ne_zero hn)]
  simp only [LSeries.term, ite_eq_right hn]
  have pwr : (n : ℂ) ^ (s : ℂ) = ((n : ℝ)^s : ℝ) := by
    simpa using (Complex.ofReal_cpow hp.le s).symm
  change _ = ((↗χ * ↗Λ) n / (n : ℂ) ^ (s : ℂ)) / ((s : ℂ) * ((s : ℂ)+1))
  rw [pwr, Real.inv_rpow hp.le]
  push_cast
  ring

theorem arithmeticSide_moment {p : ℕ} [NeZero p] (χ : DirichletCharacter ℂ p) (m : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (2*m) • arithmeticSide χ x) =
      -logDeriv (LFunction χ) (mellinPoint (m+1) : ℂ) /
        ((mellinPoint (m+1) : ℂ) * ((mellinPoint (m+1) : ℂ) + 1)) := by
  let s := (mellinPoint (m+1) : ℂ)
  have hs : 1 < s.re := by dsimp [s, mellinPoint]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  have sm := (LSeriesSummable_twist_vonMangoldt χ
    (by norm_num : 1 < (unitExponent : ℂ).re)).norm
  have eq := unit_hasSum_integral
    (F := fun n x => x ^ (2*m) • arithmeticTerm χ n x)
    (fun n => ((continuous_id.pow (2*m)).smul (arithmeticTerm_cont χ n)).continuousOn) sm
    (fun n x hx => by
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx.1 _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hx.1 hx.2)).trans
        (arithmeticTerm_bound χ n hx))
  simp_rw [term_moment] at eq
  have e : LSeries (↗χ * ↗Λ) s = -logDeriv (LFunction χ) s := by
    rw [LSeries_twist_vonMangoldt_eq χ hs, logDeriv_apply, deriv_LFunction_eq_deriv_LSeries χ hs,
      LFunction_eq_LSeries χ hs]; ring
  rw [show -logDeriv (LFunction χ) (mellinPoint (m+1) : ℂ) = LSeries (↗χ * ↗Λ) s from e.symm,
    LSeries, ← tsum_div_const, eq.tsum_eq]
  apply intervalIntegral.integral_congr
  intro x _
  exact (tsum_const_smul'' (f := fun n => arithmeticTerm χ n x) (x ^ (2*m))).symm

/-- At the reciprocal modulus the arithmetic function is exactly the finite
smoothed twist in the primitive-root sieve, up to the positive normalization. -/
theorem arithmeticSide_at_reciprocal {p : ℕ} (hp : 0 < p) (χ : DirichletCharacter ℂ p) :
    arithmeticSide χ (p : ℝ)⁻¹ =
      ((p : ℝ)⁻¹ ^ unitExponent) • CharacterSieve.mangoldtTwist χ := by
  have pp : 0 < (p : ℝ) := by exact_mod_cast hp
  have outside (n : ℕ) (hn : n ∉ Finset.Ico 1 p) : arithmeticTerm χ n (p : ℝ)⁻¹ = 0 := by
    by_cases hz : n = 0
    · subst n; simp [arithmeticTerm]
    have hle : p ≤ n := by simp only [Finset.mem_Ico] at hn; omega
    have h : 1 ≤ (n : ℝ) * (p : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ pp, one_mul]
      exact_mod_cast hle
    simp [arithmeticTerm, cutoffWeight, max_eq_right (sub_nonpos.mpr h)]
  rw [arithmeticSide, tsum_eq_sum outside, CharacterSieve.mangoldtTwist, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : (n : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Ico.mp hn).2.le
  have h : (n : ℝ) * (p : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one pp]; exact hnR
  simp only [arithmeticTerm, cutoffWeight, max_eq_left (sub_nonneg.mpr h),
    CharacterSieve.mangoldtWeight, Complex.real_smul, Pi.mul_apply, div_eq_mul_inv]
  push_cast
  ring

#print axioms arithmeticSide_continuousOn
#print axioms arithmeticSide_moment
#print axioms arithmeticSide_at_reciprocal

end JSP818
