import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-! A primitive-root detector for the smoothed Dirichlet character sums of
McGown, Treviño and Trudgian. The mass of the nonprincipal coefficients, after
normalization by the principal coefficient, is at most `2 ^ ω(p - 1) - 1`. -/

noncomputable section

open Finset

namespace JSP818.CharacterSieve

variable {p : ℕ} [Fact p.Prime]

abbrev Character (p : ℕ) := DirichletCharacter ℂ p

/-- A factor of the normalized primitive-root indicator. It vanishes when
the value of the order-`r` character is one. -/
def factor (η : Character p) (r : ℕ) (a : (ZMod p)ˣ) : ℂ :=
  1 - (r - 1 : ℂ)⁻¹ * ∑ j ∈ Ico 1 r, (η ^ j) a

def twist (w : (ZMod p)ˣ → ℂ) (χ : Character p) : ℂ :=
  ∑ a : (ZMod p)ˣ, w a * χ a

private def sift (w : (ZMod p)ˣ → ℂ) (η : ℕ → Character p) (s : Finset ℕ)
    (χ : Character p) : ℂ :=
  ∑ a : (ZMod p)ˣ, w a * χ a * ∏ r ∈ s, factor (η r) r a

private theorem sift_empty (w : (ZMod p)ˣ → ℂ) (η : ℕ → Character p) (χ : Character p) :
    sift w η ∅ χ = twist w χ := by simp [sift, twist]

private theorem sift_insert (w : (ZMod p)ˣ → ℂ) (η : ℕ → Character p) (s : Finset ℕ)
    {r : ℕ} (hr : r ∉ s) (χ : Character p) :
    sift w η (insert r s) χ = sift w η s χ -
      (r - 1 : ℂ)⁻¹ * ∑ j ∈ Ico 1 r, sift w η s (χ * η r ^ j) := by
  classical
  unfold sift
  simp only [prod_insert hr]
  rw [sum_comm (s := Ico 1 r) (t := univ)]
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  rw [factor]
  simp only [MulChar.mul_apply]
  rw [show (∑ j ∈ Ico 1 r, w a * (χ a * (η r ^ j) a) * ∏ k ∈ s, factor (η k) k a) =
      (w a * χ a * ∏ k ∈ s, factor (η k) k a) * ∑ j ∈ Ico 1 r, (η r ^ j) a by
    rw [mul_sum]; apply sum_congr rfl; intros; ring]
  ring

private theorem factor_zero {η : Character p} {r : ℕ} (hr : 1 < r) {a : (ZMod p)ˣ}
    (h : η a = 1) : factor η r a = 0 := by
  have hn : (r : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hr.ne')
  simp only [factor, MulChar.pow_apply_coe, h, one_pow, sum_const, Nat.card_Ico,
    nsmul_eq_mul, mul_one, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega : r ≠ 0)),
    Nat.cast_one, inv_mul_cancel₀ hn, sub_self]

omit [Fact p.Prime] in
private theorem shifted_ne_one {r j d : ℕ} {χ η : Character p} (hη : orderOf η = r)
    (hr : r.Prime) (hj : j ∈ Ico 1 r) (hc : r.Coprime d) (hd : χ ^ d = 1) :
    χ * η ^ j ≠ 1 := by
  intro bad
  have hpow := congrArg (fun z : Character p => z ^ d) bad
  simp only [mul_pow, hd, one_mul, one_pow, ← pow_mul] at hpow
  have hdiv := orderOf_dvd_of_pow_eq_one hpow
  rw [hη] at hdiv
  have : r ∣ j := (hr.dvd_mul.mp hdiv).resolve_right ((Nat.Prime.coprime_iff_not_dvd hr).mp hc)
  exact (Nat.not_dvd_of_pos_of_lt (mem_Ico.mp hj).1 (mem_Ico.mp hj).2) this

/-- The average of the `r-1` nontrivial twists has the same uniform norm bound. -/
private theorem norm_average_le {r : ℕ} (hr : 1 < r) (f : ℕ → ℂ) (b : ℝ)
    (h : ∀ j ∈ Ico 1 r, ‖f j‖ ≤ b) :
    ‖(r - 1 : ℂ)⁻¹ * ∑ j ∈ Ico 1 r, f j‖ ≤ b := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast hr
  have hnr : ‖(r : ℂ) - 1‖ = (r : ℝ) - 1 := by
    rw [show (r : ℂ) - 1 = (((r : ℝ) - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [norm_mul, norm_inv, hnr]
  calc
    _ ≤ ((r : ℝ) - 1)⁻¹ * ∑ j ∈ Ico 1 r, b := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hr'.le))
      exact (norm_sum_le _ _).trans (sum_le_sum h)
    _ = b := by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hr'.ne'), one_mul]

private theorem sift_bounds (w : (ZMod p)ˣ → ℂ) (η : ℕ → Character p) (B : ℝ)
    (hb : ∀ χ : Character p, χ ≠ 1 → ‖twist w χ‖ ≤ B) (s : Finset ℕ)
    (hs : ∀ r ∈ s, r.Prime ∧ orderOf (η r) = r)
    (χ : Character p) (d : ℕ) (hd : χ ^ d = 1) (hc : ∀ r ∈ s, r.Coprime d) :
    (χ ≠ 1 → ‖sift w η s χ‖ ≤ (2 : ℝ) ^ s.card * B) ∧
    (χ = 1 → ‖sift w η s χ - twist w 1‖ ≤ ((2 : ℝ) ^ s.card - 1) * B) := by
  classical
  induction s using Finset.induction_on generalizing χ d with
  | empty =>
    constructor
    · intro h; simpa [sift_empty] using hb χ h
    · rintro rfl; simp [sift_empty]
  | @insert r s hr ih =>
    obtain ⟨hp, ho⟩ := hs r (mem_insert_self ..)
    have small : ∀ l ∈ s, l.Prime ∧ orderOf (η l) = l := fun l hl => hs l (mem_insert_of_mem hl)
    have hc' : ∀ l ∈ s, l.Coprime d := fun l hl => hc l (mem_insert_of_mem hl)
    have old := ih small χ d hd hc'
    let tail := (r - 1 : ℂ)⁻¹ * ∑ j ∈ Ico 1 r, sift w η s (χ * η r ^ j)
    have htail : ‖tail‖ ≤ (2 : ℝ) ^ s.card * B := by
      apply norm_average_le hp.one_lt
      intro j hj
      have hrpow : η r ^ r = 1 := by simpa only [ho] using pow_orderOf_eq_one (η r)
      have hjpow : (η r ^ j) ^ r = 1 := by
        rw [← pow_mul, Nat.mul_comm j r, pow_mul, hrpow, one_pow]
      have hpw : (χ * η r ^ j) ^ (d * r) = 1 := by
        rw [mul_pow, pow_mul χ, hd, one_pow, one_mul, Nat.mul_comm d r,
          pow_mul (η r ^ j), hjpow, one_pow]
      have cop : ∀ l ∈ s, l.Coprime (d * r) := by
        intro l hl
        exact (hc' l hl).mul_right ((Nat.coprime_primes (small l hl).1 hp).2 (by rintro rfl; exact hr hl))
      exact (ih small _ (d * r) hpw cop).1
        (shifted_ne_one ho hp hj (hc r (mem_insert_self ..)) hd)
    have hstep : sift w η (insert r s) χ = sift w η s χ - tail := sift_insert w η s hr χ
    rw [hstep, card_insert_of_notMem hr, pow_succ]
    constructor
    · intro hχ
      exact (norm_sub_le ..).trans ((add_le_add (old.1 hχ) htail).trans_eq (by ring))
    · intro hχ
      rw [show sift w η s χ - tail - twist w 1 = (sift w η s χ - twist w 1) - tail by ring]
      exact (norm_sub_le ..).trans ((add_le_add (old.2 hχ) htail).trans_eq (by ring))

/-- If the principal mass exceeds `2^ω - 1` times the largest nonprincipal
twist, a unit of maximal order has nonzero weight. -/
theorem exists_generator_of_twists (w : (ZMod p)ˣ → ℂ) (B : ℝ)
    (hb : ∀ χ : Character p, χ ≠ 1 → ‖twist w χ‖ ≤ B)
    (main : ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B < ‖twist w 1‖) :
    ∃ a : (ZMod p)ˣ, w a ≠ 0 ∧ orderOf (a : ZMod p) = p - 1 := by
  classical
  have hp : p.Prime := Fact.out
  let m := p - 1
  have hm : 0 < m := Nat.sub_pos_of_lt hp.one_lt
  have hcyc : IsCyclic (Character p) :=
    (DirichletCharacter.mulEquiv_units ℂ p).some.isCyclic.mpr inferInstance
  obtain ⟨ξ, hξ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p, Nat.totient_prime hp] at hξ
  change orderOf ξ = m at hξ
  let η (r : ℕ) := ξ ^ (m / r)
  have hs (r : ℕ) (hr : r ∈ m.primeFactors) : r.Prime ∧ orderOf (η r) = r := by
    obtain ⟨prime, dvd, _⟩ := Nat.mem_primeFactors.mp hr
    refine ⟨prime, ?_⟩
    dsimp [η]
    rw [← hξ] at dvd ⊢
    exact orderOf_pow_orderOf_div (hξ.trans_ne hm.ne') dvd
  have bound := (sift_bounds w η B hb m.primeFactors hs 1 1 (by simp) (by simp)).2 rfl
  have hn : sift w η m.primeFactors 1 ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at bound
    exact main.not_ge bound
  by_contra no
  apply hn
  unfold sift
  apply sum_eq_zero
  intro a _
  by_cases hw : w a = 0
  · simp [hw]
  have miss : ¬∀ r : ℕ, r.Prime → r ∣ m → (a : ZMod p) ^ (m / r) ≠ 1 := by
    intro all
    exact no ⟨a, hw, orderOf_eq_of_pow_and_pow_div_prime hm (ZMod.pow_card_sub_one_eq_one a.ne_zero) all⟩
  push_neg at miss
  obtain ⟨r, hr, hd, heq⟩ := miss
  have hv : η r a = 1 := by
    change (ξ ^ (m / r)) (a : ZMod p) = 1
    rw [MulChar.pow_apply_coe, ← map_pow, heq, map_one]
  rw [prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hr, hd, hm.ne'⟩) (factor_zero hr.one_lt hv), mul_zero]

end JSP818.CharacterSieve
