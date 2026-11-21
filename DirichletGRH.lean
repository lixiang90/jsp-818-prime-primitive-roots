import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic

namespace JSP818

/-- The right-of-half-plane statement in Alpöge's `Statements.lean`. -/
def DirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

open DirichletCharacter

theorem primitive_of_prime_modulus {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · have : NeZero p := ⟨hp.ne_zero⟩
    exact (hχ (eq_one_iff_conductor_eq_one.mpr h)).elim
  · exact h

/-- GRH and the functional equation put every zero of a completed,
nonprincipal character of prime modulus on the critical line. This includes
characters with nonreal values. -/
theorem completed_zero_on_line (grh : DirichletGRH) {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) {s : ℂ}
    (hzero : completedLFunction χ s = 0) : s.re = 1 / 2 := by
  have hp : p.Prime := Fact.out
  have right (η : DirichletCharacter ℂ p) (hne : η ≠ 1) (z : ℂ) (hz : 1 / 2 < z.re) :
      completedLFunction η z ≠ 0 := by
    intro he
    apply grh p η z hz (Or.inl hne)
    rw [LFunction_eq_completed_div_gammaFactor η z (Or.inr hp.ne_one), he, zero_div]
  apply le_antisymm (le_of_not_gt (fun h => right χ hχ s h hzero))
  by_contra! h
  have hi : χ⁻¹ ≠ 1 := by simpa only [ne_eq, inv_eq_one] using hχ
  have hright : 1 / 2 < (1 - s : ℂ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  apply right χ⁻¹ hi (1 - s) hright
  rw [(primitive_of_prime_modulus hp hi).completedLFunction_one_sub, inv_inv, hzero, mul_zero]

#print axioms completed_zero_on_line

end JSP818
