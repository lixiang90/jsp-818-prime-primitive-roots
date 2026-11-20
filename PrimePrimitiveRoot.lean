import ElementaryFamilies
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! The odd-prime version of Erdős #985 (JSP-000818).
The analytic large-prime estimate is McGown–Treviño–Trudgian, Theorem 1.
It enters only as an explicit argument of the final assembly lemma. -/

namespace JSP818

/-- Matches the right-of-half-plane statement in Alpöge's Statements.lean. -/
def DirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def HasSmallPrimeRoot (p : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

private def candidates : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53]

private def witnessTest (p q : ℕ) : Bool :=
  decide q.Prime && decide (q < p) && decide (q ^ (p - 1) % p = 1) &&
    (List.range 54).all (fun d =>
      decide ((2 ≤ d → (p - 1) % d = 0 → q ^ ((p - 1) / d) % p ≠ 1) ∧
        (0 < d → d < p - 1 → (p - 1) % d = 0 → q ^ d % p ≠ 1)))

private def passesSieve (p : ℕ) : Bool :=
  (List.range 54).all (fun d => decide (2 ≤ d → d < p → p % d ≠ 0))

private theorem prime_passesSieve {p : ℕ} (hp : p.Prime) : passesSieve p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  intro hlo hhi hmod
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

private def modulusTest (p : ℕ) : Bool :=
  if 2 < p ∧ passesSieve p = true then candidates.any (witnessTest p) else true

private theorem power_eq_one_iff (p q e : ℕ) (hp : 1 < p) :
    (q : ZMod p) ^ e = 1 ↔ q ^ e % p = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff]
  change q ^ e % p = 1 % p ↔ q ^ e % p = 1
  rw [Nat.mod_eq_of_lt hp]

private theorem witnessTest_sound {p q : ℕ} (hp : 2 < p) (hmax : p ≤ 2791)
    (h : witnessTest p q = true) :
    q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  simp only [witnessTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hq, hlt⟩, hpow⟩, hfactors⟩ := h
  have hp' : 1 < p := by omega
  refine ⟨hq, hlt, orderOf_eq_of_pow_and_pow_div_prime (by omega)
    ((power_eq_one_iff _ _ _ hp').2 hpow) ?_⟩
  intro r hr hd heq
  have hz := (power_eq_one_iff _ _ _ hp').1 heq
  by_cases hs : r < 54
  · exact (hfactors r (List.mem_range.mpr hs)).1 hr.two_le (Nat.mod_eq_zero_of_dvd hd) hz
  · -- In this range either a divisor or its complementary divisor is below 54.
    have hco : (p - 1) / r < 54 := (Nat.div_lt_iff_lt_mul hr.pos).2 (by omega)
    have hrle := Nat.le_of_dvd (by omega : 0 < p - 1) hd
    exact (hfactors _ (List.mem_range.mpr hco)).2 (Nat.div_pos hrle hr.pos)
      (Nat.div_lt_self (by omega) hr.one_lt)
      (Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd hd)) hz

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem finite_check : (List.range 2792).all modulusTest = true := by decide +kernel

theorem finite_range {p : ℕ} (hp : p.Prime) (hodd : 2 < p) (hmax : p ≤ 2791) :
    HasSmallPrimeRoot p := by
  have h := List.all_eq_true.mp finite_check p (List.mem_range.mpr (by omega))
  rw [modulusTest, if_pos ⟨hodd, prime_passesSieve hp⟩, List.any_eq_true] at h
  obtain ⟨q, _, hq⟩ := h
  exact ⟨q, witnessTest_sound hodd hmax hq⟩

theorem two_exception : ¬ HasSmallPrimeRoot 2 := by
  rintro ⟨q, hq, hlt, _⟩
  exact (Nat.not_lt_of_ge hq.two_le) hlt

/-- The witness form of Theorem 1 of McGown, Treviño and Trudgian.
Its analytic derivation from Dirichlet GRH is external to this repository. -/
def McGownTrevinoTrudgianBound : Prop :=
  ∀ p : ℕ, p.Prime → 2791 < p →
    ∃ q : ℕ, q.Prime ∧ orderOf (q : ZMod p) = p - 1 ∧ (q : ℝ) < Real.sqrt p - 2

theorem odd_primes_of_mcgown_trevino_trudgian
    (large : McGownTrevinoTrudgianBound)
    (p : ℕ) (hp : p.Prime) (hne : p ≠ 2) : HasSmallPrimeRoot p := by
  by_cases h : p ≤ 2791
  · exact finite_range hp (lt_of_le_of_ne hp.two_le (Ne.symm hne)) h
  · obtain ⟨q, hq, hord, hbound⟩ := large p hp (lt_of_not_ge h)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hs : Real.sqrt (p : ℝ) ≤ p := by
      apply (Real.sqrt_le_iff).2
      exact ⟨by positivity, by nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (Nat.cast_nonneg (α := ℝ) p)]⟩
    refine ⟨q, hq, ?_, hord⟩
    exact_mod_cast (show (q : ℝ) < p by linarith)

/-- The published GRH implication is an explicit, unformalized argument. -/
theorem erdos_985 (grh : DirichletGRH)
    (theorem_one : DirichletGRH → McGownTrevinoTrudgianBound) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  odd_primes_of_mcgown_trevino_trudgian (theorem_one grh)

#print axioms finite_range
#print axioms two_exception
#print axioms odd_primes_of_mcgown_trevino_trudgian
#print axioms erdos_985

end JSP818
