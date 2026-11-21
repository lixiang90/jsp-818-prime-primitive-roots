import PrimePrimitiveRoot
import FiniteWitness
import SizeBound
import EulerBound

noncomputable section

namespace JSP818

open Real CharacterSieve

/-- The analytic target from the anchored explicit formula, with a convenient
upper bound for its lower order terms. -/
def twistEnvelope (p : ℕ) : ℝ :=
  (2 / 3 * log p + 8) * √(p : ℝ) + 3 * log p + 37

/-- A decidable statement at one modulus using the canonical factorization.
The basic sieve run attains 193 as the largest least witness. -/
def finiteModulusCheck (p : ℕ) : Bool :=
  (List.range 194).any (fun q => rootCertificate p q (p - 1).primeFactorsList)

/-- An exact finite input; it contains only natural-number arithmetic and
the explicitly bounded witness search above. -/
def BasicFiniteInput : Prop :=
  ∀ p : ℕ, p.Prime → 2791 < p → p < 2 ^ 36 →
    25 * p ≤ ((150 + 7 * (p.log2 + 1)) * (2 ^ (p - 1).primeFactors.card - 1)) ^ 2 →
    finiteModulusCheck p = true

private theorem fourth_root_id {p : ℕ} (hp : 0 < p) :
    ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = p ∧ ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √(p : ℝ) := by
  have h : (0 : ℝ) ≤ p := by positivity
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h, Real.sqrt_eq_rpow]; norm_num

theorem envelope_le_dyadic {p : ℕ} (hp : 2791 < p) :
    twistEnvelope p ≤ (7 * (p.log2 + 1 : ℕ) / 15 + 10 : ℝ) * √(p : ℝ) := by
  have hpos : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  let u := (p : ℝ) ^ (1 / 4 : ℝ)
  have hu : 0 ≤ u := Real.rpow_nonneg hpos.le _
  obtain ⟨up, us⟩ := fourth_root_id (p := p) (by omega)
  change u ^ 4 = _ at up
  change u ^ 2 = _ at us
  have h7 : 7 ≤ u := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hu (by decide : (4 : ℕ) ≠ 0)
    rw [up] at hh
    norm_num at hh
    omega
  have hl : log p ≤ 3 / 2 * u := log_le_three_halves_fourth_root hpos
  have err : 3 * log p + 37 ≤ 2 * √(p : ℝ) := by
    rw [← us]
    nlinarith [mul_nonneg (sub_nonneg.mpr h7) (show 0 ≤ u + 7 by linarith)]
  have hb : (p : ℝ) < 2 ^ (p.log2 + 1) := by exact_mod_cast (Nat.lt_log2_self (n := p))
  have hb' := Real.log_lt_log hpos hb
  rw [Real.log_pow] at hb'
  have hcoeff : (2 / 3 : ℝ) * log p ≤ 7 * (p.log2 + 1 : ℕ) / 15 := by
    have h2 := mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 7 / 10 by linarith [log_two_lt_d9])
      (Nat.cast_nonneg (α := ℝ) (p.log2 + 1))
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg (p : ℝ))
  unfold twistEnvelope
  linarith

theorem envelope_le_large {p : ℕ} (hp : 2 ^ 36 ≤ p) :
    twistEnvelope p ≤ √(p : ℝ) * log p := by
  have hR : (2 : ℝ) ^ 36 ≤ p := by exact_mod_cast hp
  have hpos : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hR
  let u := (p : ℝ) ^ (1 / 4 : ℝ)
  have hu : 0 ≤ u := Real.rpow_nonneg hpos.le _
  obtain ⟨up, us⟩ := fourth_root_id (p := p) (by omega)
  change u ^ 4 = _ at up
  change u ^ 2 = _ at us
  have h32 : 32 ≤ u := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hu (by decide : (4 : ℕ) ≠ 0)
    rw [up] at hh
    norm_num at hR hh
    linarith
  have hl : log p ≤ 3 / 2 * u := log_le_three_halves_fourth_root hpos
  have err : 3 * log p + 37 ≤ √(p : ℝ) / 4 := by
    rw [← us]
    nlinarith [mul_nonneg (sub_nonneg.mpr h32) (show 0 ≤ u + 14 by linarith)]
  have low := Real.log_le_log (by norm_num : 0 < (2 : ℝ)^36) hR
  rw [Real.log_pow] at low
  norm_num only [Nat.cast_ofNat] at low
  have hh : (2 / 3 : ℝ) * log p + 8 + 1 / 4 ≤ log p := by linarith [log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg (p : ℝ))
  unfold twistEnvelope
  linarith

/-- An explicit twist bound suffices outside the precisely specified finite
residual set. The theorem takes the analytic and finite inputs separately. -/
theorem odd_primes_of_twist_envelope (finite : BasicFiniteInput)
    (analytic : ∀ (p : ℕ), p.Prime → 2791 < p →
      ∀ χ : Character p, χ ≠ 1 → ‖mangoldtTwist χ‖ ≤ twistEnvelope p)
    (p : ℕ) (hp : p.Prime) (hne : p ≠ 2) : HasSmallPrimeRoot p := by
  by_cases small : p ≤ 2791
  · exact finite_range hp (lt_of_le_of_ne hp.two_le hne.symm) small
  have hl : 2791 < p := by omega
  let : Fact p.Prime := ⟨hp⟩
  by_cases large : 2 ^ 36 ≤ p
  · exact prime_root_of_large_twist_bound large
      (fun χ hχ => (analytic p hp hl χ hχ).trans (envelope_le_large large))
  let b := p.log2 + 1
  let c := 2 ^ (p - 1).primeFactors.card - 1
  by_cases residual : 25 * p ≤ ((150 + 7 * b) * c) ^ 2
  · obtain ⟨q, _, ok⟩ := List.any_eq_true.mp (finite p hp hl (by omega) residual)
    exact ⟨q, rootCertificate_sound hp (by omega) ok⟩
  have cs : (c : ℝ) = (2 : ℝ) ^ (p - 1).primeFactors.card - 1 := by
    dsimp [c]
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
  have comp : (((150 + 7 * (b : ℝ)) * c) ^ 2) < 25 * (p : ℝ) := by
    exact_mod_cast (lt_of_not_ge residual)
  have sqr := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hroot := Real.sqrt_pos.mpr (show 0 < (p : ℝ) by exact_mod_cast hp.pos)
  have scaled : (150 + 7 * (b : ℝ)) * c < 5 * √(p : ℝ) := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    nlinarith
  have prod := mul_lt_mul_of_pos_right scaled hroot
  apply prime_primitive_root_of_mangoldtTwists _ (analytic p hp hl)
  apply lt_of_lt_of_le _ (principal_mass_ge_third (by omega : 1024 ≤ p))
  rw [← cs]
  have mulB := mul_le_mul_of_nonneg_left (envelope_le_dyadic hl) (Nat.cast_nonneg (α := ℝ) c)
  change _ ≤ (c : ℝ) * ((7 * (b : ℝ) / 15 + 10) * √(p : ℝ)) at mulB
  exact lt_of_le_of_lt mulB (by nlinarith)

#print axioms odd_primes_of_twist_envelope

end JSP818
