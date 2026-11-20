import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.Finite.Basic

/-! Two unconditional families for the same target as Erdős problem 985. -/

namespace JSP818

/-- If a residue represented by a positive integer escapes a power equation,
at least one prime factor of the representative escapes it as well. -/
private theorem prime_factor_escapes (p e : ℕ) : ∀ m : ℕ, m ≠ 0 → (m : ZMod p) ^ e ≠ 1 →
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ (q : ZMod p) ^ e ≠ 1 := by
  apply Nat.recOnMul
  · simp
  · simp
  · intro q hq _ h
    exact ⟨q, hq, dvd_rfl, h⟩
  · intro a b ha hb hab he
    by_cases h : (a : ZMod p) ^ e = 1
    · have ht : (b : ZMod p) ^ e ≠ 1 := by
        intro hv
        exact he (by rw [Nat.cast_mul, mul_pow, h, hv, one_mul])
      obtain ⟨q, hp, hd, hq⟩ := hb (right_ne_zero_of_mul hab) ht
      exact ⟨q, hp, dvd_mul_of_dvd_right hd a, hq⟩
    · obtain ⟨q, hp, hd, hq⟩ := ha (left_ne_zero_of_mul hab) h
      exact ⟨q, hp, dvd_mul_of_dvd_left hd b, hq⟩

/-- Every proper positive exponent below p-1 misses some prime below p.
This is weaker than requiring a single prime to miss *all* proper divisors. -/
theorem prime_escapes_exponent {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hlt : e < p - 1) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ (q : ZMod p) ^ e ≠ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc : e < Nat.card (ZMod p)ˣ := by simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hlt
  obtain ⟨a, hpow⟩ := exists_pow_ne_one_of_isCyclic he.ne' hc
  let m := (a : ZMod p).val
  have hm : (m : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
  have hm0 : m ≠ 0 := by intro h; apply a.ne_zero; rw [← hm, h]; simp
  have hme : (m : ZMod p) ^ e ≠ 1 := by
    rw [hm]
    intro h
    apply hpow
    exact Units.ext (by simpa using h)
  obtain ⟨q, hq, hd, hz⟩ := prime_factor_escapes p e m hm0 hme
  exact ⟨q, hq, (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd).trans_lt (ZMod.val_lt _), hz⟩

/-- An unconditional class of odd prime moduli, with no size cutoff.
For a prime-power group order it suffices to test the single maximal proper divisor. -/
theorem prime_power_predecessor {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (horder : p - 1 = r ^ (k + 1)) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have he : 0 < r ^ k := pow_pos hr.pos _
  have hlt : r ^ k < p - 1 := by
    rw [horder, pow_succ]
    simpa using (mul_lt_mul_of_pos_left hr.one_lt he)
  obtain ⟨q, hq, hqp, hz⟩ := prime_escapes_exponent hp he hlt
  have hn : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hqp.not_ge (Nat.le_of_dvd hq.pos hd)
  refine ⟨q, hq, hqp, orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one hn) ?_⟩
  intro s hs hd
  rw [horder] at hd ⊢
  have hs' : s = r := (Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow hd)
  subst s
  simpa [pow_succ, hr.pos] using hz

/-- If p=2r+1 with r prime, a prime escaping the exponent r also escapes
the exponent 2. The only square roots of one are ±1, and p−1=2r is composite. -/
theorem safe_prime_modulus {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (horder : p - 1 = 2 * r) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlt : r < p - 1 := by rw [horder]; have := hr.pos; omega
  obtain ⟨q, hq, hqp, hes⟩ := prime_escapes_exponent hp hr.pos hlt
  have hn : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hqp.not_ge (Nat.le_of_dvd hq.pos hd)
  have noSquare : (q : ZMod p) ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with he | he
    · have he' := (ZMod.natCast_eq_natCast_iff' q 1 p).1 (by simpa using he)
      rw [Nat.mod_eq_of_lt hqp, Nat.mod_eq_of_lt hp.one_lt] at he'
      exact hq.ne_one he'
    · have hz : ((q+1 : ℕ) : ZMod p) = 0 := by push_cast; rw [he]; simp
      have hd := (ZMod.natCast_eq_zero_iff _ _).1 hz
      have hb := Nat.le_of_dvd (Nat.succ_pos q) hd
      have hcomp : ¬ (2 * r).Prime := Nat.not_prime_mul (by decide) hr.ne_one
      exact hcomp ((show q = 2 * r by omega) ▸ hq)
  refine ⟨q, hq, hqp, orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one hn) ?_⟩
  intro s hs hd
  rw [horder] at hd ⊢
  rcases hs.dvd_mul.mp hd with htwo | hr'
  · have he := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp htwo
    simpa [he] using hes
  · have he := (Nat.prime_dvd_prime_iff_eq hs hr).mp hr'
    simpa [he, hr.pos] using noSquare

#print axioms prime_escapes_exponent
#print axioms prime_power_predecessor
#print axioms safe_prime_modulus

end JSP818
