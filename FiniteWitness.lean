import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.NormNum.Prime

namespace JSP818

/-- Binary modular exponentiation with a structural bit budget. -/
def squareAndMultiply (p a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % p
  | bits + 1, e =>
    if e = 0 then 1 % p else
      let t := squareAndMultiply p a bits (e / 2)
      let u := t ^ 2 % p
      if e % 2 = 0 then u else u * a % p

theorem squareAndMultiply_eq (p a bits e : ℕ) (he : e < 2 ^ bits) :
    squareAndMultiply p a bits e = a ^ e % p := by
  induction bits generalizing e with
  | zero =>
    have : e = 0 := by simpa using he
    simp [this, squareAndMultiply]
  | succ bits ih =>
    have half : e / 2 < 2 ^ bits := (Nat.div_lt_iff_lt_mul (by decide)).mpr
      (by simpa only [pow_succ] using he)
    by_cases h : e = 0
    · simp [h, squareAndMultiply]
    simp only [squareAndMultiply, ite_eq_right h, ih _ half, sq,
      Nat.mod_mul_mod, Nat.mul_mod_mod]
    split
    · rename_i even
      have decomp : e / 2 * 2 = e := by omega
      rw [← sq, ← pow_mul, decomp]
    · rename_i odd
      have decomp : e / 2 * 2 + 1 = e := by omega
      rw [← sq, ← pow_mul, ← pow_succ, decomp]

private theorem prime_mem_of_dvd_list {r : ℕ} (hr : r.Prime) (factors : List ℕ)
    (hs : ∀ d ∈ factors, d.Prime) (hd : r ∣ factors.prod) : r ∈ factors := by
  induction factors with
  | nil => simp [hr.not_dvd_one] at hd
  | cons d ds ih =>
    rcases hr.dvd_mul.mp (show r ∣ d * ds.prod from hd) with h | h
    · have eq := (Nat.prime_dvd_prime_iff_eq hr (hs d (by simp))).mp h
      simp [eq]
    · exact List.mem_cons_of_mem _ (ih (fun t ht => hs t (by simp [ht])) h)

/-- Square-root trial division keeps the kernel work for testing witness primes
and factors small. The moduli themselves are assumed prime by the target. -/
def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt + 1)).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

theorem trialPrime_sound {n : ℕ} (h : trialPrime n = true) : n.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, ?_⟩
  intro d low upper dvd
  exact ((h.2 d (by omega)).resolve_left (by omega)) (Nat.mod_eq_zero_of_dvd dvd)

/-- The product contains the full factorization with multiplicities. The
Fermat condition follows from primality of the modulus. -/
def rootCertificate (p q : ℕ) (factors : List ℕ) : Bool :=
  decide (q < p ∧ factors.prod = p - 1) && trialPrime q &&
  factors.all (fun r => trialPrime r && squareAndMultiply p q 36 ((p - 1) / r) != 1)

theorem rootCertificate_sound {p q : ℕ} (hp : p.Prime) (hu : p ≤ 2 ^ 36)
    {factors : List ℕ} (ok : rootCertificate p q factors = true) :
    q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  simp only [rootCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne] at ok
  obtain ⟨⟨⟨hq, prod⟩, q_ok⟩, each⟩ := ok
  have prime := trialPrime_sound q_ok
  have : Fact p.Prime := ⟨hp⟩
  have qnz : (q : ZMod p) ≠ 0 := by
    intro zero
    have z := (ZMod.val_eq_zero _).mpr zero
    rw [ZMod.val_natCast_of_lt hq] at z
    exact prime.ne_zero z
  refine ⟨prime, hq, orderOf_eq_of_pow_and_pow_div_prime (Nat.sub_pos_of_lt hp.one_lt)
    (ZMod.pow_card_sub_one_eq_one qnz) ?_⟩
  intro r hr hd hz
  have mem := prime_mem_of_dvd_list hr factors (fun d h => trialPrime_sound (each d h).1) (prod ▸ hd)
  have rhs := (each r mem).2
  have bound : (p - 1) / r < 2 ^ 36 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [squareAndMultiply_eq _ _ _ _ bound] at rhs
  apply rhs
  rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff] at hz
  exact Eq.trans hz (Nat.mod_eq_of_lt hp.one_lt)

/-- Bounded Boolean test on the canonical prime factorization. -/
def finiteModulusCheck (p : ℕ) : Bool :=
  (List.range 194).any (fun q => rootCertificate p q (p - 1).primeFactorsList)

/-- A certificate supplies the result of the bounded search without requiring
the kernel to enumerate candidates or refactor the predecessor. -/
theorem finiteModulusCheck_of_certificate {p q : ℕ} {factors : List ℕ}
    (hq : q < 194) (ok : rootCertificate p q factors = true) : finiteModulusCheck p = true := by
  simp only [rootCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨lt, prod⟩, prime⟩, tests⟩ := ok
  have perm := Nat.primeFactorsList_unique prod (fun r h => trialPrime_sound (tests r h).1)
  apply List.any_eq_true.mpr
  refine ⟨q, List.mem_range.mpr hq, ?_⟩
  simp only [rootCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨lt, perm.prod_eq.symm.trans prod⟩, prime⟩, fun r h => tests r (perm.mem_iff.mpr h)⟩

/-- The largest residual modulus in the refined search has eight distinct
prime factors in its predecessor. The kernel can check this case directly. -/
theorem witness_13123111 : orderOf (19 : ZMod 13123111) = 13123110 := by
  have h := rootCertificate_sound (p := 13123111) (q := 19)
    (factors := [2, 3, 5, 7, 11, 13, 19, 23]) (by norm_num1) (by decide) (by decide +kernel)
  exact h.2.2

#print axioms rootCertificate_sound
#print axioms finiteModulusCheck_of_certificate
#print axioms witness_13123111

end JSP818
