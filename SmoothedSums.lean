import CharacterSieve

/-! Transfer the finite-group character sieve to Bach's smoothed von Mangoldt
sum at `x = p`, the strict cutoff required by Erdős 985. -/

noncomputable section

open Finset

namespace JSP818.CharacterSieve

def mangoldtWeight (p n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (1 - (n : ℝ) / p)

def mangoldtTwist {p : ℕ} (χ : Character p) : ℂ :=
  ∑ n ∈ Ico 1 p, (mangoldtWeight p n : ℂ) * χ (n : ZMod p)

variable {p : ℕ} [Fact p.Prime]

private def unitValEquiv : (ZMod p)ˣ ≃ ↥(Ico 1 p) where
  toFun a := ⟨(a : ZMod p).val, mem_Ico.mpr ⟨ZMod.val_pos.mpr a.ne_zero, ZMod.val_lt _⟩⟩
  invFun n := Units.mk0 (n.val : ZMod p) (by
    have hn := mem_Ico.mp n.property
    rintro h
    have := (ZMod.val_eq_zero _).mpr h
    rw [ZMod.val_natCast_of_lt hn.2] at this
    omega)
  left_inv a := Units.ext (ZMod.natCast_zmod_val _)
  right_inv n := Subtype.ext (ZMod.val_natCast_of_lt (mem_Ico.mp n.property).2)

private theorem twist_eq_mangoldtTwist (χ : Character p) :
    twist (fun a : (ZMod p)ˣ => (mangoldtWeight p (a : ZMod p).val : ℂ)) χ = mangoldtTwist χ := by
  classical
  let e : (ZMod p)ˣ ≃ ↥(Ico 1 p) := unitValEquiv
  let f (n : ↥(Ico 1 p)) := (mangoldtWeight p n.val : ℂ) * χ (n.val : ZMod p)
  calc
    _ = ∑ a : (ZMod p)ˣ, f (e a) := by simp [twist, f, e, unitValEquiv]
    _ = ∑ n : ↥(Ico 1 p), f n := e.sum_comp f
    _ = mangoldtTwist χ := (Ico 1 p).sum_coe_sort
      (fun n : ℕ => (mangoldtWeight p n : ℂ) * χ (n : ZMod p))

/-- At the principal character the sum is exactly the ordinary smoothed mass. -/
theorem mangoldtTwist_one : mangoldtTwist (1 : Character p) =
    (∑ n ∈ Ico 1 p, mangoldtWeight p n : ℝ) := by
  unfold mangoldtTwist
  push_cast
  apply sum_congr rfl
  intro n hn
  have hu : IsUnit (n : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have := (ZMod.val_eq_zero _).mpr h
    rw [ZMod.val_natCast_of_lt (mem_Ico.mp hn).2] at this
    have := (mem_Ico.mp hn).1
    omega
  rw [MulChar.one_apply hu, mul_one]

/-- Any primitive residue of nonzero von Mangoldt weight supplies an actual
prime primitive root, including when the residue is represented by a higher power. -/
private theorem prime_of_weighted_generator (a : (ZMod p)ˣ)
    (hw : (mangoldtWeight p (a : ZMod p).val : ℂ) ≠ 0)
    (ho : orderOf (a : ZMod p) = p - 1) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  have hp : p.Prime := Fact.out
  have hΛ : ArithmeticFunction.vonMangoldt (a : ZMod p).val ≠ 0 := by
    intro h
    apply hw
    simp [mangoldtWeight, h]
  obtain ⟨q, k, hq, hk, hpow⟩ :=
    (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hqp : q < p := calc
    q ≤ q ^ k := le_self_pow hq.one_le hk.ne'
    _ = (a : ZMod p).val := hpow
    _ < p := ZMod.val_lt _
  have hcast : (q : ZMod p) ^ k = (a : ZMod p) := by
    rw [← Nat.cast_pow, hpow, ZMod.natCast_zmod_val]
  have hbig : p - 1 ∣ orderOf (q : ZMod p) := by
    rw [← ho, ← hcast]
    exact orderOf_pow_dvd k
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hq.pos hqp
  exact ⟨q, hq, hqp, Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hq0)) hbig⟩

/-- The only analytic quantities here are exactly the smoothed sums in MTT,
Lemma 1, at `x = p`. No prior primitive-root bound is used. -/
theorem prime_primitive_root_of_mangoldtTwists (B : ℝ)
    (hb : ∀ χ : Character p, χ ≠ 1 → ‖mangoldtTwist χ‖ ≤ B)
    (hmain : ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B <
      ∑ n ∈ Ico 1 p, mangoldtWeight p n) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  let w (a : (ZMod p)ˣ) : ℂ := mangoldtWeight p (a : ZMod p).val
  have bounds (χ : Character p) (hχ : χ ≠ 1) : ‖twist w χ‖ ≤ B := by
    rw [show twist w χ = mangoldtTwist χ from twist_eq_mangoldtTwist χ]
    exact hb χ hχ
  have main : ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B < ‖twist w 1‖ := by
    rw [show twist w 1 = mangoldtTwist 1 from twist_eq_mangoldtTwist 1,
      mangoldtTwist_one, Complex.norm_real, Real.norm_eq_abs]
    exact hmain.trans_le (le_abs_self _)
  obtain ⟨a, hw, ho⟩ := exists_generator_of_twists w B bounds main
  exact prime_of_weighted_generator a hw ho

#print axioms prime_primitive_root_of_mangoldtTwists

end JSP818.CharacterSieve
