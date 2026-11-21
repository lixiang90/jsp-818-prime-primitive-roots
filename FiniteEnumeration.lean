import FiniteCaps

namespace JSP818.Enumeration

open Finset

/-- The residual implication with the number of distinct prime factors fixed. -/
def Good (k p : ℕ) : Prop :=
  p.Prime → 2791 < p → (p-1).primeFactors.card = k →
    25*p ≤ ((150+7*(p.log2+1))*(2^k-1))^2 → finiteModulusCheck p = true

/-- The final cofactor must contain the largest of the distinct prime factors. -/
def multiple (k d lo n : ℕ) : Prop :=
  (∃ r : ℕ, r.Prime ∧ lo ≤ r ∧ r ∣ n) → Good k (d*n+1)

/-- An interval of possible next factors, or of possible final cofactors. -/
def Span (P : ℕ → Prop) (a n : ℕ) : Prop := ∀ i, a ≤ i → i < a+n → P i

theorem span_join {P : ℕ → Prop} {a n m : ℕ}
    (l : Span P a n) (r : Span P (a+n) m) : Span P a (n+m) := by
  intro i lo hi
  by_cases h : i < a+n
  · exact l i lo h
  · exact r i (by omega) (by omega)

theorem span_one {P : ℕ → Prop} {a : ℕ} (h : P a) : Span P a 1 := by
  intro i lo hi
  exact (show i = a by omega) ▸ h

theorem span_zero {P : ℕ → Prop} {a : ℕ} : Span P a 0 := by intro i lo hi; omega

/-- The unchosen distinct prime factors form S. The multiplier t accounts for
all repeated factors. The factors already chosen have product d. -/
def Cover (k cap d lo left : ℕ) : Prop :=
  ∀ (S : Finset ℕ) (t : ℕ), S.card = left → (∀ r ∈ S, r.Prime ∧ lo ≤ r) → 0 < t →
    let p := d * (∏ r ∈ S, r) * t + 1
    p ≤ cap → Good k p

/-- Choose the least remaining prime. A bound on d*r^left safely stops the search. -/
theorem branch {k cap d lo left stop : ℕ} (hpos : decide (0 < left) = true)
    (hcut : decide (cap ≤ d * stop ^ left) = true)
    (sub : Span (fun r => r.Prime → Cover k cap (d*r) (r+1) (left-1)) lo (stop-lo)) :
    Cover k cap d lo left := by
  have hl := of_decide_eq_true hpos
  have cut := of_decide_eq_true hcut
  intro S t card all ht p hc
  have ne : S.Nonempty := Finset.card_pos.mp (card ▸ hl)
  let r := S.min' ne
  have mem : r ∈ S := S.min'_mem ne
  have lower (x) (hx : x ∈ S) : r ≤ x := S.min'_le x hx
  have power : r ^ left ≤ ∏ x ∈ S, x := by
    rw [← card, ← Finset.prod_const]
    exact Finset.prod_le_prod lower
  have small : r < stop := by
    by_contra! big
    have h₁ := Nat.mul_le_mul_left d ((Nat.pow_le_pow_left big left).trans power)
    have h₂ := Nat.le_mul_of_pos_right (d * (∏ x ∈ S, x)) ht
    dsimp [p] at hc
    omega
  have next := sub r (all r mem).2 (by omega) (all r mem).1 (S.erase r) t
    (by rw [Finset.card_erase_of_mem mem, card])
    (fun x hx => ⟨(all x (Finset.mem_of_mem_erase hx)).1,
      lt_of_le_of_ne (lower x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm⟩) ht
  have eqp : d*r*(∏ x ∈ S.erase r, x)*t+1 = p := by
    dsimp [p]
    rw [Nat.mul_assoc d r, Finset.mul_prod_erase S (fun x : ℕ => x) mem]
  exact (show p ≤ cap → Good k p by simpa only [eqp] using next) hc

/-- Once one distinct factor is left, the entire cofactor n lies in one
short interval. The count of actual factors is tested by the row certificate. -/
theorem last {k cap d lo stop : ℕ} (hcut : decide (cap ≤ d*stop) = true)
    (rows : Span (multiple k d lo) lo (stop-lo)) : Cover k cap d lo 1 := by
  have cut := of_decide_eq_true hcut
  intro S t card all ht p hc
  obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp card
  change d * (∏ x ∈ ({r} : Finset ℕ), x) * t + 1 ≤ cap at hc
  simp only [Finset.prod_singleton] at hc
  have low := (all r (Finset.mem_singleton_self r)).2
  have one := Nat.le_mul_of_pos_right r ht
  have upper : r*t < stop := by
    by_contra! h
    have := Nat.mul_le_mul_left d h
    rw [Nat.mul_assoc] at hc
    omega
  have hr := all r (Finset.mem_singleton_self r)
  simpa [p, Nat.mul_assoc] using rows (r*t) (by omega) (by omega) ⟨r, hr.1, hr.2, ⟨t, rfl⟩⟩

/-- A proper divisor of an integer rules out the primality premise. -/
theorem not_prime_of_factor {p v : ℕ} (ok : (decide (1 < v ∧ v < p ∧ p % v = 0)) = true) :
    ¬p.Prime := by
  obtain ⟨h, lt, dv⟩ := of_decide_eq_true ok
  intro prime
  rcases (Nat.dvd_prime prime).mp (Nat.dvd_of_mod_eq_zero dv) with h' | h' <;> omega

def choice (k cap d left r : ℕ) := r.Prime → Cover k cap (d*r) (r+1) (left-1)

theorem composite_choice {k cap d left r v : ℕ}
    (h : decide (1 < v ∧ v < r ∧ r % v = 0) = true) : choice k cap d left r := by
  intro prime
  exact (not_prime_of_factor h prime).elim

/-- Trial factoring is used to propose a factor list for the small cofactor.
Every use checks the product and the primality of the proposed factors. -/
def trialFactors : ℕ → ℕ → ℕ → List ℕ
  | 0, n, _ => [n]
  | fuel+1, n, r =>
    if n ≤ 1 then [] else if n < r*r then [n]
    else if n % r = 0 then r :: trialFactors fuel (n/r) r
    else trialFactors fuel n (if r = 2 then 3 else r+2)

/-- Codes are 0 for the size test, 1 for a different factor count,
2 through 193 for a root, 194 for a cofactor with no large prime, and
194+v for a proper divisor v of p. -/
def row (k d lo : ℕ) (chosen : List ℕ) (n code : ℕ) : Bool :=
  let p := d*n+1
  if code = 0 then decide (p ≤ 2791 ∨ ((150+7*(p.log2+1))*(2^k-1))^2 < 25*p)
  else if code = 194 then
    let fs := trialFactors 100 n 2
    decide (fs.prod = n) && fs.all (fun r => trialPrime r && decide (r < lo))
  else if 194 ≤ code then
    let v := code-194
    decide (1 < v ∧ v < p ∧ p % v = 0)
  else
    let fs := chosen ++ trialFactors 100 n 2
    if code = 1 then
      decide (fs.prod = p-1) && fs.all trialPrime && decide (fs.toFinset.card ≠ k)
    else rootCertificate p code fs

theorem row_sound {k d lo n code : ℕ} {chosen : List ℕ}
    (checked : row k d lo chosen n code = true) : multiple k d lo n := by
  rintro ⟨r, prime, lower, dvd⟩ hp hl hk hres
  unfold row at checked
  dsimp only at checked
  split at checked
  · rcases of_decide_eq_true checked with h | h <;> omega
  split at checked
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
    have perm := Nat.primeFactorsList_unique checked.1 (fun s h => trialPrime_sound (checked.2 s h).1)
    have nz : n ≠ 0 := by rintro rfl; simp at hl
    have member := perm.mem_iff.mpr ((Nat.mem_primeFactorsList_iff_dvd nz prime).mpr dvd)
    exact (Nat.not_lt_of_ge lower (checked.2 r member).2).elim
  split at checked
  · exact (not_prime_of_factor checked hp).elim
  rename_i bound
  split at checked
  · let fs := chosen ++ trialFactors 100 n 2
    change (decide (fs.prod = d*n+1-1) && fs.all trialPrime &&
      decide (fs.toFinset.card ≠ k)) = true at checked
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
    have perm := Nat.primeFactorsList_unique checked.1.1 (fun r h => trialPrime_sound (checked.1.2 r h))
    have same : fs.toFinset = (d*n+1-1).primeFactors := by
      ext r
      simpa only [Nat.primeFactors, List.mem_toFinset] using (perm.mem_iff (a := r))
    exact (checked.2 ((congrArg Finset.card same).trans hk)).elim
  · exact finiteModulusCheck_of_certificate (by omega) checked

/-- The low sixteen bits contain the hint for the first row of a page. -/
def page (k d lo : ℕ) (chosen : List ℕ) : ℕ → ℕ → ℕ → Bool
  | _, 0, _ => true
  | a, n+1, hints => row k d lo chosen a (hints % 65536) &&
      page k d lo chosen (a+1) n (hints / 65536)

theorem page_sound {k d lo : ℕ} {chosen : List ℕ} {a n hints : ℕ}
    (h : page k d lo chosen a n hints = true) : Span (multiple k d lo) a n := by
  induction n generalizing a hints with
  | zero => exact span_zero
  | succ n ih =>
    simp only [page, Bool.and_eq_true] at h
    obtain ⟨first, rest⟩ := h
    exact (show 1+n = n+1 by omega) ▸ span_join (span_one (row_sound first)) (ih rest)

theorem basic_of_covers (roots : ∀ k, 2 ≤ k → k ≤ 9 → Cover k (basicCap k) 2 3 (k-1)) :
    BasicFiniteInput := by
  intro p hp hl hu hr
  let S := (p-1).primeFactors
  obtain ⟨kl, kh, cap⟩ := residual_cap hl hu hr
  have ev : 2 ∣ p-1 := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨t, by omega⟩
  have two : 2 ∈ S := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ev, by omega⟩
  obtain ⟨t, ht⟩ := Nat.prod_primeFactors_dvd (p-1)
  change p-1 = (∏ r ∈ S, r)*t at ht
  have pos : 0 < t := by by_contra! h; interval_cases t; simp_all
  have eqp : 2*(∏ r ∈ S.erase 2, r)*t+1 = p := by
    rw [Finset.mul_prod_erase S (fun x : ℕ => x) two, ← ht]; omega
  have root := roots S.card kl kh (S.erase 2) t (Finset.card_erase_of_mem two)
    (fun r h => by
      have pr := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h)
      have diff := Finset.ne_of_mem_erase h
      exact ⟨pr, by have := pr.two_le; omega⟩) pos
  rw [eqp] at root
  exact root cap hp hl rfl hr

end JSP818.Enumeration
