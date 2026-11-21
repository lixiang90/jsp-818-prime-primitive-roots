import FiniteEnumeration
import Lean.Elab.Tactic

namespace JSP818.Enumeration

open Lean Meta Elab Tactic

/- The elaborator proposes a factor, a factor-count check or a prime root.
Its only certificates are applications of the lemmas in FiniteEnumeration. -/

private def primeWitnesses := (List.range 194).filter trialPrime

private def hint (k d lo : Nat) (chosen : List Nat) (n : Nat) : Except String Nat := do
  let p := d*n+1
  if p ≤ 2791 || ((150+7*(p.log2+1))*(2^k-1))^2 < 25*p then return 0
  let v := p.minFac
  if v < p then return 194+v
  let rest := trialFactors 100 n 2
  if rest.all (· < lo) then return 194
  let factors := (chosen ++ rest).eraseDups
  if factors.length != k then return 1
  for q in primeWitnesses do
    if factors.all (fun r => squareAndMultiply p q 36 ((p-1)/r) != 1) then return q
  throw s!"no prime witness at {p}"

private def trueRefl : Expr := mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)

private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def spanType (p : Expr) (a n : Nat) := app ``Span #[p, mkNatLit a, mkNatLit n]
private def join (p : Expr) (a n m : Nat) (l r : Expr) :=
  app ``span_join #[p, mkNatLit a, mkNatLit n, mkNatLit m, l, r]

private def packedPage (k d lo : Nat) (chosen : List Nat) (a n : Nat) : MetaM Expr := do
  let mut hints := 0
  for j in [0:n] do
    match hint k d lo chosen (a+n-1-j) with
    | .error e => throwError e
    | .ok h =>
      if h ≥ 65536 then throwError "row hint exceeds sixteen bits"
      hints := hints*65536+h
  return app ``page_sound #[mkNatLit k, mkNatLit d, mkNatLit lo, toExpr chosen, mkNatLit a,
    mkNatLit n, mkNatLit hints, trueRefl]

/-- Small pages keep reduction local. Opaque interval lemmas allow the kernel
to discard intermediate modular powers before checking the next interval. -/
private partial def rows (k d lo : Nat) (chosen : List Nat) (a n : Nat) (separate : Bool) : MetaM Expr := do
  let p := app ``multiple #[mkNatLit k, mkNatLit d, mkNatLit lo]
  if n == 0 then return app ``span_zero #[p, mkNatLit a]
  let value ← if n ≤ 16 then packedPage k d lo chosen a n else do
    let h := n / 2
    let sealChildren := n > 192
    let l ← rows k d lo chosen a h sealChildren
    let r ← rows k d lo chosen (a+h) (n-h) sealChildren
    pure (join p a h (n-h) l r)
  if separate && n ≤ 192 then
    mkAuxTheorem (spanType p a n) value (cache := false)
  else return value

mutual
  private partial def node (k cap d lo left : Nat) (chosen : List Nat) : MetaM Expr := do
    let mut stop := lo
    while d*stop^left < cap do stop := stop+1
    let type := app ``Cover #[mkNatLit k, mkNatLit cap, mkNatLit d, mkNatLit lo, mkNatLit left]
    let value ← if left == 1 then do
      let r ← rows k d lo chosen lo (stop-lo) false
      pure (app ``last #[mkNatLit k, mkNatLit cap, mkNatLit d, mkNatLit lo, mkNatLit stop, trueRefl, r])
    else do
      let r ← choices k cap d left chosen lo (stop-lo)
      pure (app ``branch #[mkNatLit k, mkNatLit cap, mkNatLit d, mkNatLit lo, mkNatLit left,
        mkNatLit stop, trueRefl, trueRefl, r])
    mkAuxTheorem type value (cache := false)

  private partial def choices (k cap d left : Nat) (chosen : List Nat) (a n : Nat) : MetaM Expr := do
    let p := app ``choice #[mkNatLit k, mkNatLit cap, mkNatLit d, mkNatLit left]
    if n == 0 then return app ``span_zero #[p, mkNatLit a]
    if n == 1 then
      let v := a.minFac
      let value ← if v == a then do
        let child ← node k cap (d*a) (a+1) (left-1) (a::chosen)
        pure (mkLambda `h .default (app ``Nat.Prime #[mkNatLit a]) child)
      else pure (app ``composite_choice #[mkNatLit k, mkNatLit cap, mkNatLit d, mkNatLit left,
        mkNatLit a, mkNatLit v, trueRefl])
      return app ``span_one #[p, mkNatLit a, value]
    let h := n/2
    let l ← choices k cap d left chosen a h
    let r ← choices k cap d left chosen (a+h) (n-h)
    return join p a h (n-h) l r
end

elab "certify_factors " k:num " [" ds:num,* "]" : tactic => do
  let count := k.getNat
  let chosen := ds.getElems.toList.map (·.getNat)
  if count ≤ chosen.length then throwError "the chosen prefix must leave at least one prime"
  let value ← node count (basicCap count) chosen.prod ((chosen.foldl max 0)+1)
    (count-chosen.length) chosen
  (← getMainGoal).assign value
  replaceMainGoal []

end JSP818.Enumeration
