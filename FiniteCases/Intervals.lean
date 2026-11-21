import CertifyEnumeration

namespace JSP818.Enumeration
open Lean Elab Tactic Meta

/-- Check one prime branch after interval_cases has made its index a numeral. -/
elab "extend_factors " k:num " [" ds:num,* "] " h:ident : tactic => withMainContext do
  let type ← inferType (← elabTerm h none)
  let some r ← getNatValue? type.appArg! | throwError "expected a numerical prime hypothesis"
  if r.minFac != r then
    let v := Syntax.mkNumLit (toString r.minFac)
    evalTactic (← `(tactic| exact False.elim ((not_prime_of_factor (v := $v) (by decide)) $h)))
  else
    let factors := ds.getElems.push (Syntax.mkNumLit (toString r))
    evalTactic (← `(tactic| certify_factors $k [$factors,*]))

macro "certify_interval " k:num " [" ds:num,* "]" : tactic =>
  `(tactic| (intro r lower upper prime; interval_cases r <;> extend_factors $k [$ds,*] prime))

end JSP818.Enumeration
