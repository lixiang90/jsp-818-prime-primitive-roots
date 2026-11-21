import FiniteCases.K2
import FiniteCases.K3
import FiniteCases.K4
import FiniteCases.K5
import FiniteCases.K6
import FiniteCases.K7
import FiniteCases.K8
import FiniteCases.K9

namespace JSP818

/-- Unconditional exhaustive verification of all residual prime moduli. -/
theorem basicFiniteInput_verified : BasicFiniteInput := by
  apply Enumeration.basic_of_covers
  intro k lo hi
  interval_cases k
  all_goals first | exact Enumeration.cover2 | exact Enumeration.cover3 |
    exact Enumeration.cover4 | exact Enumeration.cover5 | exact Enumeration.cover6 |
    exact Enumeration.cover7 | exact Enumeration.cover8 | exact Enumeration.cover9

#print axioms basicFiniteInput_verified

end JSP818
