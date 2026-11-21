import FiniteCases.Five.Smallest3Next5
import FiniteCases.Five.Smallest3Next7
import FiniteCases.Five.Smallest3Other
import FiniteCases.Five.Smallest5
import FiniteCases.Five.SmallestOther

namespace JSP818.Enumeration

/-- The largest numerical case is checked in independently buildable intervals. -/
theorem cover5 : Cover 5 (basicCap 5) 2 3 4 := by
  have atThree : choice 5 (basicCap 5) 2 4 3 := by
    intro _
    apply branch (stop := 84) (by decide) (by decide)
    exact span_join thirdA (span_join thirdB thirdC)
  apply branch (stop := 37) (by decide) (by decide)
  exact span_join (span_one atThree) (span_join secondA secondB)

end JSP818.Enumeration
