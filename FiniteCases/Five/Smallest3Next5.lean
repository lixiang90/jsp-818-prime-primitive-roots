import FiniteCases.Intervals

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem thirdA : Span (choice 5 (basicCap 5) 6 3) 4 3 := by certify_interval 5 [2,3]

end JSP818.Enumeration
