import FiniteCases.Intervals

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem thirdC : Span (choice 5 (basicCap 5) 6 3) 12 72 := by certify_interval 5 [2,3]

end JSP818.Enumeration
