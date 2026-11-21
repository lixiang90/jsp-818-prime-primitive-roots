import FiniteCases.Intervals

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem secondB : Span (choice 5 (basicCap 5) 2 4) 6 31 := by certify_interval 5 [2]

end JSP818.Enumeration
