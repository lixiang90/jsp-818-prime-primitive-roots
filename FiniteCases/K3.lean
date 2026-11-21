import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover3 : Cover 3 (basicCap 3) 2 3 2 := by certify_factors 3 [2]

end JSP818.Enumeration
