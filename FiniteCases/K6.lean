import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover6 : Cover 6 (basicCap 6) 2 3 5 := by certify_factors 6 [2]

end JSP818.Enumeration
