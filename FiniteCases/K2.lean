import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover2 : Cover 2 (basicCap 2) 2 3 1 := by certify_factors 2 [2]

end JSP818.Enumeration
