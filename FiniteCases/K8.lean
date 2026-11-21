import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover8 : Cover 8 (basicCap 8) 2 3 7 := by certify_factors 8 [2]

end JSP818.Enumeration
