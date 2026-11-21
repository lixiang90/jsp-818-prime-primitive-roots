import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover7 : Cover 7 (basicCap 7) 2 3 6 := by certify_factors 7 [2]

end JSP818.Enumeration
