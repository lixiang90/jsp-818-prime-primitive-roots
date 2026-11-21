import CertifyEnumeration

namespace JSP818.Enumeration

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem cover4 : Cover 4 (basicCap 4) 2 3 3 := by certify_factors 4 [2]

end JSP818.Enumeration
