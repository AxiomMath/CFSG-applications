import Mathlib
import CFSGOutside.WittDesigns.S5612.Search

namespace CFSGOutside.WittDesigns.Witt5612

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem go_length_123 : (go fiveMasks (addCov 0 123) [123]).length = 720 := by decide +kernel

end CFSGOutside.WittDesigns.Witt5612
