import CFSGOutside.HallPaige.Sporadic.HN.Cert
import CFSGOutside.HallPaige.Sporadic.HN.Count

/-! The orbit bound of level {i} of the stabilizer chain of `HN`, counted in blocks. -/

namespace CFSGOutside.HallPaige.Sporadic.HNData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF CFSGOutside.HallPaige.Sporadic.HNCount

set_option maxHeartbeats 0

theorem ok_count0 : cert.countOK 0 = true :=
  countOK_of_blockSum cert 0 (K := 76) (B := 20250) (by decide +kernel) (by decide +kernel)

end CFSGOutside.HallPaige.Sporadic.HNData
