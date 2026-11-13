import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `V2 * V2 = 1`, strip by strip. -/
theorem kV2sq :
    allStripsB [Cert.V2] Cert.V2 idStrips = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
