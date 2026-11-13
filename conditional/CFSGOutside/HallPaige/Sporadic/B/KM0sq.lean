import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `M0 * M0 = 1`, strip by strip. -/
theorem kM0sq :
    allStripsB [Cert.M0] Cert.M0 idStrips = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
