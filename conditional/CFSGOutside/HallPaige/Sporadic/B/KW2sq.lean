import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `W2 * W2 = 1`, strip by strip. -/
theorem kW2sq :
    allStripsB [Cert.W2] Cert.W2 idStrips = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
