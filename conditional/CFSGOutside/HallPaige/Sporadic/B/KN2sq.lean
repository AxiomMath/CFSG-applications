import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `N2 * N2 = 1`, strip by strip. -/
theorem kN2sq :
    allStripsB [Cert.N2] Cert.N2 idStrips = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
