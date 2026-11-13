import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `N2 = P * s4 * P * s4`, strip by strip. -/
theorem kN2 :
    allStripsB [CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4, Cert.P, CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4] Cert.P Cert.N2 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
