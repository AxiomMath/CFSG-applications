import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `W2 = t1 * P * t1 * P`, strip by strip. -/
theorem kW2 :
    allStripsB [Cert.P, CFSGOutside.Corpus.B.KC.BM.Seven.t1, Cert.P] CFSGOutside.Corpus.B.KC.BM.Seven.t1 Cert.W2 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
