import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `V2 = al * P * al * P`, strip by strip. -/
theorem kV2 :
    allStripsB [Cert.P, CFSGOutside.Corpus.B.KC.BM.Seven.al, Cert.P] CFSGOutside.Corpus.B.KC.BM.Seven.al Cert.V2 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
