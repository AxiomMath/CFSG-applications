import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `U = al * s4`, strip by strip. -/
theorem kU :
    allStripsB [CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4] CFSGOutside.Corpus.B.KC.BM.Seven.al Cert.U = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
