import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `P = A1 * t1 * A1`, strip by strip. -/
theorem kP :
    allStripsB [CFSGOutside.Corpus.B.KC.BM.Seven.t1, CFSGOutside.Corpus.B.KC.BM.Seeds.A1] CFSGOutside.Corpus.B.KC.BM.Seeds.A1 Cert.P = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
