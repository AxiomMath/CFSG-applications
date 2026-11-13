import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: a certificate of `rank (V2 - 1) = 2048`. -/
theorem kV2rk :
    rankChk Cert.V2 Cert.PrkV2 Cert.RrkV2 2048 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
