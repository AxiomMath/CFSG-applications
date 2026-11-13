import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: a certificate of `rank (N2 - 1) = 2048`. -/
theorem kN2rk :
    rankChk Cert.N2 Cert.PrkN2 Cert.RrkN2 2048 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
