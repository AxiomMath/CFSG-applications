import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: a certificate of `rank (M0 - 1) = 2048`. -/
theorem kM0rk :
    rankChk Cert.M0 Cert.PrkM0 Cert.RrkM0 2048 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
