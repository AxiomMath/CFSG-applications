import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: a certificate of `rank (W2 - 1) = 2048`. -/
theorem kW2rk :
    rankChk Cert.W2 Cert.PrkW2 Cert.RrkW2 2048 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
