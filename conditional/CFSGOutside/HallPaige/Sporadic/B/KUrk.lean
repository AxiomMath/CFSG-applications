import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: a certificate of `rank (U - 1) = 2158`. -/
theorem kUrk :
    rankChk Cert.U Cert.PrkU Cert.RrkU 2158 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
