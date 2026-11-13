import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `U * U = 1`, strip by strip. -/
theorem kUsq :
    allStripsB [Cert.U] Cert.U idStrips = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
