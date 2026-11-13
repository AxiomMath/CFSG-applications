import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: `M0 = s4 * e3 * s4 * e3 * e3`, strip by strip. -/
theorem kM0 :
    allStripsB [CFSGOutside.Corpus.B.KC.BM.Seven.e3, CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4, CFSGOutside.Corpus.B.KC.BM.Seven.e3, CFSGOutside.Corpus.B.KC.BM.Seven.e3] CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4 Cert.M0 = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
