import CFSGOutside.HallPaige.Sporadic.B.Cert

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM

/-- Kernel check: the strips of `A1` are well formed. -/
theorem wf_A1 : wfMat CFSGOutside.Corpus.B.KC.BM.Seeds.A1 = true := by
  decide +kernel

/-- Kernel check: the strips of `t1` are well formed. -/
theorem wf_t1 : wfMat CFSGOutside.Corpus.B.KC.BM.Seven.t1 = true := by
  decide +kernel

/-- Kernel check: the strips of `al` are well formed. -/
theorem wf_al : wfMat CFSGOutside.Corpus.B.KC.BM.Seven.al = true := by
  decide +kernel

/-- Kernel check: the strips of `e3` are well formed. -/
theorem wf_e3 : wfMat CFSGOutside.Corpus.B.KC.BM.Seven.e3 = true := by
  decide +kernel

/-- Kernel check: the strips of `s4` are well formed. -/
theorem wf_s4 : wfMat CFSGOutside.Corpus.B.KC.BM.SevenLocal.s4 = true := by
  decide +kernel

/-- Kernel check: the strips of `P` are well formed. -/
theorem wf_P : wfMat Cert.P = true := by
  decide +kernel

/-- Kernel check: the strips of `M0` are well formed. -/
theorem wf_M0 : wfMat Cert.M0 = true := by
  decide +kernel

/-- Kernel check: the strips of `N2` are well formed. -/
theorem wf_N2 : wfMat Cert.N2 = true := by
  decide +kernel

/-- Kernel check: the strips of `V2` are well formed. -/
theorem wf_V2 : wfMat Cert.V2 = true := by
  decide +kernel

/-- Kernel check: the strips of `W2` are well formed. -/
theorem wf_W2 : wfMat Cert.W2 = true := by
  decide +kernel

/-- Kernel check: the strips of `U` are well formed. -/
theorem wf_U : wfMat Cert.U = true := by
  decide +kernel

end CFSGOutside.HallPaige.B
