import CFSGOutside.HallPaige.Sporadic.M.Keys1

/-! Kernel evaluations of the corpus short-vector keys `Native.keyAt (Native.thetaTab ()) p` used
by the Monster triangles (`Sporadic/M/Visible.lean`). -/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M.Monster.AxisCount

theorem keyAt_50024 : Native.keyAt (Native.thetaTab ()) 50024 = (6, 57) := by
  rw [thetaTab_eq]; decide +kernel

theorem keyAt_178 : Native.keyAt (Native.thetaTab ()) 178 = (0, 6) := by
  rw [thetaTab_eq]; decide +kernel

end CFSGOutside.HallPaige.M
