import CFSGOutside.HallPaige.Sporadic.M.Keys1

/-! Kernel evaluations of the corpus short-vector keys `Native.keyAt (Native.thetaTab ()) p` used
by the Monster triangles (`Sporadic/M/Visible.lean`). -/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M.Monster.AxisCount

theorem keyAt_628 : Native.keyAt (Native.thetaTab ()) 628 = (57, 4) := by
  rw [thetaTab_eq]; decide +kernel

theorem keyAt_49704 : Native.keyAt (Native.thetaTab ()) 49704 = (1, 0) := by
  rw [thetaTab_eq]; decide +kernel

end CFSGOutside.HallPaige.M
