import CFSGOutside.Corpus.HallPaige.M

/-! Kernel evaluations of the corpus short-vector keys `Native.keyAt (Native.thetaTab ()) p` used
by the Monster triangles (`Sporadic/M/Visible.lean`). -/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M.Monster.AxisCount

/-- `thetaTab` as a list literal: the corpus builds it with `Array.map`, which the kernel does not
unfold, so the key evaluations below go through this form. -/
theorem thetaTab_eq : Native.thetaTab () =
    ((List.range 4096).map CFSGOutside.Corpus.M.Monster.B.Rep4371.Native.thetaN).toArray := by
  apply Array.ext
  · simp [Native.thetaTab]
  · intro i h₁ h₂
    simp [Native.thetaTab]

theorem keyAt_0 : Native.keyAt (Native.thetaTab ()) 0 = (0, 191) := by
  rw [thetaTab_eq]; decide +kernel

theorem keyAt_1 : Native.keyAt (Native.thetaTab ()) 1 = (63, 191) := by
  rw [thetaTab_eq]; decide +kernel

theorem keyAt_552 : Native.keyAt (Native.thetaTab ()) 552 = (0, 62) := by
  rw [thetaTab_eq]; decide +kernel

end CFSGOutside.HallPaige.M
