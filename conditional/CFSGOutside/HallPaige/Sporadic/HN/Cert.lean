import CFSGOutside.HallPaige.Sporadic.HN.T0
import CFSGOutside.HallPaige.Sporadic.HN.T1
import CFSGOutside.HallPaige.Sporadic.HN.T2
import CFSGOutside.HallPaige.Sporadic.HN.T3
import CFSGOutside.HallPaige.Sporadic.HN.T4
import CFSGOutside.HallPaige.Sporadic.HN.T5
import CFSGOutside.HallPaige.Sporadic.HN.T6
import CFSGOutside.HallPaige.Sporadic.HN.T7
import CFSGOutside.HallPaige.Sporadic.HN.T8

/-! The certificate for `HN` on 1539000 points (suborbit sizes [1, 1408, 2200, 5775, 35200, 123200, 277200, 354816, 739200]). -/

namespace CFSGOutside.HallPaige.Sporadic.HNData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

/-- The certificate for `HN`. -/
def cert : CFSGOutside.HallPaige.PermKitF.Cert where
  n := 1539000
  gens := [(T_g0f, T_g0b), (T_g1f, T_g1b), (T_g2f, T_g2b), (T_g3f, T_g3f), (T_g4f, T_g4b)]
  elems := [([7, 4, 3, 9, 4, 1, 9, 2, 4, 6], T_e0),
    ([5, 2, 5, 3, 3, 4, 0, 2, 5, 0, 3, 4, 0], T_e1),
    ([1, 7, 5, 7, 5, 2, 2, 0, 6, 2, 2, 4, 2, 2, 4, 3], T_e2),
    ([0, 0], T_e3)]
  x0 := 1526755
  trans := ⟨T_trdep, T_trpar, T_trvia, (fun _ => 0)⟩
  levels := [⟨[0, 1, 2, 3, 5, 6, 7], 11, ⟨T_L0dep, T_L0par, T_L0via, (fun _ => 0)⟩, 739200⟩,
    ⟨[5, 6, 7], 0, ⟨T_L1dep, T_L1par, T_L1via, (fun _ => 0)⟩, 240⟩]
  lab := ⟨T_labdep, T_labpar, T_labvia, T_labcls⟩
  labReps := [1526755, 125, 165, 344, 19, 5, 35, 0, 11]
  wit := [[], [2, 4, 2, 4, 2, 4, 6, 0, 8], [6, 0, 2, 2, 4, 6, 2, 2, 2, 2, 4, 8, 6, 4, 8], [8, 6, 2, 4, 8, 2, 2, 2, 4, 6, 8, 2, 2, 4, 8, 6, 8], [2, 2, 2, 4, 6, 0, 8, 2, 4, 6, 0, 2, 2, 4, 6, 0, 8], [6, 8, 0, 2, 2, 4, 6, 4, 8, 2, 4, 6, 2, 2, 2, 4, 6, 4, 8], [6, 4, 6, 8, 6, 2, 4, 0, 2, 2, 4, 6, 8, 6, 2, 4, 6, 8], [6, 0, 8, 2, 2, 4, 6, 4, 8, 2, 4, 6, 2, 2, 2, 4, 6, 4, 8], [2, 4, 2, 4, 2, 2, 4, 8, 6, 8, 4, 6, 2, 2, 4, 8, 6, 4, 8]]
  iu := 3
  iz := 8
  kp := (0, 0, 0)

end CFSGOutside.HallPaige.Sporadic.HNData
