import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T0
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T1
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T2
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T3
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T4
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T5
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T6
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T7
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T8
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T9
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T10
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T11
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T12
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T13
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T14
import CFSGOutside.HallPaige.Sporadic.Fi24Prime.T15

/-! The certificate for `Fi24Prime` on 306936 points (suborbit sizes [1, 31671, 275264]). -/

namespace CFSGOutside.HallPaige.Sporadic.Fi24PrimeData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

/-- The certificate for `Fi24Prime`. -/
def cert : CFSGOutside.HallPaige.PermKitF.Cert where
  n := 306936
  gens := [(T_g0f, T_g0b), (T_g1f, T_g1f), (T_g2f, T_g2f), (T_g3f, T_g3f), (T_g4f, T_g4f), (T_g5f, T_g5f), (T_g6f, T_g6f), (T_g7f, T_g7f), (T_g8f, T_g8f), (T_g9f, T_g9b), (T_g10f, T_g10f)]
  elems := [([20, 14, 12, 4, 6, 5, 20, 13], T_e0),
    ([8, 4, 6, 16, 4, 8, 21], T_e1),
    ([8, 10, 6, 8, 4, 20, 1, 3, 16, 1], T_e2),
    ([26, 22, 26, 26, 24, 22, 26, 22, 26, 22, 22, 26, 22, 26, 26, 22, 26, 26, 12, 8, 26, 26, 8, 2, 13, 11, 17], T_e3),
    ([26, 24, 22, 22, 28, 24, 22, 28, 26, 24, 22, 6, 26, 26, 20, 0, 17, 3, 11, 20], T_e4),
    ([24, 26, 28, 22, 30, 22, 0, 0, 28, 10, 6, 17, 15, 20, 13, 7], T_e5),
    ([30, 28, 28, 32, 32, 32, 32, 28, 30, 28, 22, 28, 26, 24, 32, 24, 26, 26, 22, 16, 6, 26, 4, 0, 5, 9, 6, 11, 3], T_e6),
    ([30, 28, 30, 28, 28, 32, 28, 26, 22, 26, 30, 22, 28, 34, 10, 4, 26, 4, 0, 6, 16, 8, 11, 6], T_e7),
    ([28, 28, 28, 28, 28, 28, 34, 36, 24, 34, 34, 28, 28, 28, 24, 12, 2, 24, 6, 2, 13, 16, 7, 15, 20], T_e8)]
  x0 := 119086
  trans := ⟨T_trdep, T_trpar, T_trvia, (fun _ => 0)⟩
  levels := [⟨[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], 201980, ⟨T_L0dep, T_L0par, T_L0via, (fun _ => 0)⟩, 275264⟩,
    ⟨[11, 12, 13, 14, 15, 16, 17, 18, 19], 286909, ⟨T_L1dep, T_L1par, T_L1via, (fun _ => 0)⟩, 218400⟩,
    ⟨[14, 15, 16, 17, 18, 19], 47989, ⟨T_L2dep, T_L2par, T_L2via, (fun _ => 0)⟩, 93312⟩,
    ⟨[17, 18, 19], 203816, ⟨T_L3dep, T_L3par, T_L3via, (fun _ => 0)⟩, 729⟩]
  lab := ⟨T_labdep, T_labpar, T_labvia, T_labcls⟩
  labReps := [119086, 3, 0]
  wit := [[], [11, 18, 21, 13, 0, 17, 18, 3, 9, 7, 1, 16, 8, 3], [19]]
  iu := 1
  iz := 3
  kp := (0, 0, 0)

end CFSGOutside.HallPaige.Sporadic.Fi24PrimeData
