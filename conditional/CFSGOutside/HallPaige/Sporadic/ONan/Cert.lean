import CFSGOutside.HallPaige.Sporadic.ONan.T0
import CFSGOutside.HallPaige.Sporadic.ONan.T1
import CFSGOutside.HallPaige.Sporadic.ONan.T2
import CFSGOutside.HallPaige.Sporadic.ONan.T3
import CFSGOutside.HallPaige.Sporadic.ONan.T4
import CFSGOutside.HallPaige.Sporadic.ONan.T5
import CFSGOutside.HallPaige.Sporadic.ONan.T6

/-! The certificate for `ONan` on 122760 points (suborbit sizes [1, 6384, 52136, 58653, 5586]). -/

namespace CFSGOutside.HallPaige.Sporadic.ONanData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

/-- The certificate for `ONan`. -/
def cert : CFSGOutside.HallPaige.PermKitF.Cert where
  n := 122760
  gens := [(T_g0f, T_g0f), (T_g1f, T_g1f), (T_g2f, T_g2f), (T_g3f, T_g3f), (T_g4f, T_g4f), (T_g5f, T_g5f), (T_g6f, T_g6b)]
  elems := [([11, 13, 3, 1, 7, 13, 5, 7, 12, 7, 4, 3, 12, 7, 1, 3, 4], T_e0),
    ([1, 7, 5, 3, 11, 13, 7, 6, 2, 1, 7, 13, 8, 4, 0, 13, 7], T_e1),
    ([5, 7, 9, 13, 9, 13, 3, 9, 12, 8, 5, 13, 7, 8, 3, 5, 11, 8], T_e2),
    ([1, 5, 7, 5, 9, 11, 12, 4, 12, 4, 1, 9, 1, 5, 6], T_e3),
    ([9, 13, 3, 1, 7, 9, 13, 8, 12, 4, 8, 2, 11, 7, 13, 9, 7], T_e4),
    ([6, 12, 1, 5, 9, 12, 6, 0, 3, 7, 6, 12, 10, 2, 4, 6, 0], T_e5),
    ([5, 2, 0, 6, 13, 2, 5, 6, 13, 6, 4, 12, 6, 0, 2, 12, 10], T_e6),
    ([9, 10, 4, 2, 9, 6, 12, 4, 9, 13, 8, 2, 12, 8, 12, 8, 6, 4], T_e7),
    ([6, 8, 12, 6, 10, 3, 9, 5, 13, 9, 12, 8, 6, 0, 2, 12, 8], T_e8),
    ([24, 24, 26, 28, 30, 26, 24, 26, 24, 20, 24, 20, 26, 18, 16, 28, 18, 30], T_e9),
    ([7, 4, 0, 8, 0, 5, 13, 5, 13, 10, 8, 4, 6, 4, 0], T_e10),
    ([26, 24, 28, 26, 30, 24, 24, 26, 24, 30, 34, 30, 16, 22, 22, 28, 30, 22, 20, 16], T_e11),
    ([24, 28, 26, 28, 26, 26, 28, 26, 30, 28, 20, 28, 20, 30, 20], T_e12),
    ([26, 24, 24, 28, 30, 30, 24, 24, 24, 24, 20, 28, 30, 16, 16, 16, 24, 28, 26], T_e13),
    ([16, 22, 16, 16, 22, 16, 16, 22, 16, 16, 22, 16, 16, 22, 16, 16, 22, 16, 16, 22, 16], T_e14),
    ([36], T_e15),
    ([24, 34, 30, 22, 18, 30, 30, 24, 22, 20, 22, 16, 14, 16, 16, 22, 14, 18, 16, 14], T_e16),
    ([46], T_e17),
    ([48, 42, 44], T_e18),
    ([42, 50, 42, 50, 42, 50], T_e19)]
  x0 := 0
  trans := ⟨T_trdep, T_trpar, T_trvia, (fun _ => 0)⟩
  levels := [⟨[7, 8, 9, 10, 11, 16, 18, 19, 20], 87042, ⟨T_L0dep, T_L0par, T_L0via, (fun _ => 0)⟩, 58653⟩,
    ⟨[16, 18, 19, 20], 79352, ⟨T_L1dep, T_L1par, T_L1via, (fun _ => 0)⟩, 64⟩]
  lab := ⟨T_labdep, T_labpar, T_labvia, T_labcls⟩
  labReps := [0, 1, 2, 5, 14]
  wit := [[], [8, 6, 4, 2, 12, 4, 12, 6, 8, 2, 4, 2], [10, 8, 12, 4, 6, 8, 12, 2, 4, 6, 12, 2], [4, 6, 4, 12, 8, 6, 4, 6, 12], [10, 8, 12, 4, 6, 12, 10, 0]]
  iu := 21
  iz := 26
  kp := (1, 1, 1)

end CFSGOutside.HallPaige.Sporadic.ONanData
