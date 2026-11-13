import CFSGOutside.HallPaige.Sporadic.ONan.Cert

/-! Generated block checks for `ONan`. -/

namespace CFSGOutside.HallPaige.Sporadic.ONanData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

set_option maxHeartbeats 0

theorem b_elem14_0 : allBlock (cert.elemPt 14) cert.n 16384 0 = true := by
  decide +kernel

theorem b_elem14_1 : allBlock (cert.elemPt 14) cert.n 16384 1 = true := by
  decide +kernel

theorem b_elem14_2 : allBlock (cert.elemPt 14) cert.n 16384 2 = true := by
  decide +kernel

theorem b_elem14_3 : allBlock (cert.elemPt 14) cert.n 16384 3 = true := by
  decide +kernel

theorem b_elem14_4 : allBlock (cert.elemPt 14) cert.n 16384 4 = true := by
  decide +kernel

theorem b_elem14_5 : allBlock (cert.elemPt 14) cert.n 16384 5 = true := by
  decide +kernel

theorem b_elem14_6 : allBlock (cert.elemPt 14) cert.n 16384 6 = true := by
  decide +kernel

theorem b_elem14_7 : allBlock (cert.elemPt 14) cert.n 16384 7 = true := by
  decide +kernel

theorem ok_elem14 : ∀ x < cert.n, (cert.elemPt 14) x = true :=
  forall_of_blocks (K := 8) (B := 16384) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => b_elem14_0
    | 1, _ => b_elem14_1
    | 2, _ => b_elem14_2
    | 3, _ => b_elem14_3
    | 4, _ => b_elem14_4
    | 5, _ => b_elem14_5
    | 6, _ => b_elem14_6
    | 7, _ => b_elem14_7
    | _ + 8, h => absurd h (by omega)

end CFSGOutside.HallPaige.Sporadic.ONanData
