import CFSGOutside.HallPaige.Sporadic.ONan.Cert

/-! Generated block checks for `ONan`. -/

namespace CFSGOutside.HallPaige.Sporadic.ONanData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

set_option maxHeartbeats 0

theorem b_gen4_0 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 0 = true := by
  decide +kernel

theorem b_gen4_1 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 1 = true := by
  decide +kernel

theorem b_gen4_2 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 2 = true := by
  decide +kernel

theorem b_gen4_3 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 3 = true := by
  decide +kernel

theorem b_gen4_4 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 4 = true := by
  decide +kernel

theorem b_gen4_5 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 5 = true := by
  decide +kernel

theorem b_gen4_6 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 6 = true := by
  decide +kernel

theorem b_gen4_7 : allBlock (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) cert.n 16384 7 = true := by
  decide +kernel

theorem ok_gen4 : ∀ x < cert.n, (fun x => invPt cert.n (cert.gens.getD 4 default).1 (cert.gens.getD 4 default).2 x) x = true :=
  forall_of_blocks (K := 8) (B := 16384) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => b_gen4_0
    | 1, _ => b_gen4_1
    | 2, _ => b_gen4_2
    | 3, _ => b_gen4_3
    | 4, _ => b_gen4_4
    | 5, _ => b_gen4_5
    | 6, _ => b_gen4_6
    | 7, _ => b_gen4_7
    | _ + 8, h => absurd h (by omega)

end CFSGOutside.HallPaige.Sporadic.ONanData
