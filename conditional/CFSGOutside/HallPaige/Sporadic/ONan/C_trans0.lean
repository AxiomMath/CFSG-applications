import CFSGOutside.HallPaige.Sporadic.ONan.Cert
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-! Generated block checks for `ONan`. -/

namespace CFSGOutside.HallPaige.Sporadic.ONanData

open CFSGOutside.HallPaige.PermKit CFSGOutside.HallPaige.PermKitF

set_option maxHeartbeats 0

theorem b_trans0_0 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 0 = true := by
  decide +kernel

theorem b_trans0_1 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 1 = true := by
  decide +kernel

theorem b_trans0_2 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 2 = true := by
  decide +kernel

theorem b_trans0_3 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 3 = true := by
  decide +kernel

theorem b_trans0_4 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 4 = true := by
  decide +kernel

theorem b_trans0_5 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 5 = true := by
  decide +kernel

theorem b_trans0_6 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 6 = true := by
  decide +kernel

theorem b_trans0_7 : allBlock (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) cert.n 16384 7 = true := by
  decide +kernel

theorem ok_trans0 : ∀ x < cert.n, (cert.transPt TauCeti.SporadicName.ONan.presentation.generatorCount) x = true :=
  forall_of_blocks (K := 8) (B := 16384) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => b_trans0_0
    | 1, _ => b_trans0_1
    | 2, _ => b_trans0_2
    | 3, _ => b_trans0_3
    | 4, _ => b_trans0_4
    | 5, _ => b_trans0_5
    | 6, _ => b_trans0_6
    | 7, _ => b_trans0_7
    | _ + 8, h => absurd h (by omega)

end CFSGOutside.HallPaige.Sporadic.ONanData
