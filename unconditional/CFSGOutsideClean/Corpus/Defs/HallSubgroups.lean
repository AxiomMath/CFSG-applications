import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSGOutside.Corpus.Defs.HallSubgroups

/-! The definitions copied into `CFSGOutside.Corpus.Defs.HallSubgroups` are the corpus definitions. The two
`IsHallSubgroup` copies are structures distinct from the corpus ones with the same fields, so they are matched by an
`Iff`. -/

namespace CFSGOutsideClean.Corpus

theorem isPiNumber_iff (π : Set ℕ) (n : ℕ) :
    CFSGOutside.Corpus.FeitThompson.IsPiNumber π n ↔ CFSG.FeitThompson.IsPiNumber π n :=
  Iff.rfl

theorem feitThompson_isHallSubgroup_iff {G : Type*} [Group G] (π : Set ℕ) (H : Subgroup G) :
    CFSGOutside.Corpus.FeitThompson.IsHallSubgroup π H ↔ CFSG.FeitThompson.IsHallSubgroup π H :=
  ⟨fun h => ⟨h.natCard, h.index⟩, fun h => ⟨h.natCard, h.index⟩⟩

theorem isHallSubgroup_iff {G : Type*} [Group G] (π : Set Nat.Primes) (H : Subgroup G) :
    CFSGOutside.Corpus.IsHallSubgroup π H ↔ CFSG.IsHallSubgroup π H :=
  ⟨fun h => ⟨h.p_in_pi_of_p_dvd_card, h.p_in_pi_of_p_dvd_index⟩,
    fun h => ⟨h.p_in_pi_of_p_dvd_card, h.p_in_pi_of_p_dvd_index⟩⟩

end CFSGOutsideClean.Corpus
