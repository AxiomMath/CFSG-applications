import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import CFSGOutside.Corpus.SolvableHall
import CFSGOutsideClean.Corpus.Defs.HallSubgroups

/-! The corpus proves the statements that `CFSGOutside.Corpus.SolvableHallExistence` and
`CFSGOutside.Corpus.SolvableHallConjugacy` assume. The two copied `IsHallSubgroup` structures are matched to the
corpus ones by `CFSGOutsideClean.Corpus.feitThompson_isHallSubgroup_iff` and `isHallSubgroup_iff`. -/

universe u

namespace CFSGOutsideClean.Corpus

instance solvableHallExistence : CFSGOutside.Corpus.SolvableHallExistence.{u} :=
  ⟨fun π => (CFSG.FeitThompson.exists_isHallSubgroup π).imp fun _ h =>
    (feitThompson_isHallSubgroup_iff π _).2 h⟩

instance solvableHallConjugacy : CFSGOutside.Corpus.SolvableHallConjugacy.{u} :=
  ⟨fun hsolv _ _ _ hHall₁ hHall₂ =>
    CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv
      ((isHallSubgroup_iff _ _).1 hHall₁) ((isHallSubgroup_iff _ _).1 hHall₂)⟩

end CFSGOutsideClean.Corpus
