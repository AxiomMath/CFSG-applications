import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
import CFSG.Certificates.Kernel.BabyMonster.FixSound
import CFSGOutside.Corpus.HallPaige.B.Defs

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.B` agree with the corpus definitions.

The copied inductive predicates `AllStrips` and `AllStripsX` are new types, so they agree with the corpus
ones only up to `Iff`, proved constructor by constructor.
-/

namespace CFSGOutsideClean.Corpus

theorem B_mulS_eq : @CFSGOutside.Corpus.B.KC.BM.mulS = @CFSG.KC.BM.mulS := by
  with_unfolding_all rfl

theorem B_forceB_eq : @CFSGOutside.Corpus.B.KC.BM.forceB = @CFSG.KC.BM.forceB := by
  with_unfolding_all rfl

theorem B_mulW_eq : @CFSGOutside.Corpus.B.KC.BM.mulW = @CFSG.KC.BM.mulW := by
  delta CFSGOutside.Corpus.B.KC.BM.mulW CFSG.KC.BM.mulW
  rw [B_mulS_eq, B_forceB_eq]

theorem B_allStrips_iff {Ws : List (List Nat)} {A C : List Nat} :
    CFSGOutside.Corpus.B.KC.BM.AllStrips Ws A C ↔ CFSG.KC.BM.AllStrips Ws A C := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons a c as cs hc _ ih => exact .cons a c as cs (B_mulW_eq ▸ hc) ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons a c as cs hc _ ih => exact .cons a c as cs (B_mulW_eq ▸ hc) ih

theorem B_allStripsX_iff {Q A C : List Nat} :
    CFSGOutside.Corpus.B.KC.BM.Fix.AllStripsX Q A C ↔ CFSG.KC.BM.Fix.AllStripsX Q A C := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons a c as cs hc _ ih => exact .cons a c as cs (B_mulS_eq ▸ hc) ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons a c as cs hc _ ih => exact .cons a c as cs (B_mulS_eq ▸ hc) ih

end CFSGOutsideClean.Corpus
