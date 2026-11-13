import CFSG.Open.StatedDefs
import CFSG.Open.LocalVocabulary
import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutsideClean.Corpus.Defs.Fitting

/-!
# The copied models of the classical groups are the corpus ones

`CFSGOutside.Corpus.Defs.ClassicalModel` copies the `Stated*` definitions with the elaborator `matrix_model%`
already applied. The copied inductive type `Open.StatedLieTag` is not the corpus one, so we map it to the corpus
tag by `statedLieTagToCorpus`; for each tag the copied and the corpus classical models agree by `Iff.rfl`.
-/

namespace CFSGOutsideClean.Corpus.Open

/-- The corpus tag corresponding to a copied tag. -/
def statedLieTagToCorpus : CFSGOutside.Corpus.Open.StatedLieTag → CFSG.Open.StatedLieTag
  | .PSL => .PSL
  | .PSU => .PSU
  | .PSp => .PSp
  | .POmegaOdd => .POmegaOdd
  | .POmegaPlus => .POmegaPlus
  | .POmegaMinus => .POmegaMinus
  | .G2 => .G2
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .twistedE6 => .twistedE6
  | .trialityD4 => .trialityD4
  | .twistedB2 => .twistedB2
  | .twistedG2 => .twistedG2
  | .twistedF4 => .twistedF4
  | .Tits => .Tits

/-- The copied tag corresponding to a corpus tag. -/
def statedLieTagOfCorpus : CFSG.Open.StatedLieTag → CFSGOutside.Corpus.Open.StatedLieTag
  | .PSL => .PSL
  | .PSU => .PSU
  | .PSp => .PSp
  | .POmegaOdd => .POmegaOdd
  | .POmegaPlus => .POmegaPlus
  | .POmegaMinus => .POmegaMinus
  | .G2 => .G2
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .twistedE6 => .twistedE6
  | .trialityD4 => .trialityD4
  | .twistedB2 => .twistedB2
  | .twistedG2 => .twistedG2
  | .twistedF4 => .twistedF4
  | .Tits => .Tits

theorem statedLieTagToCorpus_ofCorpus (t : CFSG.Open.StatedLieTag) :
    statedLieTagToCorpus (statedLieTagOfCorpus t) = t := by
  cases t <;> rfl

theorem statedLieTagToCorpus_eq_tits_iff (t : CFSGOutside.Corpus.Open.StatedLieTag) :
    statedLieTagToCorpus t = .Tits ↔ t = .Tits := by
  cases t <;> simp [statedLieTagToCorpus]

theorem pCoreOf_eq (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    CFSGOutside.Corpus.Open.pCoreOf p H = CFSG.Open.pCoreOf p H :=
  rfl

theorem statedScalars_eq (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    CFSGOutside.Corpus.Open.StatedScalars ι K = CFSG.Open.StatedScalars ι K :=
  rfl

theorem statedSL_eq (n : ℕ) (K : Type) [Field K] :
    CFSGOutside.Corpus.Open.StatedSL n K = CFSG.Open.StatedSL n K :=
  rfl

theorem statedSU_eq (n q : ℕ) (K : Type) [Field K] :
    CFSGOutside.Corpus.Open.StatedSU n q K = CFSG.Open.StatedSU n q K :=
  rfl

theorem statedSp_eq (n : ℕ) (K : Type) [Field K] :
    CFSGOutside.Corpus.Open.StatedSp n K = CFSG.Open.StatedSp n K :=
  rfl

theorem statedOmega_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) :
    CFSGOutside.Corpus.Open.StatedOmega Q = CFSG.Open.StatedOmega Q :=
  rfl

theorem statedQuadOdd_eq (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    CFSGOutside.Corpus.Open.StatedQuadOdd n K v = CFSG.Open.StatedQuadOdd n K v :=
  rfl

theorem statedQuadPlus_eq (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) :
    CFSGOutside.Corpus.Open.StatedQuadPlus n K v = CFSG.Open.StatedQuadPlus n K v :=
  rfl

theorem statedQuadMinus_eq (n : ℕ) (K : Type) [Field K] (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    CFSGOutside.Corpus.Open.StatedQuadMinus n K b c v = CFSG.Open.StatedQuadMinus n K b c v :=
  rfl

theorem statedLieAdmissible_iff (t : CFSGOutside.Corpus.Open.StatedLieTag) (n p f : ℕ) :
    CFSGOutside.Corpus.Open.StatedLieAdmissible t n p f ↔
      CFSG.Open.StatedLieAdmissible (statedLieTagToCorpus t) n p f := by
  cases t <;> exact Iff.rfl

/-- The copied classical model is the corpus one. -/
theorem statedClassicalModel_iff (G : Type) [Group G] (t : CFSGOutside.Corpus.Open.StatedLieTag)
    (n p f : ℕ) :
    CFSGOutside.Corpus.Open.StatedClassicalModel G t n p f ↔
      CFSG.Open.StatedClassicalModel G (statedLieTagToCorpus t) n p f := by
  cases t <;> exact Iff.rfl

end CFSGOutsideClean.Corpus.Open
