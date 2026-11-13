import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import CFSGOutside.Corpus.HallPaige.M.Blueprint.NativeSporadic

/-!
# Copied corpus declarations from `CFSG/Blueprint/FischerDefs.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Blueprint/FischerDefs.lean` -/

noncomputable section

namespace CFSGOutside.Corpus.M.Blueprint.Fischer

/-- Corpus: `CFSG.Blueprint.Fischer.K`, CFSG/Blueprint/FischerDefs.lean:9. -/
abbrev K := GaloisField 2 2
/-- Corpus: `CFSG.Blueprint.Fischer.V`, CFSG/Blueprint/FischerDefs.lean:10. -/
abbrev V := Fin 6 → K

/-- Corpus: `CFSG.Blueprint.Fischer.hermitian`, CFSG/Blueprint/FischerDefs.lean:12. -/
def hermitian (H : Matrix (Fin 6) (Fin 6) K) (x y : V) : K :=
  ∑ i, ∑ j, x i * H i j * (y j) ^ 2

/-- Corpus: `CFSG.Blueprint.Fischer.SU`, CFSG/Blueprint/FischerDefs.lean:19. -/
def SU (H : Matrix (Fin 6) (Fin 6) K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 6) K) :=
  Subgroup.closure {g | Matrix.GeneralLinearGroup.det g = 1 ∧
    ∀ x y : V, hermitian H (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) x)
      (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) y) = hermitian H x y}

/-- Corpus: `CFSG.Blueprint.Fischer.PSU`, CFSG/Blueprint/FischerDefs.lean:25. -/
abbrev PSU (H : Matrix (Fin 6) (Fin 6) K) := SU H ⧸ Subgroup.center (SU H)

/-- Corpus: `CFSG.Blueprint.Fischer.Pair`, CFSG/Blueprint/FischerDefs.lean:32. -/
def Pair (X : Type) [Group X] (E : Set X) : Prop :=
  Finite X ∧ (∃ e : X, E = {x | IsConj e x}) ∧
    (∀ e ∈ E, orderOf e = 2) ∧
    (∀ e ∈ E, ∀ f ∈ E, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧
    Subgroup.closure E = ⊤

end CFSGOutside.Corpus.M.Blueprint.Fischer
