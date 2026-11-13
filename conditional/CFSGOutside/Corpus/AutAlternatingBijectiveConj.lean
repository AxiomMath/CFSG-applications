import Mathlib

/-!
# Corpus input: automorphisms of alternating groups

Statement of `CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj`, copied verbatim from the vendored
Qiuzhen-CFSG file `CFSG/ThirdParty/QiuzhenCFSG/Theory/AutAlternating.lean` (line 2050) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.
-/

namespace CFSGOutside.Corpus

open Equiv

/-- For `n ≥ 5`, `n ≠ 6`, conjugation `Sₙ → Aut(Aₙ)` is bijective. -/
class AutAlternatingBijectiveConj : Prop where
  aut_alternatingGroup_bijective_conj : ∀ (n : ℕ) (_hn : 5 ≤ n) (_hn6 : n ≠ 6),
    Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))

end CFSGOutside.Corpus
