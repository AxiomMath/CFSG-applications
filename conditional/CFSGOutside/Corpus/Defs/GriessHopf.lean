import Mathlib

/-!
# Copied corpus definitions: Hopf's formula for the Schur multiplier

Definitions copied verbatim (only `@[expose]` dropped) from AxiomMath/CFSG at commit
69cb972f587a3ecc035e092253167ff2e303c962, file `CFSG/Open/GriessSchurMultipliersMilestoneDefs.lean`, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash:

* `Open.griessHopfRelations` from `CFSG.Open.griessHopfRelations` (line 10);
* `Open.griessHopfMultiplier` from `CFSG.Open.griessHopfMultiplier` (line 13);
* `Open.griessPSLExceptional` from `CFSG.Open.griessPSLExceptional` (line 18).
-/

namespace CFSGOutside.Corpus.Open

open scoped MatrixGroups

/-- The relations `R = ker(F(X) → X)` of the free presentation of `X` on its own elements. Copy of
`CFSG.Open.griessHopfRelations`. -/
abbrev griessHopfRelations (X : Type) [Group X] : Subgroup (FreeGroup X) :=
  (FreeGroup.lift (id : X → X)).ker

/-- The Schur multiplier by Hopf's formula, `(R ∩ [F, F]) / [F, R]`. Copy of `CFSG.Open.griessHopfMultiplier`. -/
abbrev griessHopfMultiplier (X : Type) [Group X] : Type :=
  ↥(griessHopfRelations X ⊓ commutator (FreeGroup X)) ⧸
    (⁅(⊤ : Subgroup (FreeGroup X)), griessHopfRelations X⁆).subgroupOf
      (griessHopfRelations X ⊓ commutator (FreeGroup X))

/-- The exceptional part of the Schur multiplier of `PSL(n, q)`. Copy of `CFSG.Open.griessPSLExceptional`. -/
def griessPSLExceptional (n q : ℕ) : ℕ × ℕ :=
  if (n = 2 ∧ q = 4) ∨ (n = 3 ∧ q = 2) ∨ (n = 4 ∧ q = 2) then (2, 1)
  else if n = 2 ∧ q = 9 then (3, 1)
  else if n = 3 ∧ q = 4 then (4, 4)
  else (1, 1)

end CFSGOutside.Corpus.Open
