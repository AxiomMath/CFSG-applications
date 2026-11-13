import Mathlib

/-!
# Copied corpus definitions: the Steinberg relations for `SL_n(F)`

Verbatim copy, under `CFSGOutside.Corpus`, of `CFSG.Open.steinbergSLRels` from
`CFSG/Open/SteinbergPresentationMilestoneDefs.lean` (line 10) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/SteinbergPresentation.lean`
shows the copy equals the original.
-/

namespace CFSGOutside.Corpus.Open

/-- The Steinberg relations for `SL_n(F)` on generators `(i, j, c)`, with `x_ii(c) = 1`;
`CFSG.Open.steinbergSLRels`. -/
def steinbergSLRels (n : ℕ) (F : Type) [Field F] : Set (FreeGroup (Fin n × Fin n × F)) :=
  {r | ∃ (i : Fin n) (c : F), r = FreeGroup.of (i, i, c)} ∪
  {r | ∃ (i j : Fin n) (c d : F), i ≠ j ∧
    r = FreeGroup.of (i, j, c) * FreeGroup.of (i, j, d) * (FreeGroup.of (i, j, c + d))⁻¹} ∪
  {r | ∃ (i j k l : Fin n) (c d : F), i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i) ∧
    r = FreeGroup.of (i, j, c) * FreeGroup.of (k, l, d) * (FreeGroup.of (i, j, c))⁻¹ *
        (FreeGroup.of (k, l, d))⁻¹ *
        (if j = k then FreeGroup.of (i, l, c * d)
          else if i = l then FreeGroup.of (k, j, -(c * d)) else 1)⁻¹}

end CFSGOutside.Corpus.Open
