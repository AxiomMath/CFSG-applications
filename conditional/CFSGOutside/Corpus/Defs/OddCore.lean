import CFSGOutside.Corpus.Defs.OddCoreDihedral

/-!
# Copied corpus definition: quasisimple groups

Copied verbatim at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus`:
`Open.IsQuasisimple` from `CFSG/Open/Defs.lean` line 105 (`CFSG.Open.IsQuasisimple`). The odd core
`CFSGOutside.Corpus.oddCore` is the copy in `OddCoreDihedral.lean`.
-/

namespace CFSGOutside.Corpus

namespace Open

/-- Copy of `CFSG.Open.IsQuasisimple`. -/
def IsQuasisimple (G : Type*) [Group G] : Prop :=
  commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G)

end Open

end CFSGOutside.Corpus
