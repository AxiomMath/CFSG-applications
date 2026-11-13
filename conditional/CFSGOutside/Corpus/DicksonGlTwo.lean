import CFSGOutside.Corpus.Defs.ClassicalModel

/-!
# Corpus input: Dickson's theorem for `GL₂(𝔽_p)`

Statement of `CFSG.RankThree.SubgroupLists.dickson_gl_two`, copied verbatim from
`CFSG/RankThree/SubgroupLists/DicksonGL2.lean` (line 323, with the section variables of the section `GLTwo`) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `StatedSL` is the copy
`CFSGOutside.Corpus.Open.StatedSL`.

A subgroup of `GL₂(𝔽_p)` of order divisible by `p` has a normal Sylow `p`-subgroup of order `p`, or contains
`SL₂(𝔽_p)`. The clean build provides the instance, in `clean/CFSGOutsideClean/Corpus/DicksonGlTwo.lean`.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- Dickson's theorem for subgroups of `GL₂(𝔽_p)` of order divisible by `p`, as `dickson_gl_two` states it. -/
class DicksonGlTwo : Prop where
  dickson_gl_two : ∀ {p : ℕ} [Fact p.Prime] (H : Subgroup (GL (Fin 2) (ZMod p))) (_hpH : p ∣ Nat.card H),
    (∃ P : Sylow p H, (P : Subgroup H).Normal ∧ Nat.card P = p) ∨ Open.StatedSL 2 (ZMod p) ≤ H

end CFSGOutside.Corpus
