import CFSGOutside.CravenGlesser.Main
import CFSGOutsideClean.Corpus.MacWilliamsFourGenerator
import CFSGOutsideClean.Corpus.Defs.TwoRank

/-!
# Craven–Glesser, Lemma 6.11, unconditionally

`CFSGOutside.CravenGlesser.lemma_6_11` with its corpus hypothesis discharged by
`CFSG.Milestones.cls_connectivity_macwilliams_four_generator`. The 2-rank is the copy
`CFSGOutside.Corpus.Open.twoRank`, which is `CFSG.Open.twoRank` by `rfl`
(`CFSGOutsideClean.Corpus.Open.twoRank_eq`).
-/

namespace CFSGOutsideClean.CravenGlesser

/-- **Fusion systems on small 2-groups.** Let P be a finite 2-group of 2-rank 2 and φ a nontrivial automorphism of P of
odd order that leaves some maximal subgroup of P invariant. Then P needs 3 or 4 generators and φ has order 3.

Source: D. A. Craven and A. Glesser, Fusion systems on small p-groups, Trans. Amer. Math. Soc. 364 (2012),
5945–5967, Lemma 6.11. https://doi.org/10.1090/S0002-9947-2012-05580-2 -/
theorem lemma_6_11 {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : CFSGOutside.Corpus.Open.twoRank P = 2) (φ : MulAut P) (hφ : φ ≠ 1) (hodd : Odd (orderOf φ))
    (hinv : ∃ M : Subgroup P, IsCoatom M ∧ M.map φ.toMonoidHom = M) :
    (Group.rank P = 3 ∨ Group.rank P = 4) ∧ orderOf φ = 3 :=
  CFSGOutside.CravenGlesser.lemma_6_11 hP hrank φ hφ hodd hinv

end CFSGOutsideClean.CravenGlesser
