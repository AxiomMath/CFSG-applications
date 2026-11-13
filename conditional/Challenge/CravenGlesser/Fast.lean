import CFSGOutside.Corpus.Defs.TwoRank
import CFSGOutside.Corpus.MacWilliamsFourGenerator

/-!
# Craven–Glesser, Lemma 6.11

D. A. Craven and A. Glesser, *Fusion systems on small p-groups*, Trans. Amer. Math. Soc. 364 (2012),
5945–5967, DOI 10.1090/S0002-9947-2012-05580-2, Lemma 6.11. Let `P` be a finite 2-group of 2-rank 2 with a
nontrivial odd-order automorphism `φ`. If `P` has a `φ`-invariant maximal subgroup, then `P` is 3-generator
or 4-generator and `o(φ) = 3`.
Conditional on the corpus input stated as a class in `CFSGOutside.Corpus`.
-/

theorem CFSGOutside.CravenGlesser.lemma_6_11 [CFSGOutside.Corpus.MacWilliamsFourGenerator] {P : Type}
    [Group P] [Finite P] (hP : IsPGroup 2 P) (hrank : CFSGOutside.Corpus.Open.twoRank P = 2)
    (φ : MulAut P) (hφ : φ ≠ 1) (hodd : Odd (orderOf φ))
    (hinv : ∃ M : Subgroup P, IsCoatom M ∧ M.map φ.toMonoidHom = M) :
    (Group.rank P = 3 ∨ Group.rank P = 4) ∧ orderOf φ = 3 := sorry
