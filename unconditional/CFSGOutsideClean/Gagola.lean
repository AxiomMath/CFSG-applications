import CFSGOutside.Gagola.Main
import CFSGOutside.Gagola.Theorem45
import CFSGOutsideClean.Corpus.WalterSplit
import CFSGOutsideClean.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutsideClean.Corpus.CardWalterJ1
import CFSGOutsideClean.Corpus.GorensteinWalter
import CFSGOutsideClean.Corpus.BrauerSuzukiQuaternion
import CFSGOutsideClean.Corpus.Order8Nonabelian
import CFSGOutsideClean.Corpus.RankTwoSylowShapes
import CFSGOutsideClean.Corpus.HoltAtMostOneInvolution
import CFSGOutsideClean.Corpus.CardStatedClassicalModelTwo
import CFSGOutsideClean.Corpus.Gh74SectionalTwoRankFour
import CFSGOutsideClean.Corpus.YoshidaTransfer
import CFSGOutsideClean.Corpus.ASevenOrExistsNormalPsl2
import CFSGOutsideClean.Corpus.CardMulAutPsl2GF
import CFSGOutsideClean.Corpus.SL2MinimalFaithfulZsigmondy

/-! Gagola (1974), *Characters fully ramified over a normal subgroup*, Theorem 4.5, with the 14 corpus
theorems it uses (Walter, Gorenstein–Walter, Brauer–Suzuki, Yoshida, Gorenstein–Harada, …) supplied by the
corpus. `FullyRamified` and `IsTypeFR` are in `CFSGOutside.Gagola.FullyRamified`. The two earlier results for
abelian Sylow 2-subgroups, which use Walter's theorem only, are kept below. -/

namespace CFSGOutsideClean.Gagola

open CFSGOutside.Gagola

/-- **Fully ramified characters.** Call a finite group G of type f.r. if G ≅ H/Z, where Z is a normal subgroup of a
finite group H that carries a complex irreducible character χ fully ramified over Z, meaning that the restriction of
χ to Z is e·θ for an irreducible character θ of Z with e² = |H : Z|. If G is of type f.r. and G has an abelian Sylow
p-subgroup for every prime p with p⁶ dividing |G|, then G is solvable.

Source: S. M. Gagola, Jr., Characters fully ramified over a normal subgroup, Pacific J. Math. 55 (1974), 107–126,
Theorem 4.5. https://doi.org/10.2140/pjm.1974.55.107 -/
theorem theorem_4_5 {G : Type} [Group G] (hG : IsTypeFR G)
    (hS : ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card G → ∃ P : Sylow p G, IsMulCommutative (P : Subgroup G)) :
    Group.IsSolvable G :=
  CFSGOutside.Gagola.theorem_4_5 hG hS

/-- If `(H, Z, χ)` is a fully ramified triple and `Z ≤ K ⊴ H`, then `H/K` is not a nonabelian simple group
with an abelian Sylow 2-subgroup. -/
theorem not_simple_quotient {H : Type} [Group H] [Fintype H] {Z : Subgroup H} {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    (hnonab : ∃ a b : H ⧸ K, a * b ≠ b * a) (P : Sylow 2 (H ⧸ K))
    (hP : IsMulCommutative (P : Subgroup (H ⧸ K))) : False :=
  CFSGOutside.Gagola.not_simple_quotient hfr K hZK hnonab P hP

/-- A perfect group of type f.r. with abelian Sylow 2-subgroups is trivial. -/
theorem typeFR_perfect {G : Type} [Group G] (hG : IsTypeFR G) (hperf : commutator G = ⊤)
    (hab : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) : Subsingleton G :=
  CFSGOutside.Gagola.typeFR_perfect hG hperf hab

end CFSGOutsideClean.Gagola
