import CFSGOutside.Gagola.FullyRamified
import CFSGOutside.Corpus.WalterSplit
import CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutside.Corpus.CardWalterJ1
import CFSGOutside.Corpus.GorensteinWalter
import CFSGOutside.Corpus.BrauerSuzukiQuaternion
import CFSGOutside.Corpus.Order8Nonabelian
import CFSGOutside.Corpus.RankTwoSylowShapes
import CFSGOutside.Corpus.HoltAtMostOneInvolution
import CFSGOutside.Corpus.CardStatedClassicalModelTwo
import CFSGOutside.Corpus.Gh74SectionalTwoRankFour
import CFSGOutside.Corpus.YoshidaTransfer
import CFSGOutside.Corpus.ASevenOrExistsNormalPsl2
import CFSGOutside.Corpus.CardMulAutPsl2GF
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy

/-!
# Gagola, Theorem 4.5 (fast path)

S. M. Gagola, *Characters fully ramified over a normal subgroup*, Pacific J. Math. 55 (1974), 107–126,
Theorem 4.5: *Let `G` be a group of type f.r. Assume that `G` has an abelian Sylow `p`-subgroup for every
prime `p` satisfying `p⁶ ∣ |G|`. Then `G` is solvable.* Conditional on the corpus theorems stated as classes
in `CFSGOutside.Corpus`. `FullyRamified` and `IsTypeFR` are in `CFSGOutside.Gagola.FullyRamified`.
-/

namespace CFSGOutside.Gagola

open CFSGOutside.Corpus

theorem theorem_4_5 [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour] [YoshidaTransfer.{0}] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy]
    {G : Type} [Group G] (hG : IsTypeFR G)
    (hS : ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card G → ∃ P : Sylow p G, IsMulCommutative (P : Subgroup G)) :
    Group.IsSolvable G := sorry

end CFSGOutside.Gagola
