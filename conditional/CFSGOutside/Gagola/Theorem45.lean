import CFSGOutside.Gagola.Perfect
import CFSGOutside.Gagola.Lemma44
import CFSGOutside.Gagola.Split
import CFSGOutside.Gagola.T45Defs
import CFSGOutside.Gagola.T45Sylow
import CFSGOutside.Gagola.T45Perfect
import CFSGOutside.Gagola.T45Solvable

/-!
# Gagola, Theorem 4.5

*Let `G` be a group of type f.r. Assume that `G` has an abelian Sylow `p`-subgroup for every prime `p` with
`p ^ 6 ∣ |G|`. Then `G` is solvable.*

Proof by strong induction on `|H/Z|` over fully ramified triples `(H, Z, χ)`.
* If `H/Z` is perfect and nontrivial, it has a nonabelian simple quotient `H/K`, and `perfect_step` gives a
  contradiction (the nonabelian Sylow 2-subgroups of `H/Z` have order `16` by the square-order lemma).
* Otherwise take `K ⊇ Z` normal, minimal such that `H/K` is a nontrivial `p`-group. Then `K/Z` has no
  nontrivial `p`-group quotient, and `uniqueness_of_K` (Corollary 3.6 or Lemma 4.4) shows that `χ_K` has a
  single constituent, so `(K, Z, τ)` is fully ramified (`fr_split`) and we conclude by induction.
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus

noncomputable section

theorem solvable_aux [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour] [YoshidaTransfer.{0}] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy] :
    ∀ n : ℕ, ∀ (H : Type) [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal] (χ : H → ℂ),
      FullyRamified Z χ → SylowAb (H ⧸ Z) → Nat.card (H ⧸ Z) = n → Group.IsSolvable (H ⧸ Z) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ Z _ χ hfr hS hn
    by_cases hperf : commutator (H ⧸ Z) = ⊤
    · by_cases hnt : Nontrivial (H ⧸ Z)
      · exact (perfect_false hfr hperf hnt (h16_of_sylowAb hfr hS)).elim
      · haveI : Subsingleton (H ⧸ Z) := not_nontrivial_iff_subsingleton.mp hnt
        infer_instance
    · obtain ⟨p, hp, K, hKn, hZK, hKne, hKp, hno⟩ := exists_minimal_K Z hperf
      have huniq := uniqueness_of_K hfr hS K hZK hKne hKp hno
      obtain ⟨-, τ, hτ⟩ := fr_split hfr K hZK huniq
      have hlt := card_sub_lt Z K hZK hKne
      have hsol := ih (Nat.card (K ⧸ Z.subgroupOf K)) (hn ▸ hlt) K (Z.subgroupOf K) τ hτ
        (sylowAb_sub Z K hS hZK) rfl
      exact solvable_of_sub_and_quot Z K hZK hsol hKp

/-- **Gagola, Theorem 4.5.** A group of type f.r. with an abelian Sylow `p`-subgroup for every prime `p`
with `p ^ 6 ∣ |G|` is solvable. -/
theorem gagola_4_5 [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour] [YoshidaTransfer.{0}] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy]
    {G : Type} [Group G] (hG : IsTypeFR G)
    (hS : ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card G → ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G)) :
    Group.IsSolvable G := by
  obtain ⟨H, _, _, Z, hZ, χ, hfr, ⟨eG⟩⟩ := hG
  haveI : Finite G := Finite.of_equiv _ eG.symm.toEquiv
  have hS' : SylowAb (H ⧸ Z) := sylowAb_of_equiv eG.symm hS
  haveI := solvable_aux _ H Z χ hfr hS' rfl
  exact solvable_of_equiv eG

end

end CFSGOutside.Gagola

namespace CFSGOutside.Gagola

open CFSGOutside.Corpus

/-- **Fully ramified characters.** Call a finite group G of type f.r. if G ≅ H/Z, where Z is a normal subgroup of a
finite group H that carries a complex irreducible character χ fully ramified over Z, meaning that the restriction of
χ to Z is e·θ for an irreducible character θ of Z with e² = |H : Z|. If G is of type f.r. and G has an abelian Sylow
p-subgroup for every prime p with p⁶ dividing |G|, then G is solvable.

Source: S. M. Gagola, Jr., Characters fully ramified over a normal subgroup, Pacific J. Math. 55 (1974), 107–126,
Theorem 4.5. https://doi.org/10.2140/pjm.1974.55.107

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_4_5 [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour] [YoshidaTransfer.{0}] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy]
    {G : Type} [Group G] (hG : IsTypeFR G)
    (hS : ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card G → ∃ P : Sylow p G, IsMulCommutative (P : Subgroup G)) :
    Group.IsSolvable G := by
  have hG' := hG
  obtain ⟨H, _, _, Z, _, χ, -, ⟨eG⟩⟩ := hG'
  haveI : Finite G := Finite.of_equiv _ eG.symm.toEquiv
  refine gagola_4_5 hG ?_
  intro p hp h6 Q
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := hS p hp h6
  let e : (Q : Subgroup G) ≃* (P : Subgroup G) := Sylow.equiv Q P
  exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, hP.is_comm.comm])⟩⟩

end CFSGOutside.Gagola
