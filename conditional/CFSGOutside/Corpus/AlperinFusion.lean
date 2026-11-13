import Mathlib

/-!
# Corpus input: Alperin's fusion theorem for a Sylow subgroup

Statement of `CFSG.RankTwoShapes.alperin_centric_radical_fusion`
(`CFSG/LocalAnalysis/RankTwoShapes/AlperinFusion.lean`, lines 341–344, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), with `IsAlperinSubgroup` (line 13) and
`AlperinDecomposition` (line 21) of the same file copied verbatim.

For a Sylow subgroup `S` of a finite group `G`, every conjugation `c_g : P → S` (`P ≤ S`) agrees on
`P` with a product of elements of normalizers `N_G(Q)` of "Alperin subgroups" `Q ≤ S` (fully
normalized, `C_S(Q) ≤ Q`, radical), applied successively to subgroups of the `Q`.
-/

namespace CFSGOutside.Corpus

variable {G : Type*} [Group G]

/-- `CFSG.RankTwoShapes.IsAlperinSubgroup`, verbatim. -/
def IsAlperinSubgroup (p : ℕ) (S Q : Subgroup G) : Prop :=
  Q ≤ S ∧
  Nat.Coprime p ((S ⊓ (Subgroup.normalizer (Q : Set G))).subgroupOf (Subgroup.normalizer (Q : Set G))).index ∧
  Subgroup.centralizer (Q : Set G) ⊓ S ≤ Q ∧
  ∀ R : Subgroup G, Q ⊔ Subgroup.centralizer (Q : Set G) ≤ R → R ≤ (Subgroup.normalizer (Q : Set G)) →
    (Subgroup.normalizer (Q : Set G)) ≤ (Subgroup.normalizer (R : Set G)) →
    (∃ k : ℕ, ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf R).index = p ^ k) →
    R = Q ⊔ Subgroup.centralizer (Q : Set G)

/-- `CFSG.RankTwoShapes.AlperinDecomposition`, verbatim. -/
inductive AlperinDecomposition (p : ℕ) (S P : Subgroup G) : G → Prop
  | one : AlperinDecomposition p S P 1
  | step {c n : G} {Q : Subgroup G} : AlperinDecomposition p S P c → IsAlperinSubgroup p S Q →
      P.map (MulAut.conj c⁻¹).toMonoidHom ≤ Q → n ∈ (Subgroup.normalizer (Q : Set G)) →
      AlperinDecomposition p S P (c * n)

/-- Alperin's fusion theorem, as `CFSG.RankTwoShapes.alperin_centric_radical_fusion` states it. -/
class AlperinFusion : Prop where
  alperin_centric_radical_fusion : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {P : Subgroup G} (_hP : P ≤ S) {g : G}
    (_hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S),
    ∃ c : G, AlperinDecomposition p (S : Subgroup G) P c ∧ ∀ x ∈ P, c⁻¹ * x * c = g⁻¹ * x * g

end CFSGOutside.Corpus
