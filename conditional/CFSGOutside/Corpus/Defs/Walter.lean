import CFSGOutside.Corpus.Defs.ElementaryAbelian
import CFSGOutside.Corpus.Defs.J1Models

/-!
# Copied corpus definitions: Walter's classification of groups with abelian Sylow `2`-subgroups

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` (`IsElementaryAbelian` is the existing copy `CFSGOutside.Corpus.IsElementaryAbelian`).

* Janko's group `J₁` as a subgroup of `GL₇(𝔽₁₁)` (`Open.walterJ1`) is the copy in `CFSGOutside.Corpus.Defs.J1Models`;
* `Walter.IsTypeL2`: `CFSG/Walter/Defs.lean` lines 15–18;
* `Walter.Ward.wardSign`, `Walter.Ward.ReeTypeHyp`, `ReeTypeHyp.q`: `CFSG/Walter/ReeOrder/Ward/Defs.lean`
  lines 13–41, the hypotheses of a group of Ree type (Ward 1966).
-/

open scoped MatrixGroups

namespace CFSGOutside.Corpus

namespace Walter

/-- `L ≅ PSL(2, q)` with `q = 2^f ≥ 4` or `q ≡ ±3 (mod 8)`, `q ≥ 5`. Copy of `CFSG.Walter.IsTypeL2`. -/
def IsTypeL2 (L : Type*) [Group L] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))) ∨
  (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f)))

namespace Ward

/-- Copy of `CFSG.Walter.Ward.wardSign`. -/
def wardSign (q : ℕ) : ℤ := if q % 8 = 3 then -1 else 1

/-- The hypotheses of a group of Ree type. Copy of `CFSG.Walter.Ward.ReeTypeHyp`. -/
structure ReeTypeHyp (G : Type) [Group G] [Finite G] where
  p : ℕ
  f : ℕ
  [fact_prime : Fact p.Prime]
  p_ne_two : p ≠ 2
  f_pos : 0 < f
  card_sylow : ∀ P : Sylow 2 G, Nat.card P = 8
  elementary_sylow : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P
  index_ne_two : ∀ N : Subgroup G, N.Normal → N.index ≠ 2
  J : G
  orderOf_J : orderOf J = 2
  L : Subgroup G
  le_centralizer : L ≤ Subgroup.centralizer ({J} : Set G)
  J_not_mem : J ∉ L
  centralizer_eq : Subgroup.centralizer ({J} : Set G) = Subgroup.zpowers J ⊔ L
  iso : L ≃* PSL(2, GaloisField p f)
  normalizer_le : ∀ R ∈ L, 2 * (orderOf R : ℤ) = p ^ f + wardSign (p ^ f) →
    ∀ R₀ ∈ Subgroup.zpowers R, R₀ ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers R₀ : Set G) ≤ Subgroup.centralizer ({J} : Set G)
  not_commute : ∀ J' ∈ L, orderOf J' = 2 →
    ∀ S ∈ L, 4 * (orderOf S : ℤ) = p ^ f - wardSign (p ^ f) → S * J' = J' * S →
      ∀ A : G, orderOf A = 3 →
        A ∈ Subgroup.normalizer (Subgroup.closure ({J, J'} : Set G) : Set G) → A * S ≠ S * A

attribute [instance] ReeTypeHyp.fact_prime

/-- Copy of `CFSG.Walter.Ward.ReeTypeHyp.q`. -/
def ReeTypeHyp.q {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G) : ℕ := h.p ^ h.f

end Ward

end Walter

end CFSGOutside.Corpus
