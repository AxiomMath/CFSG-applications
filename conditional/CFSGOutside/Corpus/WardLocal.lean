import CFSGOutside.Corpus.Defs.Walter

/-!
# Corpus input: Ward's local structure of groups of Ree type

Statements of three corpus theorems at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, copied
verbatim (with the section variables `{G : Type} [Group G] [Finite G]`); `ReeTypeHyp`, `ReeTypeHyp.q` and
`IsElementaryAbelian` are the copies in `CFSGOutside.Corpus`.

* `CFSG.Walter.Ward.ward_order`, `CFSG/Walter/ReeOrder/Ward/Order.lean` line 31: `|G| = q³(q³ + 1)(q − 1)` with
  `q = 3^(2k+1)`, `k ≥ 1`;
* `CFSG.Walter.WardLocal.ward_two_three`, `CFSG/Walter/ReeOrder/WardLocal/Statements.lean` line 31: the Sylow
  `3`-normalizer `N(P) = P W`, `W` cyclic of order `q − 1`, whose involutions centralize no nonidentity element of
  `Z(P)`;
* `CFSG.Walter.WardLocal.ward_four`, `CFSG/Walter/ReeOrder/WardLocal/Four.lean` line 51: the abelian Hall subgroups
  `M±` of orders `q + 1 ± 3^(k+1)` with `N(M±) = M± W±`, `W±` cyclic of order `6` acting fixed-point-freely.
-/

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSGOutside.Corpus

open Walter.Ward

/-- The order of a group of Ree type, as `CFSG.Walter.Ward.ward_order` states it. -/
class WardOrder : Prop where
  ward_order : ∀ {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G),
    (∃ k ≥ 1, h.q = 3 ^ (2 * k + 1)) ∧ Nat.card G = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1)

/-- Ward's Sylow `3`-subgroup structure, as `CFSG.Walter.WardLocal.ward_two_three` states it. -/
class WardTwoThree : Prop where
  ward_two_three : ∀ {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) (P : Sylow 3 G),
    let Pg : Subgroup G := P
    let Z : Subgroup G := (Subgroup.center Pg).map Pg.subtype
    Nat.card Pg = h.q ^ 3 ∧
    (∀ g : G, Pg ⊓ (MulAut.conj g • Pg) = ⊥ ∨ Pg ⊓ (MulAut.conj g • Pg) = Pg) ∧
    IsElementaryAbelian 3 Z ∧ Nat.card Z = h.q ∧
    ∃ P₁ W : Subgroup G,
      P₁ ≤ Pg ∧ Pg ≤ Subgroup.normalizer (P₁ : Set G) ∧ IsElementaryAbelian 3 P₁ ∧
      Nat.card P₁ = h.q ^ 2 ∧ Z ≤ P₁ ∧
      (∀ x ∈ P₁, x ∉ Z → Pg ⊓ Subgroup.centralizer ({x} : Set G) = P₁) ∧
      IsCyclic W ∧ Nat.card W = h.q - 1 ∧ Pg ⊓ W = ⊥ ∧
      Subgroup.normalizer (Pg : Set G) = Pg ⊔ W ∧
      (∀ t ∈ W, orderOf t = 2 →
        Pg ⊓ Subgroup.centralizer ({t} : Set G) = P₁ ⊓ Subgroup.centralizer ({t} : Set G) ∧
        IsElementaryAbelian 3 (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ∧
        Nat.card (Pg ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = h.q ∧
        Pg ⊓ Subgroup.centralizer ({t} : Set G) ⊓ Z = ⊥) ∧
      ∀ R ∈ W, orderOf R = (h.q - 1) / 2 → ∀ R'' ∈ Subgroup.zpowers R, R'' ≠ 1 →
        Pg ⊓ Subgroup.centralizer ({R''} : Set G) = ⊥

/-- Ward's Hall subgroups `M±`, as `CFSG.Walter.WardLocal.ward_four` states it. -/
class WardFour : Prop where
  ward_four : ∀ {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) {k : ℕ} (_hq : h.q = 3 ^ (2 * k + 1)),
    h.q ^ 2 - h.q + 1 = (h.q + 1 + 3 * 3 ^ k) * (h.q + 1 - 3 * 3 ^ k) ∧
    ∀ s : Bool, ∃ M W : Subgroup G,
      IsMulCommutative M ∧
      Nat.card M = (if s then h.q + 1 + 3 * 3 ^ k else h.q + 1 - 3 * 3 ^ k) ∧
      Nat.Coprime (Nat.card M) M.index ∧
      (∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) ∧
      (∀ g : G, M ⊓ (MulAut.conj g • M) = ⊥ ∨ M ⊓ (MulAut.conj g • M) = M) ∧
      IsCyclic W ∧ Nat.card W = 6 ∧ M ⊓ W = ⊥ ∧
      Subgroup.normalizer (M : Set G) = M ⊔ W ∧
      ∀ w ∈ W, w ≠ 1 → M ⊓ Subgroup.centralizer ({w} : Set G) = ⊥

end CFSGOutside.Corpus
