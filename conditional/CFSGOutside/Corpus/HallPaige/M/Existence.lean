import Mathlib
import CFSGOutside.Corpus.HallPaige.M.Blueprint.NativeSporadic
import CFSGOutside.Corpus.HallPaige.M.Blueprint.FischerDefs
import CFSGOutside.Corpus.HallPaige.M.Foundations.Basic
import CFSGOutside.Corpus.HallPaige.M.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
import CFSGOutside.Corpus.HallPaige.M.Open.MonsterDefs

/-!
# The Monster existence statement over abstract Lie-type and elementary-abelian predicates

The group-theoretic predicates of `CFSG/Monster/Existence/Defs.lean` (AxiomMath/CFSG @ 69cb972), copied
verbatim except that the corpus predicates `LieModel` (`CFSG/Blueprint/Catalog.lean`) and
`IsElementaryAbelian` (`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/ElementaryAbelian.lean`) are parameters.
Their corpus definitions rest on the corpus Chevalley-group and class types, which a copy cannot equate
with the originals; the Hall–Paige proof never unfolds them. `StatedLieTag` is the corpus enumeration of
the Lie types, copied verbatim (`CFSG/Open/StatedDefs.lean`).
-/

namespace CFSGOutside.Corpus.M.Open

/-- Corpus: `CFSG.Open.StatedLieTag`, CFSG/Open/StatedDefs.lean:12. -/
inductive StatedLieTag
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits
  deriving DecidableEq

end CFSGOutside.Corpus.M.Open

namespace CFSGOutside.Corpus.M.Monster.Existence

open CFSGOutside.Corpus.M CFSGOutside.Corpus.M.Blueprint

/-- Corpus: `CFSG.Monster.Existence.twoBCentralizerOrder`, CFSG/Monster/Existence/Defs.lean:16. -/
def twoBCentralizerOrder : ℕ := 2 ^ 46 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23

/-- Corpus: `CFSG.Monster.Existence.suborbitClassOrder`, CFSG/Monster/Existence/Defs.lean:18. -/
def suborbitClassOrder : Fin 9 → ℕ := ![1, 2, 2, 3, 3, 4, 4, 5, 6]

variable (LieModel : ∀ (X : Type) [Group X], CFSGOutside.Corpus.M.Open.StatedLieTag → ℕ → ℕ → ℕ → Prop)
  (IsElementaryAbelian : ℕ → ∀ (X : Type) [Group X], Prop)

variable {G : Type} [Group G]

/-- Corpus: `CFSG.Monster.Existence.cent`, CFSG/Monster/Existence/Defs.lean:22. -/
abbrev cent (x : G) : Subgroup G := Subgroup.centralizer {x}

/-- Corpus: `CFSG.Monster.Existence.cent2`, CFSG/Monster/Existence/Defs.lean:24. -/
abbrev cent2 (α β : G) : Subgroup G := cent α ⊓ cent β

/-- Corpus: `CFSG.Monster.Existence.pointStab`, CFSG/Monster/Existence/Defs.lean:26. -/
abbrev pointStab (s : Set G) : Subgroup G := ⨅ x ∈ s, cent x

/-- Corpus: `CFSG.Monster.Existence.conjSet`, CFSG/Monster/Existence/Defs.lean:28. -/
def conjSet (g : G) (s : Set G) : Set G := (fun x => g * x * g⁻¹) '' s

/-- Corpus: `CFSG.Monster.Existence.HasTwoShape`, CFSG/Monster/Existence/Defs.lean:30. -/
def HasTwoShape (H : Subgroup G) (k : ℕ) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), Nat.card N = 2 ^ k ∧ P (H ⧸ N)

/-- Corpus: `CFSG.Monster.Existence.HasLayeredTwoShape`, CFSG/Monster/Existence/Defs.lean:33. -/
def HasLayeredTwoShape (H : Subgroup G) (a b : ℕ) (P : ∀ (X : Type) [Group X], Prop) :
    Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal) (N₀ : Subgroup H) (_ : N₀.Normal), N₀ ≤ N ∧
    IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ a ∧
    IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (a + b) ∧ P (H ⧸ N)

/-- Corpus: `CFSG.Monster.Existence.TwoPointShape`, CFSG/Monster/Existence/Defs.lean:39. -/
def TwoPointShape (H : Subgroup G) : Fin 9 → Prop
  | 0 => HasTwoShape H 1 fun X _ => Nonempty (X ≃* NativeSporadic.B)
  | 1 => ∃ (N : Subgroup H) (_ : N.Normal), IsElementaryAbelian 2 N ∧ Nat.card N = 2 ^ 2 ∧
      LieModel (H ⧸ N) .twistedE6 0 2 1
  | 2 => HasLayeredTwoShape IsElementaryAbelian H 2 22 fun X _ => Nonempty (X ≃* NativeSporadic.Co2)
  | 3 => Nonempty (H ≃* NativeSporadic.Fi23)
  | 4 => Nonempty (H ≃* NativeSporadic.Th)
  | 5 => ∃ (N : Subgroup H) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧ Nat.card N = 2 ^ 23 ∧
      Nonempty (H ⧸ N ≃* NativeSporadic.McL)
  | 6 => HasTwoShape H 1 fun X _ => LieModel X .F4 0 2 1
  | 7 => Nonempty (H ≃* NativeSporadic.HN)
  | 8 => HasTwoShape H 1 fun X _ => Nonempty (X ≃* NativeSporadic.Fi22)

/-- Corpus: `CFSG.Monster.Existence.IsTwoACentralizer`, CFSG/Monster/Existence/Defs.lean:52. -/
def IsTwoACentralizer (a : G) : Prop :=
  Group.IsPerfect (cent a) ∧ (Subgroup.center (cent a)).map (cent a).subtype = Subgroup.zpowers a ∧
    Nonempty (cent a ⧸ Subgroup.center (cent a) ≃* NativeSporadic.B)

/-- Corpus: `CFSG.Monster.Existence.IsTwoBCentralizer`, CFSG/Monster/Existence/Defs.lean:56. -/
def IsTwoBCentralizer (z : G) : Prop :=
  IsExtraspecialPGroup 2 (pCore 2 (cent z)) ∧ Nat.card (pCore 2 (cent z)) = 2 ^ 25 ∧
    Subgroup.centralizer (inSubgroup (pCore 2) (cent z) : Set G) ≤ inSubgroup (pCore 2) (cent z) ∧
    Nonempty (cent z ⧸ pCore 2 (cent z) ≃* NativeSporadic.Co1) ∧
    Nat.card (cent z) = twoBCentralizerOrder ∧ ¬ 17 ∣ Nat.card (cent z)

/-- Corpus: `CFSG.Monster.Existence.IsTriangle`, CFSG/Monster/Existence/Defs.lean:62. -/
def IsTriangle (a : G) (s : Set G) : Prop :=
  s.ncard = 3 ∧ (∀ x ∈ s, IsConj a x) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsConj a (x * y)

/-- Corpus: `CFSG.Monster.Existence.IsShortTriangle`, CFSG/Monster/Existence/Defs.lean:65. -/
def IsShortTriangle (a : G) (s : Set G) : Prop :=
  IsTriangle a s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x * y ∈ s

/-- Corpus: `CFSG.Monster.Existence.IsLongTriangle`, CFSG/Monster/Existence/Defs.lean:68. -/
def IsLongTriangle (a : G) (s : Set G) : Prop :=
  IsTriangle a s ∧ ¬ IsShortTriangle a s

/-- Corpus: `CFSG.Monster.Existence.IsTwoAGraphData`, CFSG/Monster/Existence/Defs.lean:71. -/
def IsTwoAGraphData (a z : G) : Prop :=
  (∀ α β β' : G, IsConj a α → IsConj a β → IsConj a β' → IsConj (α * β) (α * β') →
    ∃ g ∈ cent α, g * β * g⁻¹ = β') ∧
  ∃ c : Fin 9 → G,
    (∀ i j, IsConj (c i) (c j) → i = j) ∧ c 0 = 1 ∧ IsConj a (c 1) ∧ IsConj z (c 2) ∧
    (∀ i, orderOf (c i) = suborbitClassOrder i) ∧
    (∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i)) ∧
    (∀ i, ∃ α β : G, IsConj a α ∧ IsConj a β ∧ IsConj (α * β) (c i)) ∧
    (∀ (α β : G) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape LieModel IsElementaryAbelian (cent2 α β) i) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 3) →
      (∃ γ, IsConj a γ ∧ IsConj (α * γ) (c 3) ∧ IsConj a (β * γ)) ∧
      (∀ γ γ', IsConj a γ → IsConj (α * γ) (c 3) → IsConj a (β * γ) →
        IsConj a γ' → IsConj (α * γ') (c 3) → IsConj a (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj a γ → IsConj (α * γ) (c 3) → IsConj a (β * γ) →
        LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 6) →
      α ≠ β ∧ ¬ IsConj a (α * β) ∧
        ∃! γ, IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (γ * β)) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 3) →
      (∃ D : Set ↥(cent2 α β), CFSGOutside.Corpus.M.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
        {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} =
          Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} = 31671) ∧
    (∃ s₁ s₂ : Set G, IsTriangle a s₁ ∧ IsTriangle a s₂ ∧ (∀ g : G, conjSet g s₁ ≠ s₂) ∧
      ∀ s, IsTriangle a s → ∃ g : G, conjSet g s = s₁ ∨ conjSet g s = s₂) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      {s | IsShortTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 1 ∧
      {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 3968055) ∧
    (∀ s, IsLongTriangle a s →
      LieModel (pointStab s ⧸ pCore 2 (pointStab s)) .PSU 6 2 1 ∧
      HasLayeredTwoShape IsElementaryAbelian (pointStab s) 3 20 fun X _ => LieModel X .PSU 6 2 1) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      ∃ γ δ : G, IsLongTriangle a {α, β, γ} ∧ IsConj a δ ∧ IsConj (α * δ) (c 3) ∧
        IsConj (β * δ) (c 3) ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1)

/-- Corpus: `CFSG.Monster.Existence.MonsterExistenceStatement`, CFSG/Monster/Existence/Defs.lean:112. -/
def MonsterExistenceStatement (G : Type) [Group G] : Prop :=
  (Finite G ∧ IsSimpleGroup G ∧ (∃ x y : G, x * y ≠ y * x) ∧ Nat.card G = CFSGOutside.Corpus.M.Open.monsterOrder) ∧
  ∃ a z : G, orderOf a = 2 ∧ orderOf z = 2 ∧ ¬ IsConj a z ∧
    (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧
    (∀ α, IsConj a α → IsTwoACentralizer α) ∧
    (∀ ζ, IsConj z ζ → IsTwoBCentralizer ζ) ∧
    IsTwoAGraphData LieModel IsElementaryAbelian a z


end CFSGOutside.Corpus.M.Monster.Existence
