import Mathlib

/-!
# Copied corpus definitions: the model of the small Ree groups `²G₂(3^f)`

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The copies are:

* `Open.StatedLieTag`, `Open.StatedLieAdmissible` from `CFSG/Open/StatedDefs.lean`;
* `Blueprint.Chevalley.Tag` to `Blueprint.Chevalley.adjointGroup`, the Chevalley adjoint groups built from root
  data, from `CFSG/Blueprint/Chevalley.lean`; only the declarations `ReeTitsModel` depends on are copied;
* `Blueprint.DerivedCentralQuotient` to `Blueprint.ReeTitsModel` from `CFSG/Blueprint/Catalog.lean`.

`Blueprint.ReeTitsModel G .twistedG2 3 f` says that `G` is isomorphic to the small Ree group `²G₂(3^f)`, built
as the derived group modulo its centre of the fixed points of the Steinberg endomorphism of `G₂(𝔽_{3^f})`.
The clean build proves the copy equivalent to the corpus original in
`clean/CFSGOutsideClean/Corpus/Defs/ReeModel.lean`.
-/

namespace CFSGOutside.Corpus

namespace Open

/-- Types of finite simple groups of Lie type. Copy of `CFSG.Open.StatedLieTag`,
`CFSG/Open/StatedDefs.lean` line 12. -/
inductive StatedLieTag
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits
  deriving DecidableEq

/-- The parameters `(n, p, f)` for which the type `t` is admissible. Copy of `CFSG.Open.StatedLieAdmissible`,
`CFSG/Open/StatedDefs.lean` line 18. -/
def StatedLieAdmissible (t : StatedLieTag) (n p f : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ f ∧
  match t with
  | .PSL => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2) ∧ (n, p ^ f) ≠ (2, 3)
  | .PSU => 3 ≤ n ∧ (n, p ^ f) ≠ (3, 2)
  | .PSp => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2)
  | .POmegaOdd => 3 ≤ n ∧ p ≠ 2
  | .POmegaPlus => 4 ≤ n
  | .POmegaMinus => 4 ≤ n
  | .G2 => n = 0 ∧ 3 ≤ p ^ f
  | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 => n = 0
  | .twistedB2 | .twistedF4 => n = 0 ∧ p = 2 ∧ Odd f ∧ 3 ≤ f
  | .twistedG2 => n = 0 ∧ p = 3 ∧ Odd f ∧ 3 ≤ f
  | .Tits => n = 0 ∧ p = 2 ∧ f = 1

end Open

noncomputable section

namespace Blueprint

namespace Chevalley

/-- Types of root data. Copy of `CFSG.Blueprint.Chevalley.Tag`, `CFSG/Blueprint/Chevalley.lean` line 9. -/
inductive Tag
  | G2 | F4 | D4 | E6 | E7 | E8
  deriving DecidableEq, Repr

namespace Tag

/-- The rank of a root datum. Copy of `CFSG.Blueprint.Chevalley.Tag.rank`,
`CFSG/Blueprint/Chevalley.lean` line 15. -/
def rank : Tag → ℕ
  | G2 => 2
  | F4 => 4
  | D4 => 4
  | E6 => 6
  | E7 => 7
  | E8 => 8

/-- The Cartan matrix of type `E`. Copy of `CFSG.Blueprint.Chevalley.Tag.cartanE`,
`CFSG/Blueprint/Chevalley.lean` line 23. -/
def cartanE (r : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j =>
    if i = j then 2
    else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨
        (i.val = 3 ∧ j.val = 1) ∨ (2 ≤ i.val ∧ j.val = i.val + 1) ∨
        (2 ≤ j.val ∧ i.val = j.val + 1) then -1
    else 0

/-- The Cartan matrix of a root datum. Copy of `CFSG.Blueprint.Chevalley.Tag.cartan`,
`CFSG/Blueprint/Chevalley.lean` line 31. -/
def cartan : (τ : Tag) → Matrix (Fin τ.rank) (Fin τ.rank) ℤ
  | G2 => !![2, -1; -3, 2]
  | F4 => !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]
  | D4 => !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2]
  | E6 => cartanE 6
  | E7 => cartanE 7
  | E8 => cartanE 8

end Tag

/-- The simple reflection `i` acting on `ℤ^rank`. Copy of `CFSG.Blueprint.Chevalley.reflect`,
`CFSG/Blueprint/Chevalley.lean` line 52. -/
def reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  v - (∑ j, τ.cartan i j * v j) • Pi.single i 1

/-- The roots: the Weyl orbit of the simple roots. Copy of `CFSG.Blueprint.Chevalley.IsRoot`,
`CFSG/Blueprint/Chevalley.lean` line 55. -/
inductive IsRoot (τ : Tag) : (Fin τ.rank → ℤ) → Prop
  | basis (j : Fin τ.rank) : IsRoot τ (Pi.single j 1)
  | reflect (i : Fin τ.rank) {v : Fin τ.rank → ℤ} : IsRoot τ v → IsRoot τ (reflect τ i v)

/-- Basis labels of the adjoint module: the Cartan part and the roots. Copy of
`CFSG.Blueprint.Chevalley.Label`, `CFSG/Blueprint/Chevalley.lean` line 62. -/
abbrev Label (τ : Tag) : Type :=
  Fin τ.rank ⊕ {v : Fin τ.rank → ℤ // IsRoot τ v}

/-- The adjoint module over `R`. Copy of `CFSG.Blueprint.Chevalley.RootModule`,
`CFSG/Blueprint/Chevalley.lean` line 65. -/
abbrev RootModule (τ : Tag) (R : Type*) [CommRing R] : Type _ :=
  Label τ →₀ R

variable (τ : Tag) (R : Type*) [CommRing R]

/-- Basis vector of the Cartan part. Copy of `CFSG.Blueprint.Chevalley.hVec`,
`CFSG/Blueprint/Chevalley.lean` line 82. -/
def hVec (i : Fin τ.rank) : RootModule τ R :=
  Finsupp.single (Sum.inl i) 1

open Classical in
/-- Basis vector of a root, or `0` if the vector is not a root. Copy of `CFSG.Blueprint.Chevalley.rootVec`,
`CFSG/Blueprint/Chevalley.lean` line 86. -/
def rootVec (β : Fin τ.rank → ℤ) : RootModule τ R :=
  if h : IsRoot τ β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

/-- The length of the `α`-string up. Copy of `CFSG.Blueprint.Chevalley.stringUp`,
`CFSG/Blueprint/Chevalley.lean` line 89. -/
def stringUp (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | IsRoot τ (α + (k : ℤ) • Pi.single i 1)}

/-- The length of the `α`-string down. Copy of `CFSG.Blueprint.Chevalley.stringDown`,
`CFSG/Blueprint/Chevalley.lean` line 92. -/
def stringDown (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | IsRoot τ (α - (k : ℤ) • Pi.single i 1)}

open Classical in
/-- The root element `x_i(c)` acting on the adjoint module. Copy of `CFSG.Blueprint.Chevalley.xOp`,
`CFSG/Blueprint/Chevalley.lean` line 96. -/
def xOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1)
    | .inr α =>
      if α.1 = Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = -Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringUp τ i α.1 + 1),
          (((stringDown τ i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ R (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
/-- The root element `y_i(c)` acting on the adjoint module. Copy of `CFSG.Blueprint.Chevalley.yOp`,
`CFSG/Blueprint/Chevalley.lean` line 110. -/
def yOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1)
    | .inr α =>
      if α.1 = -Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringDown τ i α.1 + 1),
          (((stringUp τ i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ R (α.1 - (k : ℤ) • Pi.single i 1)

/-- Automorphisms of the adjoint module. Copy of `CFSG.Blueprint.Chevalley.ModGL`,
`CFSG/Blueprint/Chevalley.lean` line 123. -/
abbrev ModGL (K : Type*) [Field K] : Type _ :=
  LinearMap.GeneralLinearGroup K (RootModule τ K)

/-- The adjoint Chevalley group over `K`. Copy of `CFSG.Blueprint.Chevalley.adjointGroup`,
`CFSG/Blueprint/Chevalley.lean` line 126. -/
def adjointGroup (K : Type*) [Field K] : Subgroup (ModGL τ K) :=
  Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}

end Chevalley

open Chevalley

/-- The derived subgroup modulo its centre. Copy of `CFSG.Blueprint.DerivedCentralQuotient`,
`CFSG/Blueprint/Catalog.lean` line 26. -/
abbrev DerivedCentralQuotient {M : Type} [Group M] (H : Subgroup M) : Type :=
  ↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆

/-- Pairs `(g, h)` with `h` the image of `g` under the Steinberg endomorphism. Copy of
`CFSG.Blueprint.reeRelationGroup`, `CFSG/Blueprint/Catalog.lean` line 55. -/
def reeRelationGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K × ModGL τ K) :=
  Subgroup.closure {gh | ∃ (i : Fin τ.rank) (c : K),
    ((gh.1 : Module.End K (RootModule τ K)) = xOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = xOp τ K (ρ i) (c ^ e i)) ∨
      ((gh.1 : Module.End K (RootModule τ K)) = yOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = yOp τ K (ρ i) (c ^ e i))}

/-- The fixed points of the Steinberg endomorphism in the adjoint group. Copy of
`CFSG.Blueprint.reeFixedGroup`, `CFSG/Blueprint/Catalog.lean` line 63. -/
def reeFixedGroup (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ (reeRelationGroup τ K ρ e).comap ((MonoidHom.id _).prod (MonoidHom.id _))

/-- The graph automorphism of the `G₂` diagram. Copy of `CFSG.Blueprint.reeG2Perm`,
`CFSG/Blueprint/Catalog.lean` line 67. -/
def reeG2Perm : Equiv.Perm (Fin Tag.G2.rank) :=
  (Equiv.swap 0 1 : Equiv.Perm (Fin 2))

/-- The graph automorphism of the `F₄` diagram. Copy of `CFSG.Blueprint.reeF4Perm`,
`CFSG/Blueprint/Catalog.lean` line 70. -/
def reeF4Perm : Equiv.Perm (Fin Tag.F4.rank) :=
  (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))

/-- The long simple roots of `G₂`. Copy of `CFSG.Blueprint.reeG2Long`,
`CFSG/Blueprint/Catalog.lean` line 73. -/
def reeG2Long : Finset (Fin Tag.G2.rank) :=
  ({0} : Finset (Fin 2))

/-- The long simple roots of `F₄`. Copy of `CFSG.Blueprint.reeF4Long`,
`CFSG/Blueprint/Catalog.lean` line 76. -/
def reeF4Long : Finset (Fin Tag.F4.rank) :=
  ({0, 1} : Finset (Fin 4))

/-- `G` is the group of fixed points of the Steinberg endomorphism, in the derived-modulo-centre form. Copy of
`CFSG.Blueprint.ReeTitsRelationModel`, `CFSG/Blueprint/Catalog.lean` line 79. -/
def ReeTitsRelationModel (G : Type) [Group G] (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
    Nonempty (G ≃* DerivedCentralQuotient
      (reeFixedGroup τ K ρ fun i => if i ∈ L then p ^ a else p ^ (a + 1)))

/-- `G` is isomorphic to the Ree or Tits group of type `t` over `𝔽_{p^f}`; for `t = .twistedG2` and `p = 3` it is
the small Ree group `²G₂(3^f)`. Copy of `CFSG.Blueprint.ReeTitsModel`, `CFSG/Blueprint/Catalog.lean`
line 85. -/
def ReeTitsModel (G : Type) [Group G] (t : Open.StatedLieTag) (p f : ℕ) : Prop :=
  Open.StatedLieAdmissible t 0 p f ∧ ∃ a : ℕ, f = 2 * a + 1 ∧
    match t with
    | .twistedG2 => ReeTitsRelationModel G .G2 reeG2Perm reeG2Long p f a
    | .twistedF4 => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | .Tits => ReeTitsRelationModel G .F4 reeF4Perm reeF4Long p f a
    | _ => False

end Blueprint

end

end CFSGOutside.Corpus
