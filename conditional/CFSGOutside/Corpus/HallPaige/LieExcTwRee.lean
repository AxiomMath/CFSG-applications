import CFSGOutside.Corpus.HallPaige.LieRankOneRee

/-!
# Corpus input for the large Ree groups `²F₄(q)`

On top of hp-rk1's copy of the Ree model (`CFSGOutside.Corpus.HallPaige.LieRankOneRee`: `ReeTag`,
`reeGamma`, `reeFixedBorel`, …) and hp-exc's Chevalley stack: the relative Weyl group
`relWeylRee`, the fixed orbit elements `z_j`, the monomial subgroup and Bruhat cells of
`reeGamma`, the standard parabolic subgroups of the ambient Chevalley group, and the corpus
theorems used for the Hall–Paige theorem.

All definitions are copied verbatim from AxiomMath/CFSG @ 69cb972 (only `@[expose]` and the
module-system keywords are dropped, and the names are put in the namespace
`CFSGOutside.Corpus.Ree`); each docstring gives the corpus name and file:line. Corpus theorems are
stated as classes whose fields are the corpus statements.
-/

set_option autoImplicit false

namespace CFSGOutside.Corpus.Ree

noncomputable section

open CFSGOutside.Corpus.Exc
open scoped Pointwise

/-! ### `CFSG/LieType/Chevalley/StandardParabolic.lean` -/

section
variable [h0 : Corpus.Ree.FiniteWeylGroup]
include h0

/-- Corpus: `CFSG.LieType.Chevalley.parabolicWeylGroup`,
CFSG/LieType/Chevalley/StandardParabolic.lean:12. -/
def parabolicWeylGroup
    (τ : Tag) (J : Set (Fin τ.rank)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure (simple τ '' J)

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.LieType.Chevalley.parabolicSubgroup`,
CFSG/LieType/Chevalley/StandardParabolic.lean:16. -/
def parabolicSubgroup
    (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank)) :
    Subgroup (Module.End K (RootModule τ K))ˣ :=
  borelGroup τ K ⊔ Subgroup.closure ((fun j => weylElt τ K j 1) '' J)

end

namespace ReeTag

/-! ### `CFSG/LieType/Ree/ShortModule.lean`, `EndoRoots.lean`, `RelWeylRee.lean` -/

section Weyl

variable {t : ReeTag}

/-- Corpus: CFSG/LieType/Ree/ShortModule.lean:152 (same proof). -/
theorem perm_perm (i : Fin t.tag.rank) : t.perm (t.perm i) = i := by
  cases t <;> revert i <;> decide

/-- Corpus: CFSG/LieType/Ree/EndoRoots.lean:49 (same proof). -/
theorem cartan_mul_cartan_perm (t : ReeTag) (i j : Fin t.tag.rank) :
    t.tag.cartan (t.perm i) (t.perm j) * t.tag.cartan (t.perm j) (t.perm i) =
      t.tag.cartan i j * t.tag.cartan j i := by
  revert i j
  cases t <;> decide

/-- Corpus: CFSG/LieType/Ree/EndoRoots.lean:55 (same proof). -/
theorem coxeterMatrix_perm (i j : Fin t.tag.rank) :
    (coxeterMatrix (isFiniteType_cartan t.tag)).M (t.perm i)
        (t.perm j) =
      (coxeterMatrix (isFiniteType_cartan t.tag)).M i j := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    cartan_mul_cartan_perm]

section
variable [h0 : Corpus.Ree.FiniteWeylGroup]
include h0

variable (t) in
/-- Corpus: `CFSG.LieType.Ree.ReeTag.weylPermHom`, CFSG/LieType/Ree/EndoRoots.lean:63. -/
def weylPermHom : WeylGroup t.tag →* WeylGroup t.tag :=
  (coxeterSystem t.tag).lift ⟨fun i => simple t.tag (t.perm i), fun i i' => by
    rw [← coxeterMatrix_perm]
    exact (coxeterSystem t.tag).simple_mul_simple_pow _ _⟩

/-- Corpus: CFSG/LieType/Ree/EndoRoots.lean:68 (same proof). -/
theorem weylPermHom_simple (i : Fin t.tag.rank) :
    t.weylPermHom (simple t.tag i) = simple t.tag (t.perm i) :=
  (coxeterSystem t.tag).lift_apply_simple _ i

/-- Corpus: CFSG/LieType/Ree/EndoRoots.lean:72 (same proof). -/
theorem weylPermHom_comp_self : t.weylPermHom.comp t.weylPermHom = MonoidHom.id _ :=
  (coxeterSystem t.tag).ext_simple fun i => by
    rw [MonoidHom.comp_apply, weylPermHom_simple, weylPermHom_simple, perm_perm,
      MonoidHom.id_apply]

variable (t) in
/-- Corpus: `CFSG.LieType.Ree.ReeTag.weylPerm`, CFSG/LieType/Ree/EndoRoots.lean:78. -/
def weylPerm : WeylGroup t.tag ≃* WeylGroup t.tag :=
  MonoidHom.toMulEquiv t.weylPermHom t.weylPermHom weylPermHom_comp_self weylPermHom_comp_self

variable (t) in
/-- Corpus: `CFSG.LieType.Ree.ReeTag.relWeylRee`, CFSG/LieType/Ree/RelWeylRee.lean:155. -/
def relWeylRee : Subgroup (WeylGroup t.tag) :=
  MonoidHom.eqLocus t.weylPerm.toMonoidHom (MonoidHom.id _)

end

end Weyl

/-! ### `CFSG/LieType/Ree/FixedWeylData.lean` -/

section Orbits

variable (t : ReeTag)

/-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitCount`, CFSG/LieType/Ree/FixedWeylData.lean:21. -/
def fixedOrbitCount : ReeTag → ℕ
  | G2 => 1
  | F4 => 2

/-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitSet`, CFSG/LieType/Ree/FixedWeylData.lean:25. -/
def fixedOrbitSet : (t : ReeTag) → Fin t.fixedOrbitCount → Set (Fin t.tag.rank)
  | G2, _ => ({0, 1} : Set (Fin 2))
  | F4, j => if j.val = 0 then ({0, 3} : Set (Fin 4)) else ({1, 2} : Set (Fin 4))

/-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitWord`, CFSG/LieType/Ree/FixedWeylData.lean:29. -/
def fixedOrbitWord : (t : ReeTag) → Fin t.fixedOrbitCount → List (Fin t.tag.rank)
  | G2, _ => ([0, 1, 0, 1, 0, 1] : List (Fin 2))
  | F4, j => if j.val = 0 then ([0, 3] : List (Fin 4)) else ([1, 2, 1, 2] : List (Fin 4))

section
variable [h0 : Corpus.Ree.FiniteWeylGroup]
include h0

/-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitElement`,
CFSG/LieType/Ree/FixedWeylData.lean:33. -/
def fixedOrbitElement
    (j : Fin t.fixedOrbitCount) : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd (t.fixedOrbitWord j)

/-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitWeyl`, CFSG/LieType/Ree/FixedWeylData.lean:37. -/
def fixedOrbitWeyl
    (j : Fin t.fixedOrbitCount) : Subgroup (WeylGroup t.tag) :=
  parabolicWeylGroup t.tag (t.fixedOrbitSet j)

end

end Orbits

/-! ### `CFSG/LieType/Ree/FixedSubgroupData.lean`, `FixedBruhatDecomposition.lean` -/

section Cells

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedMonomial`,
CFSG/LieType/Ree/FixedSubgroupData.lean:29. -/
def reeFixedMonomial
    : Subgroup (ModGL t.tag K) :=
  monomialSubgroup t.tag K ⊓ t.reeGamma K a

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley] [h6 : Corpus.Ree.FiniteWeylGroup]
include h0 h1 h2 h3 h4 h5 h6

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedBruhatCell`,
CFSG/LieType/Ree/FixedBruhatDecomposition.lean:17. -/
def reeFixedBruhatCell
    (w : WeylGroup t.tag) : Set (ModGL t.tag K) :=
  (t.reeFixedBorel K a : Set (ModGL t.tag K)) *
    {canonicalRep (coxeterSystem t.tag) K w} *
    (t.reeFixedBorel K a : Set (ModGL t.tag K))

end

end Cells

/-! ### Corpus theorems -/

section Theorems

/-- The Ree fixed-point subgroup of a Chevalley group: orbit elements, Bruhat cells and parabolics. -/
class FixedOrbits [Corpus.Exc.RootPred] [Corpus.Exc.Ops] [Corpus.Ree.ReeTag.ReeAut] [Corpus.Exc.ParameterAddition] [Corpus.Ree.FiniteWeylGroup] : Prop where
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mul_self`,
  CFSG/LieType/Ree/FixedWeylStructure.lean:53. -/
  fixedOrbitElement_mul_self {t : ReeTag}
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j * t.fixedOrbitElement j = 1
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem`,
  CFSG/LieType/Ree/FixedWeylStructure.lean:63. -/
  fixedOrbitElement_mem {t : ReeTag}
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j ∈ t.relWeylRee
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitElement_mem_fixedOrbitWeyl`,
  CFSG/LieType/Ree/FixedWeylStructure.lean:508. -/
  fixedOrbitElement_mem_fixedOrbitWeyl {t : ReeTag}
    (j : Fin t.fixedOrbitCount) :
    t.fixedOrbitElement j ∈ t.fixedOrbitWeyl j
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitWeyl_inter_relWeylRee`,
  CFSG/LieType/Ree/FixedWeylStructure.lean:514. -/
  fixedOrbitWeyl_inter_relWeylRee {t : ReeTag}
    (j : Fin t.fixedOrbitCount) :
    (t.fixedOrbitWeyl j : Set (WeylGroup t.tag)) ∩ t.relWeylRee = {1, t.fixedOrbitElement j}
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.fixedOrbitElement_injective`,
  CFSG/LieType/Ree/BorelOvergroupClassification.lean:16. -/
  fixedOrbitElement_injective {t : ReeTag} :
    Function.Injective t.fixedOrbitElement
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.canonicalRep_mem_reeFixedMonomial`,
  CFSG/LieType/Ree/FixedMonomialQuotient.lean:30. -/
  canonicalRep_mem_reeFixedMonomial (t : ReeTag) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (a : ℕ)
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    canonicalRep (coxeterSystem t.tag) K w ∈ t.reeFixedMonomial K a
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedMonomial_eq_sup`,
  CFSG/LieType/Ree/FixedMonomialQuotient.lean:134. -/
  reeFixedMonomial_eq_sup (t : ReeTag) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (a : ℕ) :
    t.reeFixedMonomial K a = t.reeFixedTorus K a ⊔ Subgroup.closure
      (Set.range fun j => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.reeGamma_eq_iUnion_reeFixedBruhatCell`,
  CFSG/LieType/Ree/FixedBruhatDecomposition.lean:252. -/
  reeGamma_eq_iUnion_reeFixedBruhatCell {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ} :
    (t.reeGamma K a : Set (ModGL t.tag K)) = ⋃ w : t.relWeylRee, t.reeFixedBruhatCell K a w
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.reeGamma_eq_sup_reeFixedMonomial`,
  CFSG/LieType/Ree/FixedBruhatDecomposition.lean:270. -/
  reeGamma_eq_sup_reeFixedMonomial {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ} :
    t.reeGamma K a = t.reeFixedBorel K a ⊔ t.reeFixedMonomial K a
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.coe_reeGamma_inf_parabolicSubgroup`,
  CFSG/LieType/Ree/FixedTwoCellParabolics.lean:67. -/
  coe_reeGamma_inf_parabolicSubgroup {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ}
    (j : Fin t.fixedOrbitCount) :
    ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      (t.reeFixedBorel K a : Set (ModGL t.tag K)) ∪
        t.reeFixedBruhatCell K a (t.fixedOrbitElement j)
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.not_normal_reeFixedBorel_subgroupOf`,
  CFSG/LieType/Ree/FixedTwoCellParabolics.lean:108. -/
  not_normal_reeFixedBorel_subgroupOf {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ}
    (j : Fin t.fixedOrbitCount) :
    ¬((t.reeFixedBorel K a).subgroupOf
      (t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j))).Normal
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.not_dvd_index_reeFixedPosUnipotent`,
  CFSG/LieType/Ree/LargeReeSylowOpposition.lean:57. -/
  not_dvd_index_reeFixedPosUnipotent {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ}
    [Fact t.prime.Prime] :
    ¬ t.prime ∣ ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)).index

end Theorems

end ReeTag

/-! ### The bridge to the TauCeti carrier -/

/-- Corpus: `CFSG.LieType.SeitzGeneration.Cat`, CFSG/LieType/SeitzGeneration/Defs.lean:12. -/
abbrev Cat (d : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie d).Group

open ReeTag in
/-- The corpus identification of the catalogue group `²F₄(2^{2b+1})` with the Ree group. -/
class ReeGammaCat [Corpus.Exc.RootPred] [Corpus.Exc.Ops] [Corpus.Ree.ReeTag.ReeAut] : Prop where
  /-- Corpus:
  `CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card`,
  CFSG/HardMathSupport/Solomon/Coordinator/SeitzOuterCube/Exc/ReeTransport.lean:57. -/
  reeGamma_equiv_cat_of_card {b : ℕ} (hb : 1 ≤ b)
    (hv : (TauCeti.LieTypeIndex.reeF4 b).Valid)
    {k : Type} [Field k] [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    Nonempty (Cat ⟨.reeF4 b, hv⟩ ≃* F4.reeGamma k b)

end

end CFSGOutside.Corpus.Ree
