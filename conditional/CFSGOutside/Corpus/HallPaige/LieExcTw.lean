import CFSGOutside.Corpus.HallPaige.LieExcChevalley
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# Corpus input for the twisted groups `²E₆(q)` and `³D₄(q)`

The graph-fixed Chevalley groups `graphFixedRootGroup t K σ ≤ GL(L(K))` of the corpus (generated
by the unipotent elements of the adjoint group of type `E₆` or `D₄` over `K = 𝔽_{q^e}` fixed by
the twist `g ↦ d ∘ σ(g) ∘ d⁻¹`), their Borel, torus and monomial subgroups, the relative Weyl group
`relWeylTwist t` with its orbit reflections, and the corpus theorems used for the Hall–Paige
theorem.

All definitions are copied verbatim from AxiomMath/CFSG @ 69cb972 (only `@[expose]` and the
module-system keywords are dropped, and all names are put in the namespace
`CFSGOutside.Corpus.ExcTw`); each docstring gives the corpus name and file:line. The Chevalley
stack (`adjointGroup`, `torusElt`, `borelGroup`, `canonicalRep`, …) is imported from
`CFSGOutside.Corpus.HallPaige.LieExcChevalley`. Corpus theorems are stated as classes with their exact
statements.
-/

set_option autoImplicit false

namespace CFSGOutside.Corpus.ExcTw

noncomputable section

open scoped Pointwise
open CFSGOutside.Corpus.Exc

/-! ### `CFSG/Blueprint/Chevalley.lean` -/

section Twist

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag`, CFSG/Blueprint/Chevalley.lean:131. -/
inductive TwistTag
  | E6 | D4
  deriving DecidableEq, Repr

namespace TwistTag

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.tag`, CFSG/Blueprint/Chevalley.lean:137. -/
def tag : TwistTag → Tag
  | E6 => .E6
  | D4 => .D4

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.perm`, CFSG/Blueprint/Chevalley.lean:141. -/
def perm : (t : TwistTag) → Equiv.Perm (Fin t.tag.rank)
  | E6 => (Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))
  | D4 => (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4))

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.order`, CFSG/Blueprint/Chevalley.lean:145. -/
def order : TwistTag → ℕ
  | E6 => 2
  | D4 => 3

end TwistTag

/-- Corpus: `CFSG.Blueprint.Chevalley.permLattice`, CFSG/Blueprint/Chevalley.lean:151. -/
def permLattice {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  v ∘ π.symm

/-- Corpus: CFSG/LieType/Chevalley/TwistMap.lean:49 (same proof). -/
theorem permLattice_add {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (u v : Fin τ.rank → ℤ) :
    permLattice π (u + v) = permLattice π u + permLattice π v :=
  rfl

/-- Corpus: CFSG/LieType/Chevalley/TwistMap.lean:61 (same proof). -/
theorem permLattice_zsmul {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (k : ℤ) (v : Fin τ.rank → ℤ) :
    permLattice π (k • v) = k • permLattice π v :=
  rfl

/-- Corpus: CFSG/Blueprint/Chevalley.lean:178 (same proof). -/
theorem cartan_perm_symm {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i j : Fin τ.rank) :
    τ.cartan (π.symm i) (π.symm j) = τ.cartan i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

/-- Corpus: CFSG/Blueprint/Chevalley.lean:183 (same proof). -/
theorem TwistTag.cartan_submatrix (t : TwistTag) :
    t.tag.cartan.submatrix t.perm t.perm = t.tag.cartan := by
  cases t <;> decide

/-- Corpus: CFSG/Blueprint/Chevalley.lean:187 (same proof). -/
theorem TwistTag.cartan_perm (t : TwistTag) (i j : Fin t.tag.rank) :
    t.tag.cartan (t.perm i) (t.perm j) = t.tag.cartan i j :=
  congrFun (congrFun t.cartan_submatrix i) j

/-- The permutation of the labels induced by a permutation of the simple roots preserving the Cartan matrix, as a
parameter. In the corpus (`CFSG.Blueprint.Chevalley.labelPerm`, CFSG/Blueprint/Chevalley.lean:191) it is defined by a
`match` on the label, which is not definitionally equal to any other definition by `match`; the clean build
instantiates this class with the corpus definition. -/
class LabelPerm [Corpus.Exc.RootPred] : Type where
  labelPerm {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) :
    Label τ ≃ Label τ

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.ExcTw.LabelPerm]
include h0 h1

/-- Corpus: `CFSG.Blueprint.Chevalley.labelPerm`, CFSG/Blueprint/Chevalley.lean:191. -/
def labelPerm {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) : Label τ ≃ Label τ :=
  LabelPerm.labelPerm π hπ

/-- Corpus: `CFSG.Blueprint.Chevalley.diagramMap`, CFSG/Blueprint/Chevalley.lean:210. -/
def diagramMap (t : TwistTag) (K : Type) [Field K] : ModGL t.tag K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Finsupp.domLCongr (labelPerm t.perm t.cartan_perm))

end

section Entrywise

variable {τ : Tag} {R : Type} [CommRing R]

section
variable [h0 : Corpus.Exc.RootPred]
include h0

/-- Corpus: `CFSG.Blueprint.Chevalley.entrywise`, CFSG/Blueprint/Chevalley.lean:227. -/
def entrywise (σ : R →+* R) (A : Module.End R (RootModule τ R)) :
    Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b => Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1))

/-- Corpus: CFSG/Blueprint/Chevalley.lean:231 (same proof). -/
theorem entrywise_single (σ : R →+* R) (A : Module.End R (RootModule τ R)) (b : Label τ) :
    entrywise σ A (Finsupp.single b 1) =
      Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1)) := by
  simp [entrywise]

/-- Corpus: CFSG/Blueprint/Chevalley.lean:236 (same proof). -/
theorem entrywise_apply_mapRange (σ : R →+* R) (A : Module.End R (RootModule τ R))
    (x : RootModule τ R) :
    entrywise σ A (Finsupp.mapRange σ σ.map_zero x) =
      Finsupp.mapRange σ σ.map_zero (A x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add σ), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add σ)]
  | single b r =>
    have h1 : Finsupp.mapRange σ σ.map_zero (Finsupp.single b r) =
        σ r • Finsupp.single b (1 : R) := by
      simp
    have h2 : Finsupp.single b r = r • Finsupp.single b (1 : R) := by simp
    rw [h1, map_smul, entrywise_single, h2, map_smul]
    ext l
    simp

/-- Corpus: CFSG/Blueprint/Chevalley.lean:254 (same proof). -/
theorem entrywise_one (σ : R →+* R) :
    entrywise σ (1 : Module.End R (RootModule τ R)) = 1 := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywise]

/-- Corpus: CFSG/Blueprint/Chevalley.lean:261 (same proof). -/
theorem entrywise_mul (σ : R →+* R) (A B : Module.End R (RootModule τ R)) :
    entrywise σ (A * B) = entrywise σ A * entrywise σ B := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [entrywise_single, entrywise_single, entrywise_apply_mapRange, Module.End.mul_apply]

/-- Corpus: `CFSG.Blueprint.Chevalley.entrywiseHom`, CFSG/Blueprint/Chevalley.lean:269. -/
def entrywiseHom (σ : R →+* R) :
    Module.End R (RootModule τ R) →* Module.End R (RootModule τ R) where
  toFun := entrywise σ
  map_one' := entrywise_one σ
  map_mul' := entrywise_mul σ

end

end Entrywise

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.ExcTw.LabelPerm]
include h0 h1

/-- Corpus: `CFSG.Blueprint.Chevalley.twistHom`, CFSG/Blueprint/Chevalley.lean:275. -/
def twistHom (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    ModGL t.tag K →* ModGL t.tag K :=
  (MulAut.conj (diagramMap t K)).toMonoidHom.comp (Units.map (entrywiseHom σ))

end

end Twist

/-! ### `CFSG/Blueprint/Catalog.lean`, `CFSG/Blueprint/ChevalleyPinned.lean` -/

/-- Corpus: `CFSG.Blueprint.DerivedCentralQuotient`, CFSG/Blueprint/Catalog.lean:26. -/
abbrev DerivedCentralQuotient {M : Type} [Group M] (H : Subgroup M) : Type :=
  ↥⁅H, H⁆ ⧸ Subgroup.center ↥⁅H, H⁆

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm]
include h0 h1 h2

/-- Corpus: `CFSG.Blueprint.twistedFixedGroup`, CFSG/Blueprint/Catalog.lean:29. -/
def twistedFixedGroup (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (ModGL t.tag K) :=
  adjointGroup t.tag K ⊓ MonoidHom.eqLocus (twistHom t K σ) (MonoidHom.id _)

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.Blueprint.Chevalley.negUnipotent`, CFSG/Blueprint/ChevalleyPinned.lean:252. -/
def negUnipotent (τ : Tag) (R : Type) [CommRing R] :
    Subgroup (Module.End R (RootModule τ R))ˣ :=
  rootSpan τ R {α | RootPred.IsRoot τ α ∧ height α < 0}

end

/-! ### `CFSG/LieType/Chevalley/GraphFixedData.lean` -/

section GraphFixed

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedBorel`, CFSG/LieType/Chevalley/GraphFixedData.lean:16. -/
def graphFixedBorel
    : Subgroup (ModGL t.tag K) :=
  borelGroup t.tag K ⊓ twistedFixedGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedTorus`, CFSG/LieType/Chevalley/GraphFixedData.lean:20. -/
def graphFixedTorus
    : Subgroup (ModGL t.tag K) :=
  torusGroup t.tag K ⊓ twistedFixedGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedMonomial`,
CFSG/LieType/Chevalley/GraphFixedData.lean:24. -/
def graphFixedMonomial
    : Subgroup (ModGL t.tag K) :=
  monomialSubgroup t.tag K ⊓ twistedFixedGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedPosUnipotent`,
CFSG/LieType/Chevalley/GraphFixedData.lean:28. -/
def graphFixedPosUnipotent
    : Subgroup (ModGL t.tag K) :=
  posUnipotent t.tag K ⊓ twistedFixedGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedNegUnipotent`,
CFSG/LieType/Chevalley/GraphFixedData.lean:32. -/
def graphFixedNegUnipotent
    : Subgroup (ModGL t.tag K) :=
  negUnipotent t.tag K ⊓ twistedFixedGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootGroup`,
CFSG/LieType/Chevalley/GraphFixedData.lean:36. -/
def graphFixedRootGroup
    : Subgroup (ModGL t.tag K) :=
  graphFixedPosUnipotent t K σ ⊔ graphFixedNegUnipotent t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootBorel`,
CFSG/LieType/Chevalley/GraphFixedData.lean:85. -/
def graphFixedRootBorel
    : Subgroup (ModGL t.tag K) :=
  graphFixedBorel t K σ ⊓ graphFixedRootGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootTorus`,
CFSG/LieType/Chevalley/GraphFixedData.lean:89. -/
def graphFixedRootTorus
    : Subgroup (ModGL t.tag K) :=
  graphFixedTorus t K σ ⊓ graphFixedRootGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootMonomial`,
CFSG/LieType/Chevalley/GraphFixedData.lean:93. -/
def graphFixedRootMonomial
    : Subgroup (ModGL t.tag K) :=
  graphFixedMonomial t K σ ⊓ graphFixedRootGroup t K σ

/-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootBruhatCell`,
CFSG/LieType/Chevalley/GraphFixedRootBruhat.lean:14. -/
def graphFixedRootBruhatCell
    (w : WeylGroup t.tag) : Set (ModGL t.tag K) :=
  (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) * {canonicalRep (coxeterSystem t.tag) K w} *
    (graphFixedRootBorel t K σ : Set (ModGL t.tag K))

end

end GraphFixed

/-! ### `CFSG/LieType/Chevalley/FoldedWeylData.lean` -/

namespace TwistTag

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.foldedTag`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:11. -/
def foldedTag : TwistTag → Tag
  | E6 => .F4
  | D4 => .G2

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbit`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:15. -/
def orbit : (t : TwistTag) → Fin t.foldedTag.rank → Finset (Fin t.tag.rank)
  | E6 => (![{0, 5}, {2, 4}, {3}, {1}] : Fin 4 → Finset (Fin 6))
  | D4 => (![{0, 1, 3}, {2}] : Fin 2 → Finset (Fin 4))

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitIndex`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:19. -/
def orbitIndex : (t : TwistTag) → Fin t.tag.rank → Fin t.foldedTag.rank
  | E6 => (![0, 3, 1, 2, 1, 0] : Fin 6 → Fin 4)
  | D4 => (![0, 0, 1, 0] : Fin 4 → Fin 2)

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitWord`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:23. -/
def orbitWord (t : TwistTag) (a : Fin t.foldedTag.rank) : List (Fin t.tag.rank) :=
  (List.finRange t.tag.rank).filter (· ∈ t.orbit a)

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitReflection`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:32. -/
def orbitReflection
    (t : TwistTag) (a : Fin t.foldedTag.rank) : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd (t.orbitWord a)

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitSum`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:26. -/
def orbitSum (t : TwistTag) (a : Fin t.foldedTag.rank) : Fin t.tag.rank → ℤ :=
  ∑ i ∈ t.orbit a, Pi.single i 1

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.foldMap`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:29. -/
def foldMap (t : TwistTag) : (Fin t.foldedTag.rank → ℤ) →ₗ[ℤ] Fin t.tag.rank → ℤ :=
  Fintype.linearCombination ℤ t.orbitSum

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.fixedLattice`,
CFSG/LieType/Chevalley/FoldedWeylData.lean:36. -/
def fixedLattice
    (t : TwistTag) : Submodule ℤ (Fin t.tag.rank → ℤ) where
  carrier := {v | permLattice t.perm v = v}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    rw [permLattice_add, hu, hv]
  zero_mem' := rfl
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [permLattice_zsmul, hv]

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitLength`,
CFSG/LieType/Chevalley/FoldedLengthSigns.lean:13. -/
def orbitLength (t : TwistTag)
    (w : WeylGroup t.tag) : ℕ :=
  sInf {n | ∃ ω : List (Fin t.foldedTag.rank), ω.length = n ∧ (ω.map t.orbitReflection).prod = w}

/-- Corpus: CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:11 (same proof). -/
theorem orbit_nonempty (t : TwistTag) (a : Fin t.foldedTag.rank) : (t.orbit a).Nonempty := by
  revert a
  cases t <;> decide

/-- Corpus: `CFSG.Blueprint.Chevalley.TwistTag.orbitMin`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:15. -/
def orbitMin (t : TwistTag) (a : Fin t.foldedTag.rank) : Fin t.tag.rank :=
  (t.orbit a).min' (t.orbit_nonempty a)

end TwistTag

/-! ### `CFSG/LieType/Chevalley/WeylRoots.lean` -/

section
variable [h0 : Corpus.Exc.Liftable]
include h0

/-- Corpus: `CFSG.LieType.Chevalley.instDistribMulActionWeylGroup`,
CFSG/LieType/Chevalley/WeylRoots.lean:77. -/
instance instDistribMulActionWeylGroup {τ : Tag} :
    DistribMulAction (WeylGroup τ) (Fin τ.rank → ℤ) :=
  DistribMulAction.compHom _ (weylAction (isFiniteType_cartan τ))

end

/-! ### `CFSG/LieType/Chevalley/TwistMap.lean`, `RelativeWeylTwist.lean` -/

section Weyl

variable {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}

/-- Corpus: CFSG/LieType/Chevalley/TwistMap.lean:394 (same proof). -/
theorem coxeterMatrix_apply_perm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (i j : Fin τ.rank) :
    (coxeterMatrix (isFiniteType_cartan τ)).M (π i) (π j) =
      (coxeterMatrix (isFiniteType_cartan τ)).M i j := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hπ]

/-- Corpus: CFSG/LieType/Chevalley/TwistMap.lean:401 (same proof). -/
theorem isLiftable_simple_comp_perm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) :
    (coxeterMatrix (isFiniteType_cartan τ)).IsLiftable fun i => simple τ (π i) := fun i j => by
  have h := (coxeterSystem τ).simple_mul_simple_pow (π i) (π j)
  rwa [coxeterMatrix_apply_perm hπ] at h

variable (π) in
/-- Corpus: `CFSG.LieType.Chevalley.weylGroupPerm`, CFSG/LieType/Chevalley/TwistMap.lean:407. -/
def weylGroupPerm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) :
    WeylGroup τ →* WeylGroup τ :=
  (coxeterSystem τ).lift ⟨fun i => simple τ (π i), isLiftable_simple_comp_perm hπ⟩

/-- Corpus: CFSG/LieType/Chevalley/TwistMap.lean:411 (same proof). -/
theorem weylGroupPerm_simple (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (i : Fin τ.rank) : weylGroupPerm π hπ (simple τ i) = simple τ (π i) :=
  (coxeterSystem τ).lift_apply_simple (isLiftable_simple_comp_perm hπ) i

end Weyl

section WeylTwist

variable (t : TwistTag)

/-- Corpus: `CFSG.LieType.Chevalley.weylTwist`, CFSG/LieType/Chevalley/TwistMap.lean:421. -/
def weylTwist : WeylGroup t.tag ≃* WeylGroup t.tag :=
  MonoidHom.toMulEquiv (weylGroupPerm t.perm t.cartan_perm)
    (weylGroupPerm t.perm.symm (cartan_perm_symm t.cartan_perm))
    ((coxeterSystem t.tag).ext_simple fun i => by
      rw [MonoidHom.comp_apply, weylGroupPerm_simple, weylGroupPerm_simple,
        Equiv.symm_apply_apply, MonoidHom.id_apply])
    ((coxeterSystem t.tag).ext_simple fun i => by
      rw [MonoidHom.comp_apply, weylGroupPerm_simple, weylGroupPerm_simple,
        Equiv.apply_symm_apply, MonoidHom.id_apply])

/-- Corpus: `CFSG.LieType.Chevalley.relWeylTwist`,
CFSG/LieType/Chevalley/RelativeWeylTwist.lean:91. -/
def relWeylTwist : Subgroup (WeylGroup t.tag) :=
  MonoidHom.eqLocus (weylTwist t).toMonoidHom (MonoidHom.id _)

end WeylTwist

/-! ### `CFSG/LieType/Chevalley/NativeHolds.lean`, `GraphFixedOrbitParameters.lean` -/

section Orbit

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.Blueprint.Chevalley.xUnit_mem_adjointGroup` (reproved). -/
theorem xUnit_mem_adjointGroup {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (c : K) :
    xUnit τ K i c ∈ adjointGroup τ K :=
  Subgroup.subset_closure ⟨i, c, Or.inl rfl⟩

/-- Corpus: `CFSG.Blueprint.Chevalley.yUnit_mem_adjointGroup` (reproved). -/
theorem yUnit_mem_adjointGroup {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (c : K) :
    yUnit τ K i c ∈ adjointGroup τ K :=
  Subgroup.subset_closure ⟨i, c, Or.inr rfl⟩

/-- Corpus: `CFSG.LieType.Chevalley.xElement`, CFSG/LieType/Chevalley/NativeHolds.lean:159. -/
def xElement {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c⟩

/-- Corpus: `CFSG.LieType.Chevalley.yElement`, CFSG/LieType/Chevalley/NativeHolds.lean:162. -/
def yElement {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (c : K) : adjointGroup τ K :=
  ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩

end

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

/-- Corpus: `CFSG.LieType.Chevalley.orbitField`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:44. -/
def orbitField (a : Fin t.foldedTag.rank) : Subfield K :=
  RingHom.eqLocusField (σ ^ (t.orbit a).card) (RingHom.id K)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.LieType.Chevalley.orbitX`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:47. -/
def orbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) : adjointGroup t.tag K :=
  ((List.range (t.orbit a).card).map fun k =>
    xElement ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod

/-- Corpus: `CFSG.LieType.Chevalley.orbitY`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:52. -/
def orbitY
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) : adjointGroup t.tag K :=
  ((List.range (t.orbit a).card).map fun k =>
    yElement ((t.perm ^ k) (t.orbitMin a)) ((σ ^ k) (c : K))).prod

/-- Corpus: `CFSG.LieType.Chevalley.orbitN`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:57. -/
def orbitN
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    adjointGroup t.tag K :=
  orbitX t K σ a u * orbitY t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) *
    orbitX t K σ a u

/-- Corpus: `CFSG.LieType.Chevalley.orbitH`,
CFSG/LieType/Chevalley/GraphFixedOrbitParameters.lean:63. -/
def orbitH
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    adjointGroup t.tag K :=
  orbitN t K σ a u * (orbitN t K σ a 1)⁻¹

end

end Orbit

/-! ### `CFSG/Open/SplitBNPair.lean`, `CFSG/Foundations/Basic.lean` -/

section SplitBN

variable {G : Type} [Group G]

/-- Corpus: `CFSG.conjugate`, CFSG/Foundations/Basic.lean:31. -/
def conjugate {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

/-- Corpus: `CFSG.ASVolI.ChIJK.IsSplitBNPair`, CFSG/Open/SplitBNPair.lean:12. -/
structure IsSplitBNPair (p : ℕ) (B N : Subgroup G) : Prop where
  gen : B ⊔ N = ⊤
  normal_inter : ((B ⊓ N).subgroupOf N).Normal
  coxeter : ∃ S : Set G, (∀ s ∈ S, s ∈ N ∧ s ∉ B ∧ s ^ 2 ∈ B) ∧
    Subgroup.closure S ⊔ (B ⊓ N) = N ∧
    (∀ s ∈ S, ∀ w ∈ N, ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂) ∧
    (∀ s ∈ S, ∃ b ∈ B, s * b * s ∉ B)
  split : ∃ U : Subgroup G, U ≤ B ∧ (U.subgroupOf B).Normal ∧ IsPGroup p U ∧ ¬ p ∣ U.index ∧
    U ⊓ N = ⊥ ∧ U ⊔ (B ⊓ N) = B ∧ (⨅ n ∈ N, conjugate B n) = B ⊓ N

end SplitBN

/-! ### Corpus theorems -/

section Theorems

/-- The graph-fixed subgroup of a Chevalley group has a split BN-pair. -/
class GraphFixed [Corpus.Exc.RootPred] [Corpus.Exc.Ops] [Corpus.ExcTw.LabelPerm] [Corpus.Exc.ParameterAddition] [Corpus.Exc.Liftable] [Corpus.Exc.Descent] [Corpus.Exc.BorelNormal] [Corpus.Exc.Chevalley] : Prop where
  /-- Corpus: `CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGen.graphFixed_isSplitBNPair`,
  CFSG/LocalAnalysis/RankFourTheoremC/PEmpty/L6LeavesKFactParabolicGenTwisted.lean:19. -/
  graphFixed_isSplitBNPair
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) [CharP K p] (σ : K ≃+* K) :
    IsSplitBNPair p ((graphFixedRootBorel t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom))
      ((graphFixedRootMonomial t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom)) ∧
      graphFixedRootMonomial t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom ⊔
        Subgroup.closure (Set.range fun a => canonicalRep (coxeterSystem t.tag) K
          (t.orbitReflection a)) ∧
      ¬ p ∣ Nat.card (graphFixedRootTorus t K σ.toRingHom) ∧
      graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
        graphFixedRootTorus t K σ.toRingHom ∧
      IsPGroup p (graphFixedPosUnipotent t K σ.toRingHom)
  /-- Corpus: `CFSG.LieType.Chevalley.disjoint_graphFixedRootBruhatCell`,
  CFSG/LieType/Chevalley/GraphFixedRootBruhat.lean:58. -/
  disjoint_graphFixedRootBruhatCell {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    {w w' : WeylGroup t.tag} (h : w ≠ w') :
    Disjoint (graphFixedRootBruhatCell t K σ w) (graphFixedRootBruhatCell t K σ w')
  /-- Corpus: `CFSG.LieType.Chevalley.fixed_simple_Bruhat_multiplication`,
  CFSG/LieType/Chevalley/GraphFixedSimpleBruhat.lean:339. -/
  fixed_simple_Bruhat_multiplication
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ w ∈ relWeylTwist t, (graphFixedRootBruhatCell t K σ.toRingHom w)⁻¹ =
      graphFixedRootBruhatCell t K σ.toRingHom w⁻¹) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1 →
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
            graphFixedRootBruhatCell t K σ.toRingHom w =
          graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * w)) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w →
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
            graphFixedRootBruhatCell t K σ.toRingHom w =
          graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * w) ∪
            graphFixedRootBruhatCell t K σ.toRingHom w) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (w * t.orbitReflection a) = t.orbitLength w + 1 →
        graphFixedRootBruhatCell t K σ.toRingHom w *
            graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) =
          graphFixedRootBruhatCell t K σ.toRingHom (w * t.orbitReflection a)) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (w * t.orbitReflection a) + 1 = t.orbitLength w →
        graphFixedRootBruhatCell t K σ.toRingHom w *
            graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) =
          graphFixedRootBruhatCell t K σ.toRingHom (w * t.orbitReflection a) ∪
            graphFixedRootBruhatCell t K σ.toRingHom w) ∧
    ∀ w ∈ relWeylTwist t, graphFixedRootBruhatCell t K σ.toRingHom w ⊆
      (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K))
  /-- Corpus: `CFSG.LieType.Chevalley.canonicalRep_mem_graphFixedRootMonomial`,
  CFSG/LieType/Chevalley/GraphFixedRootMonomialQuotient.lean:59. -/
  canonicalRep_mem_graphFixedRootMonomial (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootMonomial t K σ
  /-- Corpus: `CFSG.LieType.Chevalley.graphFixedRootMonomial_eq_sup`,
  CFSG/LieType/Chevalley/GraphFixedRootMonomialQuotient.lean:111. -/
  graphFixedRootMonomial_eq_sup (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    graphFixedRootMonomial t K σ = graphFixedRootTorus t K σ ⊔ Subgroup.closure
      (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))
  /-- Corpus: `CFSG.LieType.Chevalley.fixed_Weyl_folded_identification`,
  CFSG/LieType/Chevalley/FoldedWeylIdentification.lean:360. -/
  fixed_Weyl_folded_identification
    (t : TwistTag) :
    (∃ e : (Fin t.foldedTag.rank → ℤ) ≃ₗ[ℤ] t.fixedLattice,
      ∀ u, (e u : Fin t.tag.rank → ℤ) = t.foldMap u) ∧
    (∀ a, t.orbitReflection a ∈ relWeylTwist t ∧ t.orbitReflection a ≠ 1 ∧
      t.orbitReflection a * t.orbitReflection a = 1) ∧
    relWeylTwist t = Subgroup.closure (Set.range t.orbitReflection) ∧
    (∃ φ : relWeylTwist t ≃* WeylGroup t.foldedTag,
      (∀ (w : relWeylTwist t) (u : Fin t.foldedTag.rank → ℤ),
        (w : WeylGroup t.tag) • t.foldMap u = t.foldMap (φ w • u)) ∧
      ∀ a (h : t.orbitReflection a ∈ relWeylTwist t),
        φ ⟨t.orbitReflection a, h⟩ = simple t.foldedTag a) ∧
    (∀ a (u : Fin t.foldedTag.rank → ℤ),
      t.orbitReflection a • t.foldMap u = t.foldMap (simple t.foldedTag a • u)) ∧
    ∀ w ∈ relWeylTwist t, (∀ v ∈ t.fixedLattice, w • v = v) → w = 1
  /-- Corpus: `CFSG.LieType.Chevalley.orbitH_mem_graphFixedRootGroup`,
  CFSG/LieType/Chevalley/GraphFixedOrbitParametrization.lean:636. -/
  orbitH_mem_graphFixedRootGroup (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    (a : Fin t.foldedTag.rank)
    (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) ∈ graphFixedRootGroup t K σ
  /-- Corpus: `CFSG.LieType.Chevalley.coe_orbitH`,
  CFSG/LieType/Chevalley/GraphFixedRankOneScalar.lean:218. -/
  coe_orbitH (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) = ((List.range (t.orbit a).card).map fun k =>
      torusElt t.tag K ((t.perm ^ k) (t.orbitMin a))
        (Units.map ((σ ^ k).comp (orbitField t K σ a).subtype).toMonoidHom u)).prod

end Theorems

/-! ### The bridges to the TauCeti carriers -/

section Bridges

open TauCeti

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm]
include h0 h1 h2

/-- Corpus: `CFSG.TauCetiBridge.TwistedBridge`,
CFSG/Adapters/TauCetiExceptional/Interface.lean:17. -/
def TwistedBridge (t : TwistTag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card ^ t.order →
      ∀ σ : K →+* K, (∀ x, σ x = x ^ q.card) →
        Nonempty (DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
          ValidLieTypeIndex.Group ⟨c q, hv⟩)

/-- Corpus: `CFSG.TauCetiBridge.Even.TwistedBridgeEven`,
CFSG/Adapters/TauCetiExceptional/EvenInterface.lean:18. -/
def TwistedBridgeEven (t : TwistTag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card ^ t.order →
      ∀ σ : K →+* K, (∀ x, σ x = x ^ q.card) →
        Nonempty (DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
          ValidLieTypeIndex.Group ⟨c q, hv⟩)

end

/-- The corpus identifications of the twisted exceptional catalogue groups. -/
class Bridges [Corpus.Exc.RootPred] [Corpus.Exc.Ops] [Corpus.ExcTw.LabelPerm] [Corpus.Exc.ParameterAddition] : Prop where
  /-- Corpus: `CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6`,
  CFSG/Adapters/TauCetiExceptional/TwistedE6Push.lean:104. -/
  twistedBridge_twistedE6 : TwistedBridge .E6 LieTypeIndex.twistedE6
  /-- Corpus: `CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4`,
  CFSG/Adapters/TauCetiExceptional/TwistedD4Push.lean:99. -/
  twistedBridge_trialityD4 : TwistedBridge .D4 LieTypeIndex.trialityD4
  /-- Corpus: `CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6`,
  CFSG/Adapters/TauCetiExceptional/EvenBridgeTwistedE6.lean:64. -/
  twistedBridgeEven_twistedE6 : TwistedBridgeEven .E6 LieTypeIndex.twistedE6
  /-- Corpus: `CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4`,
  CFSG/Adapters/TauCetiExceptional/EvenD4.lean:167. -/
  twistedBridgeEven_trialityD4 : TwistedBridgeEven .D4 LieTypeIndex.trialityD4
  /-- Corpus:
  `CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted.nonempty_mulEquiv_graphFixedRootGroup'`,
  CFSG/LocalAnalysis/ComponentClassification/UnbalancingLocalDihedralTwisted.lean:18. -/
  nonempty_mulEquiv_graphFixedRootGroup' {T : Type} [Group T] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = (p ^ f) ^ t.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : T ≃* DerivedCentralQuotient (twistedFixedGroup t K σ)) :
    Nonempty (T ≃* graphFixedRootGroup t K σ)

end Bridges

end

end CFSGOutside.Corpus.ExcTw
