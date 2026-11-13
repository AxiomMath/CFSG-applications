import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Copied corpus definitions: models of the finite simple groups of Lie type

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. They complete
`CFSGOutside.Corpus.Defs.ReeModel`, `.ClassicalModel` and `.Suzuki` to `Blueprint.LieModel`:

* `Blueprint.Chevalley.TwistTag` to `Blueprint.Chevalley.twistHom`, the graph automorphisms and field
  automorphisms of the adjoint Chevalley groups of types `E₆` and `D₄`, from `CFSG/Blueprint/Chevalley.lean`;
* `Blueprint.classicalTags` to `Blueprint.ChevalleyExceptionalModel` and `Blueprint.LieModel` from
  `CFSG/Blueprint/Catalog.lean`.

`Blueprint.LieModel G t n p f` says that `G` is isomorphic to the finite simple group of Lie type `t` in
characteristic `p` over `𝔽_{p^f}` (rank parameter `n` for the classical types). The clean build proves the copy
equivalent to the corpus original in `clean/CFSGOutsideClean/Corpus/Defs/LieModel.lean`.
-/

namespace CFSGOutside.Corpus

noncomputable section

namespace Blueprint

namespace Chevalley

/-- The twisted types of root data. Copy of `CFSG.Blueprint.Chevalley.TwistTag`,
`CFSG/Blueprint/Chevalley.lean` line 131. -/
inductive TwistTag
  | E6 | D4
  deriving DecidableEq, Repr

namespace TwistTag

/-- The root datum underlying a twisted type. Copy of `CFSG.Blueprint.Chevalley.TwistTag.tag`,
`CFSG/Blueprint/Chevalley.lean` line 137. -/
def tag : TwistTag → Tag
  | E6 => .E6
  | D4 => .D4

/-- The graph automorphism of the Dynkin diagram. Copy of `CFSG.Blueprint.Chevalley.TwistTag.perm`,
`CFSG/Blueprint/Chevalley.lean` line 141. -/
def perm : (t : TwistTag) → Equiv.Perm (Fin t.tag.rank)
  | E6 => (Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6))
  | D4 => (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4))

/-- The order of the graph automorphism. Copy of `CFSG.Blueprint.Chevalley.TwistTag.order`,
`CFSG/Blueprint/Chevalley.lean` line 145. -/
def order : TwistTag → ℕ
  | E6 => 2
  | D4 => 3

end TwistTag

/-- The permutation of the coordinates of `ℤ^rank`. Copy of `CFSG.Blueprint.Chevalley.permLattice`,
`CFSG/Blueprint/Chevalley.lean` line 151. -/
def permLattice {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  v ∘ π.symm

/-- Copy of `CFSG.Blueprint.Chevalley.permLattice_single`, `CFSG/Blueprint/Chevalley.lean` line 155. -/
theorem permLattice_single {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) (i : Fin τ.rank) :
    permLattice π (Pi.single i 1) = Pi.single (π i) 1 := by
  ext j
  simp only [permLattice, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- Copy of `CFSG.Blueprint.Chevalley.permLattice_reflect`, `CFSG/Blueprint/Chevalley.lean` line 160. -/
theorem permLattice_reflect {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    permLattice π (reflect τ i v) = reflect τ (π i) (permLattice π v) := by
  have hsum : ∑ j, τ.cartan (π i) j * (v ∘ π.symm) j = ∑ j, τ.cartan i j * v j := by
    rw [← Equiv.sum_comp π]
    simp [hπ]
  simp only [reflect, permLattice, hsum]
  ext j
  simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Equiv.symm_apply_eq]

/-- Copy of `CFSG.Blueprint.Chevalley.IsRoot.permLattice`, `CFSG/Blueprint/Chevalley.lean` line 171. -/
theorem IsRoot.permLattice {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    IsRoot τ (Chevalley.permLattice π v) := by
  induction hv with
  | basis j => rw [permLattice_single]; exact .basis _
  | reflect i _ ih => rw [permLattice_reflect hπ]; exact .reflect _ ih

/-- Copy of `CFSG.Blueprint.Chevalley.cartan_perm_symm`, `CFSG/Blueprint/Chevalley.lean` line 178. -/
theorem cartan_perm_symm {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (i j : Fin τ.rank) :
    τ.cartan (π.symm i) (π.symm j) = τ.cartan i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

/-- Copy of `CFSG.Blueprint.Chevalley.TwistTag.cartan_submatrix`, `CFSG/Blueprint/Chevalley.lean` line 183. -/
theorem TwistTag.cartan_submatrix (t : TwistTag) :
    t.tag.cartan.submatrix t.perm t.perm = t.tag.cartan := by
  cases t <;> decide

/-- Copy of `CFSG.Blueprint.Chevalley.TwistTag.cartan_perm`, `CFSG/Blueprint/Chevalley.lean` line 187. -/
theorem TwistTag.cartan_perm (t : TwistTag) (i j : Fin t.tag.rank) :
    t.tag.cartan (t.perm i) (t.perm j) = t.tag.cartan i j :=
  congrFun (congrFun t.cartan_submatrix i) j

/-- The graph automorphism acting on the basis labels. Copy of `CFSG.Blueprint.Chevalley.labelPerm`,
`CFSG/Blueprint/Chevalley.lean` line 191. -/
def labelPerm {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) : Label τ ≃ Label τ where
  toFun
    | .inl i => .inl (π i)
    | .inr α => .inr ⟨permLattice π α.1, α.2.permLattice hπ⟩
  invFun
    | .inl i => .inl (π.symm i)
    | .inr α => .inr ⟨permLattice π.symm α.1, α.2.permLattice (cartan_perm_symm hπ)⟩
  left_inv := by
    rintro (i | ⟨α, hα⟩)
    · simp
    · simp only [Sum.inr.injEq, Subtype.mk.injEq]
      ext j; simp [permLattice]
  right_inv := by
    rintro (i | ⟨α, hα⟩)
    · simp
    · simp only [Sum.inr.injEq, Subtype.mk.injEq]
      ext j; simp [permLattice]

/-- The graph automorphism of the adjoint module. Copy of `CFSG.Blueprint.Chevalley.diagramMap`,
`CFSG/Blueprint/Chevalley.lean` line 210. -/
def diagramMap (t : TwistTag) (K : Type*) [Field K] : ModGL t.tag K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Finsupp.domLCongr (labelPerm t.perm t.cartan_perm))

variable {τ : Tag} {R : Type*} [CommRing R]

/-- Apply a ring endomorphism entrywise. Copy of `CFSG.Blueprint.Chevalley.entrywise`,
`CFSG/Blueprint/Chevalley.lean` line 227. -/
def entrywise (σ : R →+* R) (A : Module.End R (RootModule τ R)) :
    Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b => Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1))

/-- Copy of `CFSG.Blueprint.Chevalley.entrywise_single`, `CFSG/Blueprint/Chevalley.lean` line 231. -/
theorem entrywise_single (σ : R →+* R) (A : Module.End R (RootModule τ R)) (b : Label τ) :
    entrywise σ A (Finsupp.single b 1) =
      Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1)) := by
  simp [entrywise]

/-- Copy of `CFSG.Blueprint.Chevalley.entrywise_apply_mapRange`, `CFSG/Blueprint/Chevalley.lean` line 236. -/
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

/-- Copy of `CFSG.Blueprint.Chevalley.entrywise_one`, `CFSG/Blueprint/Chevalley.lean` line 254. -/
theorem entrywise_one (σ : R →+* R) :
    entrywise σ (1 : Module.End R (RootModule τ R)) = 1 := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywise]

/-- Copy of `CFSG.Blueprint.Chevalley.entrywise_mul`, `CFSG/Blueprint/Chevalley.lean` line 261. -/
theorem entrywise_mul (σ : R →+* R) (A B : Module.End R (RootModule τ R)) :
    entrywise σ (A * B) = entrywise σ A * entrywise σ B := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [entrywise_single, entrywise_single, entrywise_apply_mapRange, Module.End.mul_apply]

/-- `entrywise` as a monoid homomorphism. Copy of `CFSG.Blueprint.Chevalley.entrywiseHom`,
`CFSG/Blueprint/Chevalley.lean` line 269. -/
def entrywiseHom (σ : R →+* R) :
    Module.End R (RootModule τ R) →* Module.End R (RootModule τ R) where
  toFun := entrywise σ
  map_one' := entrywise_one σ
  map_mul' := entrywise_mul σ

/-- The twisted Frobenius endomorphism of the adjoint module: the field endomorphism `σ` followed by the graph
automorphism. Copy of `CFSG.Blueprint.Chevalley.twistHom`, `CFSG/Blueprint/Chevalley.lean` line 275. -/
def twistHom (t : TwistTag) (K : Type*) [Field K] (σ : K →+* K) :
    ModGL t.tag K →* ModGL t.tag K :=
  (MulAut.conj (diagramMap t K)).toMonoidHom.comp (Units.map (entrywiseHom σ))

end Chevalley

open Chevalley

/-- The classical types. Copy of `CFSG.Blueprint.classicalTags`, `CFSG/Blueprint/Catalog.lean` line 14. -/
def classicalTags : Finset Open.StatedLieTag :=
  {.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus}

/-- The exceptional Chevalley types and their twists. Copy of `CFSG.Blueprint.chevalleyExceptionalTags`,
`CFSG/Blueprint/Catalog.lean` line 17. -/
def chevalleyExceptionalTags : Finset Open.StatedLieTag :=
  {.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4}

/-- The Ree and Tits types. Copy of `CFSG.Blueprint.reeTitsTags`, `CFSG/Blueprint/Catalog.lean` line 20. -/
def reeTitsTags : Finset Open.StatedLieTag :=
  {.twistedG2, .twistedF4, .Tits}

/-- The adjoint Chevalley group modulo its centre. Copy of `CFSG.Blueprint.AdjointQuotient`,
`CFSG/Blueprint/Catalog.lean` line 23. -/
abbrev AdjointQuotient (τ : Tag) (K : Type) [Field K] : Type :=
  ↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)

/-- The fixed points of the twisted Frobenius endomorphism in the adjoint group. Copy of
`CFSG.Blueprint.twistedFixedGroup`, `CFSG/Blueprint/Catalog.lean` line 29. -/
def twistedFixedGroup (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (ModGL t.tag K) :=
  adjointGroup t.tag K ⊓ MonoidHom.eqLocus (twistHom t K σ) (MonoidHom.id _)

/-- `G` is the untwisted Chevalley group of type `τ` over `𝔽_q`, in the adjoint form. Copy of
`CFSG.Blueprint.UntwistedChevalleyModel`, `CFSG/Blueprint/Catalog.lean` line 33. -/
def UntwistedChevalleyModel (G : Type) [Group G] (τ : Tag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (G ≃* AdjointQuotient τ K)

/-- `G` is the twisted Chevalley group of type `t` over `𝔽_q`. Copy of `CFSG.Blueprint.TwistedChevalleyModel`,
`CFSG/Blueprint/Catalog.lean` line 37. -/
def TwistedChevalleyModel (G : Type) [Group G] (t : TwistTag) (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ t.order ∧
    ∃ σ : K →+* K, (∀ c, σ c = c ^ q) ∧
      Nonempty (G ≃* DerivedCentralQuotient (twistedFixedGroup t K σ))

/-- `G` is isomorphic to the exceptional Chevalley group of type `t` over `𝔽_{p^f}`. Copy of
`CFSG.Blueprint.ChevalleyExceptionalModel`, `CFSG/Blueprint/Catalog.lean` line 42. -/
def ChevalleyExceptionalModel (G : Type) [Group G] (t : Open.StatedLieTag) (p f : ℕ) :
    Prop :=
  Open.StatedLieAdmissible t 0 p f ∧
    match t with
    | .G2 => UntwistedChevalleyModel G .G2 (p ^ f)
    | .F4 => UntwistedChevalleyModel G .F4 (p ^ f)
    | .E6 => UntwistedChevalleyModel G .E6 (p ^ f)
    | .E7 => UntwistedChevalleyModel G .E7 (p ^ f)
    | .E8 => UntwistedChevalleyModel G .E8 (p ^ f)
    | .twistedE6 => TwistedChevalleyModel G .E6 (p ^ f)
    | .trialityD4 => TwistedChevalleyModel G .D4 (p ^ f)
    | _ => False

/-- `G` is isomorphic to the finite simple group of Lie type `t` in characteristic `p` over `𝔽_{p^f}`, with rank
parameter `n` for the classical types. Copy of `CFSG.Blueprint.LieModel`, `CFSG/Blueprint/Catalog.lean`
line 137. -/
def LieModel (G : Type) [Group G] (t : Open.StatedLieTag) (n p f : ℕ) : Prop :=
  (t ∈ classicalTags ∧ Open.StatedClassicalModel G t n p f) ∨
    (n = 0 ∧ t ∈ chevalleyExceptionalTags ∧ ChevalleyExceptionalModel G t p f) ∨
    (n = 0 ∧ t ∈ reeTitsTags ∧ ReeTitsModel G t p f) ∨
    (n = 0 ∧ t = .twistedB2 ∧ SuzukiModel G p f)

end Blueprint

end

end CFSGOutside.Corpus
