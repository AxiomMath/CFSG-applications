import CFSG.Blueprint.Catalog
import CFSGOutside.Corpus.Defs.LieModel
import CFSGOutsideClean.Corpus.Defs.ClassicalModel
import CFSGOutsideClean.Corpus.Defs.Suzuki

/-!
# The copied model of the simple groups of Lie type is the corpus model

`CFSGOutside.Corpus.Defs.LieModel` (with `.ReeModel`, `.ClassicalModel` and `.Suzuki`) copies inductive types
(`StatedLieTag`, `Chevalley.Tag`, `Chevalley.TwistTag`, `Chevalley.IsRoot`), so its definitions are not equal to
the corpus ones by `rfl`. The Chevalley groups depend on the root datum `τ` only through its rank, its Cartan
matrix and the root predicate `IsRoot τ`. We therefore restate the models of the adjoint, twisted and Ree groups
once, in `LieGen`, for an arbitrary rank `r`, Cartan matrix `C` and predicate `P` on `ℤ^r` in place of `IsRoot`.
The copied and the corpus models of a root datum `τ` are `LieGen` models of their own `IsRoot τ`
(by `Iff.rfl`), the two predicates are both equivalent to the inductive predicate `LieGen.IsRoot` of `r` and `C`,
and `LieGen` models of equivalent predicates are equivalent. For concrete root data the ranks and Cartan matrices
of the copy and of the corpus reduce to the same terms.
-/

namespace CFSGOutsideClean.Corpus

noncomputable section

namespace LieGen

/-- The roots of the root datum with Cartan matrix `C`: the Weyl orbit of the simple roots. -/
inductive IsRoot (r : ℕ) (C : Matrix (Fin r) (Fin r) ℤ) : (Fin r → ℤ) → Prop
  | basis (j : Fin r) : IsRoot r C (Pi.single j 1)
  | reflect (i : Fin r) {v : Fin r → ℤ} :
      IsRoot r C v → IsRoot r C (v - (∑ j, C i j * v j) • Pi.single i 1)

variable (r : ℕ) (C : Matrix (Fin r) (Fin r) ℤ) (P : (Fin r → ℤ) → Prop)

/-- `Chevalley.Label`, with the root predicate `P`. -/
abbrev Label : Type := Fin r ⊕ {v : Fin r → ℤ // P v}

/-- `Chevalley.RootModule`, with the root predicate `P`. -/
abbrev RootModule (R : Type*) [CommRing R] : Type _ := Label r P →₀ R

variable (R : Type*) [CommRing R]

/-- `Chevalley.hVec`, with the root predicate `P`. -/
def hVec (i : Fin r) : RootModule r P R :=
  Finsupp.single (Sum.inl i) 1

open Classical in
/-- `Chevalley.rootVec`, with the root predicate `P`. -/
def rootVec (β : Fin r → ℤ) : RootModule r P R :=
  if h : P β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

/-- `Chevalley.stringUp`, with the root predicate `P`. -/
def stringUp (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | P (α + (k : ℤ) • Pi.single i 1)}

/-- `Chevalley.stringDown`, with the root predicate `P`. -/
def stringDown (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | P (α - (k : ℤ) • Pi.single i 1)}

open Classical in
/-- `Chevalley.xOp`, with the Cartan matrix `C` and the root predicate `P`. -/
def xOp (i : Fin r) (c : R) : Module.End R (RootModule r P R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec r P R j + (((C j i).natAbs : R) * c) • rootVec r P R (Pi.single i 1)
    | .inr α =>
      if α.1 = Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = -Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec r P R i + c ^ 2 • rootVec r P R (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringUp r P i α.1 + 1),
          (((stringDown r P i α.1 + k).choose k : R) * c ^ k) •
            rootVec r P R (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
/-- `Chevalley.yOp`, with the Cartan matrix `C` and the root predicate `P`. -/
def yOp (i : Fin r) (c : R) : Module.End R (RootModule r P R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec r P R j + (((C j i).natAbs : R) * c) • rootVec r P R (-Pi.single i 1)
    | .inr α =>
      if α.1 = -Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec r P R i + c ^ 2 • rootVec r P R (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringDown r P i α.1 + 1),
          (((stringUp r P i α.1 + k).choose k : R) * c ^ k) •
            rootVec r P R (α.1 - (k : ℤ) • Pi.single i 1)

/-- `Chevalley.ModGL`, with the root predicate `P`. -/
abbrev ModGL (K : Type*) [Field K] : Type _ :=
  LinearMap.GeneralLinearGroup K (RootModule r P K)

/-- `Chevalley.adjointGroup`, with the Cartan matrix `C` and the root predicate `P`. -/
def adjointGroup (K : Type*) [Field K] : Subgroup (ModGL r P K) :=
  Subgroup.closure {g | ∃ (i : Fin r) (c : K),
    (g : Module.End K (RootModule r P K)) = xOp r C P K i c ∨
      (g : Module.End K (RootModule r P K)) = yOp r C P K i c}

/-- `reeRelationGroup`, with the Cartan matrix `C` and the root predicate `P`. -/
def reeRelationGroup (K : Type) [Field K] (ρ : Equiv.Perm (Fin r)) (e : Fin r → ℕ) :
    Subgroup (ModGL r P K × ModGL r P K) :=
  Subgroup.closure {gh | ∃ (i : Fin r) (c : K),
    ((gh.1 : Module.End K (RootModule r P K)) = xOp r C P K i c ∧
        (gh.2 : Module.End K (RootModule r P K)) = xOp r C P K (ρ i) (c ^ e i)) ∨
      ((gh.1 : Module.End K (RootModule r P K)) = yOp r C P K i c ∧
        (gh.2 : Module.End K (RootModule r P K)) = yOp r C P K (ρ i) (c ^ e i))}

/-- `reeFixedGroup`, with the Cartan matrix `C` and the root predicate `P`. -/
def reeFixedGroup (K : Type) [Field K] (ρ : Equiv.Perm (Fin r)) (e : Fin r → ℕ) :
    Subgroup (ModGL r P K) :=
  adjointGroup r C P K ⊓
    (reeRelationGroup r C P K ρ e).comap ((MonoidHom.id _).prod (MonoidHom.id _))

/-- `ReeTitsRelationModel`, with the Cartan matrix `C` and the root predicate `P`. -/
def ReeTitsRelationModel (G : Type) [Group G] (ρ : Equiv.Perm (Fin r)) (L : Finset (Fin r))
    (p f a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
    Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient
      (reeFixedGroup r C P K ρ fun i => if i ∈ L then p ^ a else p ^ (a + 1)))

/-- `UntwistedChevalleyModel`, with the Cartan matrix `C` and the root predicate `P`. -/
def UntwistedChevalleyModel (G : Type) [Group G] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (G ≃* (↥(adjointGroup r C P K) ⧸ Subgroup.center ↥(adjointGroup r C P K)))

variable {r}

/-- `Chevalley.permLattice`. -/
def permLattice (π : Equiv.Perm (Fin r)) (v : Fin r → ℤ) : Fin r → ℤ :=
  v ∘ π.symm

/-- `Chevalley.labelPerm`, with the root predicate `P` and its closure under the permutations. -/
def labelPerm (π : Equiv.Perm (Fin r)) (hf : ∀ v, P v → P (permLattice π v))
    (hg : ∀ v, P v → P (permLattice π.symm v)) : Label r P ≃ Label r P where
  toFun
    | .inl i => .inl (π i)
    | .inr α => .inr ⟨permLattice π α.1, hf _ α.2⟩
  invFun
    | .inl i => .inl (π.symm i)
    | .inr α => .inr ⟨permLattice π.symm α.1, hg _ α.2⟩
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

/-- `Chevalley.diagramMap`, with the root predicate `P` and its closure under the permutations. -/
def diagramMap (π : Equiv.Perm (Fin r)) (hf : ∀ v, P v → P (permLattice π v))
    (hg : ∀ v, P v → P (permLattice π.symm v)) (K : Type*) [Field K] : ModGL r P K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (Finsupp.domLCongr (labelPerm P π hf hg))

variable {R}

/-- `Chevalley.entrywise`, with the root predicate `P`. -/
def entrywise (σ : R →+* R) (A : Module.End R (RootModule r P R)) :
    Module.End R (RootModule r P R) :=
  Finsupp.linearCombination R fun b => Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1))

theorem entrywise_single (σ : R →+* R) (A : Module.End R (RootModule r P R)) (b : Label r P) :
    entrywise P σ A (Finsupp.single b 1) =
      Finsupp.mapRange σ σ.map_zero (A (Finsupp.single b 1)) := by
  simp [entrywise]

theorem entrywise_apply_mapRange (σ : R →+* R) (A : Module.End R (RootModule r P R))
    (x : RootModule r P R) :
    entrywise P σ A (Finsupp.mapRange σ σ.map_zero x) =
      Finsupp.mapRange σ σ.map_zero (A x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add σ), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add σ)]
  | single b s =>
    have h1 : Finsupp.mapRange σ σ.map_zero (Finsupp.single b s) =
        σ s • Finsupp.single b (1 : R) := by
      simp
    have h2 : Finsupp.single b s = s • Finsupp.single b (1 : R) := by simp
    rw [h1, map_smul, entrywise_single, h2, map_smul]
    ext l
    simp

theorem entrywise_one (σ : R →+* R) :
    entrywise P σ (1 : Module.End R (RootModule r P R)) = 1 := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywise]

theorem entrywise_mul (σ : R →+* R) (A B : Module.End R (RootModule r P R)) :
    entrywise P σ (A * B) = entrywise P σ A * entrywise P σ B := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [entrywise_single, entrywise_single, entrywise_apply_mapRange, Module.End.mul_apply]

/-- `Chevalley.entrywiseHom`, with the root predicate `P`. -/
def entrywiseHom (σ : R →+* R) :
    Module.End R (RootModule r P R) →* Module.End R (RootModule r P R) where
  toFun := entrywise P σ
  map_one' := entrywise_one P σ
  map_mul' := entrywise_mul P σ

/-- `Chevalley.twistHom`, with the root predicate `P` and its closure under the permutations. -/
def twistHom (π : Equiv.Perm (Fin r)) (hf : ∀ v, P v → P (permLattice π v))
    (hg : ∀ v, P v → P (permLattice π.symm v)) (K : Type*) [Field K] (σ : K →+* K) :
    ModGL r P K →* ModGL r P K :=
  (MulAut.conj (diagramMap P π hf hg K)).toMonoidHom.comp (Units.map (entrywiseHom P σ))

variable (r)

/-- `twistedFixedGroup`, with the Cartan matrix `C` and the root predicate `P`. -/
def twistedFixedGroup (π : Equiv.Perm (Fin r)) (hf : ∀ v, P v → P (permLattice π v))
    (hg : ∀ v, P v → P (permLattice π.symm v)) (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (ModGL r P K) :=
  adjointGroup r C P K ⊓ MonoidHom.eqLocus (twistHom P π hf hg K σ) (MonoidHom.id _)

/-- `TwistedChevalleyModel`, with the Cartan matrix `C` and the root predicate `P`. -/
def TwistedChevalleyModel (π : Equiv.Perm (Fin r)) (hf : ∀ v, P v → P (permLattice π v))
    (hg : ∀ v, P v → P (permLattice π.symm v)) (o : ℕ) (G : Type) [Group G] (q : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ o ∧
    ∃ σ : K →+* K, (∀ c, σ c = c ^ q) ∧
      Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient
        (twistedFixedGroup r C P π hf hg K σ))

variable {r C P}

/-- The models do not depend on the root predicate beyond its extension. -/
theorem reeTitsRelationModel_congr {Q : (Fin r → ℤ) → Prop} (h : ∀ v, P v ↔ Q v) (G : Type)
    [Group G] (ρ : Equiv.Perm (Fin r)) (L : Finset (Fin r)) (p f a : ℕ) :
    ReeTitsRelationModel r C P G ρ L p f a ↔ ReeTitsRelationModel r C Q G ρ L p f a := by
  obtain rfl : P = Q := funext fun v => propext (h v)
  exact Iff.rfl

theorem untwistedChevalleyModel_congr {Q : (Fin r → ℤ) → Prop} (h : ∀ v, P v ↔ Q v) (G : Type)
    [Group G] (q : ℕ) :
    UntwistedChevalleyModel r C P G q ↔ UntwistedChevalleyModel r C Q G q := by
  obtain rfl : P = Q := funext fun v => propext (h v)
  exact Iff.rfl

theorem twistedChevalleyModel_congr {Q : (Fin r → ℤ) → Prop} (h : ∀ v, P v ↔ Q v)
    (π : Equiv.Perm (Fin r)) (hfP : ∀ v, P v → P (permLattice π v))
    (hgP : ∀ v, P v → P (permLattice π.symm v)) (hfQ : ∀ v, Q v → Q (permLattice π v))
    (hgQ : ∀ v, Q v → Q (permLattice π.symm v)) (o : ℕ) (G : Type) [Group G] (q : ℕ) :
    TwistedChevalleyModel r C P π hfP hgP o G q ↔ TwistedChevalleyModel r C Q π hfQ hgQ o G q := by
  obtain rfl : P = Q := funext fun v => propext (h v)
  exact Iff.rfl

/-! ### The copy and the corpus as `LieGen` models -/

theorem isRoot_copy_iff (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (v : Fin τ.rank → ℤ) :
    CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ v ↔ IsRoot τ.rank τ.cartan v := by
  constructor
  · intro h
    induction h with
    | basis j => exact .basis j
    | reflect i _ ih => exact .reflect i ih
  · intro h
    induction h with
    | basis j => exact .basis j
    | reflect i _ ih => exact .reflect i ih

theorem isRoot_corpus_iff (τ : CFSG.Blueprint.Chevalley.Tag) (v : Fin τ.rank → ℤ) :
    CFSG.Blueprint.Chevalley.IsRoot τ v ↔ IsRoot τ.rank τ.cartan v := by
  constructor
  · intro h
    induction h with
    | basis j => exact .basis j
    | reflect i _ ih => exact .reflect i ih
  · intro h
    induction h with
    | basis j => exact .basis j
    | reflect i _ ih => exact .reflect i ih

/-- `permLattice` is compatible with the reflections. -/
theorem permLattice_reflect {C : Matrix (Fin r) (Fin r) ℤ} {π : Equiv.Perm (Fin r)}
    (hπ : ∀ i j, C (π i) (π j) = C i j) (i : Fin r) (v : Fin r → ℤ) :
    permLattice π (v - (∑ j, C i j * v j) • Pi.single i 1) =
      permLattice π v - (∑ j, C (π i) j * permLattice π v j) • Pi.single (π i) 1 := by
  have hsum : ∑ j, C (π i) j * (v ∘ π.symm) j = ∑ j, C i j * v j := by
    rw [← Equiv.sum_comp π]
    simp [hπ]
  simp only [permLattice, hsum]
  ext j
  simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Equiv.symm_apply_eq]

/-- The roots are preserved by the diagram automorphisms. -/
theorem IsRoot.permLattice {C : Matrix (Fin r) (Fin r) ℤ} {π : Equiv.Perm (Fin r)}
    (hπ : ∀ i j, C (π i) (π j) = C i j) {v : Fin r → ℤ} (hv : IsRoot r C v) :
    IsRoot r C (LieGen.permLattice π v) := by
  induction hv with
  | basis j =>
    have : LieGen.permLattice π (Pi.single j 1) = Pi.single (π j) 1 := by
      ext k
      simp only [LieGen.permLattice, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
    rw [this]
    exact .basis _
  | reflect i _ ih => rw [permLattice_reflect hπ]; exact .reflect _ ih

theorem cartan_perm_symm {C : Matrix (Fin r) (Fin r) ℤ} {π : Equiv.Perm (Fin r)}
    (hπ : ∀ i j, C (π i) (π j) = C i j) (i j : Fin r) :
    C (π.symm i) (π.symm j) = C i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

theorem nonempty_mulEquiv_quotient_congr {M : Type} [Group M] {H H' : Subgroup M} (h : H = H')
    (G : Type) [Group G] :
    Nonempty (G ≃* (↥H ⧸ Subgroup.center ↥H)) ↔ Nonempty (G ≃* (↥H' ⧸ Subgroup.center ↥H')) := by
  subst h
  rfl

theorem nonempty_mulEquiv_derivedCentralQuotient_congr {M : Type} [Group M] {H H' : Subgroup M}
    (h : H = H') (G : Type) [Group G] :
    Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient H) ↔
      Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient H') := by
  subst h
  rfl

section copy

theorem xOp_copy (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSGOutside.Corpus.Blueprint.Chevalley.xOp τ K i c = xOp τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) K i c := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.xOp xOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

theorem yOp_copy (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSGOutside.Corpus.Blueprint.Chevalley.yOp τ K i c = yOp τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) K i c := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.yOp yOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

theorem adjointGroup_copy (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (K : Type) [Field K] :
    CFSGOutside.Corpus.Blueprint.Chevalley.adjointGroup τ K = adjointGroup τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) K := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.adjointGroup adjointGroup
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, xOp_copy, yOp_copy]

theorem reeRelationGroup_copy (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (K : Type) [Field K]
    (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    CFSGOutside.Corpus.Blueprint.reeRelationGroup τ K ρ e = reeRelationGroup τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) K ρ e := by
  unfold CFSGOutside.Corpus.Blueprint.reeRelationGroup reeRelationGroup
  congr 1
  ext gh
  simp only [Set.mem_setOf_eq, xOp_copy, yOp_copy]

theorem reeFixedGroup_copy (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (K : Type) [Field K]
    (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    CFSGOutside.Corpus.Blueprint.reeFixedGroup τ K ρ e = reeFixedGroup τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) K ρ e := by
  unfold CFSGOutside.Corpus.Blueprint.reeFixedGroup reeFixedGroup
  rw [adjointGroup_copy, reeRelationGroup_copy]

theorem labelPerm_copy (t : CFSGOutside.Corpus.Blueprint.Chevalley.TwistTag) :
    CFSGOutside.Corpus.Blueprint.Chevalley.labelPerm t.perm t.cartan_perm =
      labelPerm (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice (CFSGOutside.Corpus.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) :=
  Equiv.ext fun x => by rcases x with i | α <;> rfl

theorem diagramMap_copy (t : CFSGOutside.Corpus.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] :
    CFSGOutside.Corpus.Blueprint.Chevalley.diagramMap t K =
      diagramMap (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice (CFSGOutside.Corpus.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K := by
  simp only [CFSGOutside.Corpus.Blueprint.Chevalley.diagramMap, diagramMap, labelPerm_copy]

theorem twistHom_copy (t : CFSGOutside.Corpus.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    CFSGOutside.Corpus.Blueprint.Chevalley.twistHom t K σ =
      twistHom (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice (CFSGOutside.Corpus.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K σ := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.twistHom twistHom
  rw [diagramMap_copy]
  rfl

theorem twistedFixedGroup_copy (t : CFSGOutside.Corpus.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    CFSGOutside.Corpus.Blueprint.twistedFixedGroup t K σ =
      twistedFixedGroup t.tag.rank t.tag.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice (CFSGOutside.Corpus.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K σ := by
  unfold CFSGOutside.Corpus.Blueprint.twistedFixedGroup twistedFixedGroup
  rw [adjointGroup_copy, twistHom_copy]

theorem untwisted_copy (G : Type) [Group G] (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G τ q ↔
      UntwistedChevalleyModel τ.rank τ.cartan (IsRoot τ.rank τ.cartan) G q :=
  Iff.trans (b := UntwistedChevalleyModel τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) G q)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ =>
      and_congr Iff.rfl (nonempty_mulEquiv_quotient_congr (adjointGroup_copy τ K) G))
    (untwistedChevalleyModel_congr (isRoot_copy_iff τ) G q)

theorem twisted_copy (G : Type) [Group G] (t : CFSGOutside.Corpus.Blueprint.Chevalley.TwistTag) (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.TwistedChevalleyModel G t q ↔
      TwistedChevalleyModel t.tag.rank t.tag.cartan (IsRoot t.tag.rank t.tag.cartan) t.perm
        (fun _ hv => IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => IsRoot.permLattice (cartan_perm_symm t.cartan_perm) hv) t.order G q :=
  Iff.trans (b := TwistedChevalleyModel t.tag.rank t.tag.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot t.tag) t.perm
      (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
      (fun _ hv => CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.permLattice (CFSGOutside.Corpus.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) t.order G q)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl <|
      exists_congr fun σ => and_congr Iff.rfl
        (nonempty_mulEquiv_derivedCentralQuotient_congr (twistedFixedGroup_copy t K σ) G))
    (twistedChevalleyModel_congr (isRoot_copy_iff t.tag) _ _ _ _ _ _ G q)

theorem reeTitsRelation_copy (G : Type) [Group G] (τ : CFSGOutside.Corpus.Blueprint.Chevalley.Tag) (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsRelationModel G τ ρ L p f a ↔
      ReeTitsRelationModel τ.rank τ.cartan (IsRoot τ.rank τ.cartan) G ρ L p f a :=
  Iff.trans (b := ReeTitsRelationModel τ.rank τ.cartan (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot τ) G ρ L p f a)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ =>
      and_congr Iff.rfl (nonempty_mulEquiv_derivedCentralQuotient_congr
        (reeFixedGroup_copy τ K ρ _) G))
    (reeTitsRelationModel_congr (isRoot_copy_iff τ) G ρ L p f a)

end copy

section corpus

theorem xOp_corpus (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSG.Blueprint.Chevalley.xOp τ K i c = xOp τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) K i c := by
  unfold CFSG.Blueprint.Chevalley.xOp xOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

theorem yOp_corpus (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSG.Blueprint.Chevalley.yOp τ K i c = yOp τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) K i c := by
  unfold CFSG.Blueprint.Chevalley.yOp yOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

theorem adjointGroup_corpus (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] :
    CFSG.Blueprint.Chevalley.adjointGroup τ K = adjointGroup τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) K := by
  unfold CFSG.Blueprint.Chevalley.adjointGroup adjointGroup
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, xOp_corpus, yOp_corpus]

theorem reeRelationGroup_corpus (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K]
    (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    CFSG.Blueprint.reeRelationGroup τ K ρ e = reeRelationGroup τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) K ρ e := by
  unfold CFSG.Blueprint.reeRelationGroup reeRelationGroup
  congr 1
  ext gh
  simp only [Set.mem_setOf_eq, xOp_corpus, yOp_corpus]

theorem reeFixedGroup_corpus (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K]
    (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    CFSG.Blueprint.reeFixedGroup τ K ρ e = reeFixedGroup τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) K ρ e := by
  unfold CFSG.Blueprint.reeFixedGroup reeFixedGroup
  rw [adjointGroup_corpus, reeRelationGroup_corpus]

theorem labelPerm_corpus (t : CFSG.Blueprint.Chevalley.TwistTag) :
    CFSG.Blueprint.Chevalley.labelPerm t.perm t.cartan_perm =
      labelPerm (CFSG.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice (CFSG.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) :=
  Equiv.ext fun x => by rcases x with i | α <;> rfl

theorem diagramMap_corpus (t : CFSG.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] :
    CFSG.Blueprint.Chevalley.diagramMap t K =
      diagramMap (CFSG.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice (CFSG.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K := by
  simp only [CFSG.Blueprint.Chevalley.diagramMap, diagramMap, labelPerm_corpus]

theorem twistHom_corpus (t : CFSG.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    CFSG.Blueprint.Chevalley.twistHom t K σ =
      twistHom (CFSG.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice (CFSG.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K σ := by
  unfold CFSG.Blueprint.Chevalley.twistHom twistHom
  rw [diagramMap_corpus]
  rfl

theorem twistedFixedGroup_corpus (t : CFSG.Blueprint.Chevalley.TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    CFSG.Blueprint.twistedFixedGroup t K σ =
      twistedFixedGroup t.tag.rank t.tag.cartan (CFSG.Blueprint.Chevalley.IsRoot t.tag) t.perm
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice (CFSG.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) K σ := by
  unfold CFSG.Blueprint.twistedFixedGroup twistedFixedGroup
  rw [adjointGroup_corpus, twistHom_corpus]

theorem untwisted_corpus (G : Type) [Group G] (τ : CFSG.Blueprint.Chevalley.Tag) (q : ℕ) :
    CFSG.Blueprint.UntwistedChevalleyModel G τ q ↔
      UntwistedChevalleyModel τ.rank τ.cartan (IsRoot τ.rank τ.cartan) G q :=
  Iff.trans (b := UntwistedChevalleyModel τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) G q)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ =>
      and_congr Iff.rfl (nonempty_mulEquiv_quotient_congr (adjointGroup_corpus τ K) G))
    (untwistedChevalleyModel_congr (isRoot_corpus_iff τ) G q)

theorem twisted_corpus (G : Type) [Group G] (t : CFSG.Blueprint.Chevalley.TwistTag) (q : ℕ) :
    CFSG.Blueprint.TwistedChevalleyModel G t q ↔
      TwistedChevalleyModel t.tag.rank t.tag.cartan (IsRoot t.tag.rank t.tag.cartan) t.perm
        (fun _ hv => IsRoot.permLattice t.cartan_perm hv)
        (fun _ hv => IsRoot.permLattice (cartan_perm_symm t.cartan_perm) hv) t.order G q :=
  Iff.trans (b := TwistedChevalleyModel t.tag.rank t.tag.cartan (CFSG.Blueprint.Chevalley.IsRoot t.tag) t.perm
      (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice t.cartan_perm hv)
      (fun _ hv => CFSG.Blueprint.Chevalley.IsRoot.permLattice (CFSG.Blueprint.Chevalley.cartan_perm_symm t.cartan_perm) hv) t.order G q)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl <|
      exists_congr fun σ => and_congr Iff.rfl
        (nonempty_mulEquiv_derivedCentralQuotient_congr (twistedFixedGroup_corpus t K σ) G))
    (twistedChevalleyModel_congr (isRoot_corpus_iff t.tag) _ _ _ _ _ _ G q)

theorem reeTitsRelation_corpus (G : Type) [Group G] (τ : CFSG.Blueprint.Chevalley.Tag) (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) :
    CFSG.Blueprint.ReeTitsRelationModel G τ ρ L p f a ↔
      ReeTitsRelationModel τ.rank τ.cartan (IsRoot τ.rank τ.cartan) G ρ L p f a :=
  Iff.trans (b := ReeTitsRelationModel τ.rank τ.cartan (CFSG.Blueprint.Chevalley.IsRoot τ) G ρ L p f a)
    (exists_congr fun K => exists_congr fun _ => exists_congr fun _ =>
      and_congr Iff.rfl (nonempty_mulEquiv_derivedCentralQuotient_congr
        (reeFixedGroup_corpus τ K ρ _) G))
    (reeTitsRelationModel_congr (isRoot_corpus_iff τ) G ρ L p f a)

end corpus

end LieGen

/-! ### The models of the concrete root data -/

section Concrete

open LieGen
open CFSGOutside.Corpus.Blueprint (UntwistedChevalleyModel TwistedChevalleyModel)

theorem untwistedChevalleyModel_g2_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G .G2 q ↔
      CFSG.Blueprint.UntwistedChevalleyModel G .G2 q :=
  (untwisted_copy G .G2 q).trans (untwisted_corpus G .G2 q).symm

theorem untwistedChevalleyModel_f4_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G .F4 q ↔
      CFSG.Blueprint.UntwistedChevalleyModel G .F4 q :=
  (untwisted_copy G .F4 q).trans (untwisted_corpus G .F4 q).symm

theorem untwistedChevalleyModel_e6_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G .E6 q ↔
      CFSG.Blueprint.UntwistedChevalleyModel G .E6 q :=
  (untwisted_copy G .E6 q).trans (untwisted_corpus G .E6 q).symm

theorem untwistedChevalleyModel_e7_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G .E7 q ↔
      CFSG.Blueprint.UntwistedChevalleyModel G .E7 q :=
  (untwisted_copy G .E7 q).trans (untwisted_corpus G .E7 q).symm

theorem untwistedChevalleyModel_e8_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.UntwistedChevalleyModel G .E8 q ↔
      CFSG.Blueprint.UntwistedChevalleyModel G .E8 q :=
  (untwisted_copy G .E8 q).trans (untwisted_corpus G .E8 q).symm

theorem twistedChevalleyModel_e6_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.TwistedChevalleyModel G .E6 q ↔
      CFSG.Blueprint.TwistedChevalleyModel G .E6 q :=
  (twisted_copy G .E6 q).trans (twisted_corpus G .E6 q).symm

theorem twistedChevalleyModel_d4_iff (G : Type) [Group G] (q : ℕ) :
    CFSGOutside.Corpus.Blueprint.TwistedChevalleyModel G .D4 q ↔
      CFSG.Blueprint.TwistedChevalleyModel G .D4 q :=
  (twisted_copy G .D4 q).trans (twisted_corpus G .D4 q).symm

theorem reeTitsRelationModel_g2_iff (G : Type) [Group G] (p f a : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsRelationModel G .G2 CFSGOutside.Corpus.Blueprint.reeG2Perm
        CFSGOutside.Corpus.Blueprint.reeG2Long p f a ↔
      CFSG.Blueprint.ReeTitsRelationModel G .G2 CFSG.Blueprint.reeG2Perm CFSG.Blueprint.reeG2Long
        p f a :=
  (reeTitsRelation_copy G .G2 _ _ p f a).trans (reeTitsRelation_corpus G .G2 _ _ p f a).symm

theorem reeTitsRelationModel_f4_iff (G : Type) [Group G] (p f a : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsRelationModel G .F4 CFSGOutside.Corpus.Blueprint.reeF4Perm
        CFSGOutside.Corpus.Blueprint.reeF4Long p f a ↔
      CFSG.Blueprint.ReeTitsRelationModel G .F4 CFSG.Blueprint.reeF4Perm CFSG.Blueprint.reeF4Long
        p f a :=
  (reeTitsRelation_copy G .F4 _ _ p f a).trans (reeTitsRelation_corpus G .F4 _ _ p f a).symm

end Concrete

open Open (statedLieTagToCorpus statedLieAdmissible_iff statedClassicalModel_iff)

/-- The copied exceptional Chevalley models are the corpus ones. -/
theorem chevalleyExceptionalModel_iff (G : Type) [Group G]
    (t : CFSGOutside.Corpus.Open.StatedLieTag) (p f : ℕ) :
    CFSGOutside.Corpus.Blueprint.ChevalleyExceptionalModel G t p f ↔
      CFSG.Blueprint.ChevalleyExceptionalModel G (statedLieTagToCorpus t) p f := by
  unfold CFSGOutside.Corpus.Blueprint.ChevalleyExceptionalModel
    CFSG.Blueprint.ChevalleyExceptionalModel
  refine and_congr (statedLieAdmissible_iff t 0 p f) ?_
  cases t
  case G2 => exact untwistedChevalleyModel_g2_iff G _
  case F4 => exact untwistedChevalleyModel_f4_iff G _
  case E6 => exact untwistedChevalleyModel_e6_iff G _
  case E7 => exact untwistedChevalleyModel_e7_iff G _
  case E8 => exact untwistedChevalleyModel_e8_iff G _
  case twistedE6 => exact twistedChevalleyModel_e6_iff G _
  case trialityD4 => exact twistedChevalleyModel_d4_iff G _
  all_goals exact Iff.rfl

/-- The copied Ree and Tits models are the corpus ones. -/
theorem reeTitsModel_iff (G : Type) [Group G] (t : CFSGOutside.Corpus.Open.StatedLieTag)
    (p f : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsModel G t p f ↔
      CFSG.Blueprint.ReeTitsModel G (statedLieTagToCorpus t) p f := by
  unfold CFSGOutside.Corpus.Blueprint.ReeTitsModel CFSG.Blueprint.ReeTitsModel
  refine and_congr (statedLieAdmissible_iff t 0 p f) (exists_congr fun a => and_congr Iff.rfl ?_)
  cases t
  case twistedG2 => exact reeTitsRelationModel_g2_iff G p f a
  case twistedF4 => exact reeTitsRelationModel_f4_iff G p f a
  case Tits => exact reeTitsRelationModel_f4_iff G p f a
  all_goals exact Iff.rfl

/-- The copied model of the finite simple groups of Lie type is the corpus model. -/
theorem lieModel_iff (G : Type) [Group G] (t : CFSGOutside.Corpus.Open.StatedLieTag)
    (n p f : ℕ) :
    CFSGOutside.Corpus.Blueprint.LieModel G t n p f ↔
      CFSG.Blueprint.LieModel G (statedLieTagToCorpus t) n p f := by
  unfold CFSGOutside.Corpus.Blueprint.LieModel CFSG.Blueprint.LieModel
  refine or_congr (and_congr ?_ (statedClassicalModel_iff G t n p f))
    (or_congr (and_congr Iff.rfl (and_congr ?_ (chevalleyExceptionalModel_iff G t p f)))
      (or_congr (and_congr Iff.rfl (and_congr ?_ (reeTitsModel_iff G t p f)))
        (and_congr Iff.rfl (and_congr ?_ (Iff.of_eq (suzukiModel_eq G p f))))))
  all_goals cases t <;> decide

end

end CFSGOutsideClean.Corpus
