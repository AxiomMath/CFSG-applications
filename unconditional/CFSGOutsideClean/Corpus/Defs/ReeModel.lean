import CFSG.Open.StatedDefs
import CFSG.Blueprint.Chevalley
import CFSG.Blueprint.Catalog
import CFSGOutside.Corpus.Defs.ReeModel

/-!
# The copied Ree group model is the corpus model

`CFSGOutside.Corpus.Defs.ReeModel` copies inductive types (`StatedLieTag`, `Chevalley.Tag`, `Chevalley.IsRoot`),
so its definitions are not equal to the corpus ones by `rfl`. For `²G₂` only the predicate `IsRoot` of the root
datum `G₂` differs between the copy and the corpus: every other ingredient of `ReeTitsModel` reduces to the same
term. We therefore restate the model once for an arbitrary predicate `P` on `ℤ²` in place of `IsRoot`
(`ReeG2Model P`), show that the copy and the corpus models are `ReeG2Model` of their own `IsRoot`, and that the
two `IsRoot` predicates agree.
-/

namespace CFSGOutsideClean.Corpus

noncomputable section

namespace ReeGen

open CFSGOutside.Corpus.Blueprint.Chevalley (Tag)

variable (τ : Tag) (P : (Fin τ.rank → ℤ) → Prop)

/-- `Chevalley.Label`, with the root predicate `P`. -/
abbrev Label : Type := Fin τ.rank ⊕ {v : Fin τ.rank → ℤ // P v}

/-- `Chevalley.RootModule`, with the root predicate `P`. -/
abbrev RootModule (R : Type*) [CommRing R] : Type _ := Label τ P →₀ R

variable (R : Type*) [CommRing R]

/-- `Chevalley.hVec`, with the root predicate `P`. -/
def hVec (i : Fin τ.rank) : RootModule τ P R :=
  Finsupp.single (Sum.inl i) 1

open Classical in
/-- `Chevalley.rootVec`, with the root predicate `P`. -/
def rootVec (β : Fin τ.rank → ℤ) : RootModule τ P R :=
  if h : P β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

/-- `Chevalley.stringUp`, with the root predicate `P`. -/
def stringUp (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | P (α + (k : ℤ) • Pi.single i 1)}

/-- `Chevalley.stringDown`, with the root predicate `P`. -/
def stringDown (i : Fin τ.rank) (α : Fin τ.rank → ℤ) : ℕ :=
  sSup {k : ℕ | P (α - (k : ℤ) • Pi.single i 1)}

open Classical in
/-- `Chevalley.xOp`, with the root predicate `P`. -/
def xOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ P R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ P R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ P R (Pi.single i 1)
    | .inr α =>
      if α.1 = Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = -Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ P R i + c ^ 2 • rootVec τ P R (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringUp τ P i α.1 + 1),
          (((stringDown τ P i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ P R (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
/-- `Chevalley.yOp`, with the root predicate `P`. -/
def yOp (i : Fin τ.rank) (c : R) : Module.End R (RootModule τ P R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl j => hVec τ P R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ P R (-Pi.single i 1)
    | .inr α =>
      if α.1 = -Pi.single i 1 then Finsupp.single (Sum.inr α) 1
      else if α.1 = Pi.single i 1 then
        Finsupp.single (Sum.inr α) 1 + c • hVec τ P R i + c ^ 2 • rootVec τ P R (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringDown τ P i α.1 + 1),
          (((stringUp τ P i α.1 + k).choose k : R) * c ^ k) •
            rootVec τ P R (α.1 - (k : ℤ) • Pi.single i 1)

/-- `Chevalley.ModGL`, with the root predicate `P`. -/
abbrev ModGL (K : Type*) [Field K] : Type _ :=
  LinearMap.GeneralLinearGroup K (RootModule τ P K)

/-- `Chevalley.adjointGroup`, with the root predicate `P`. -/
def adjointGroup (K : Type*) [Field K] : Subgroup (ModGL τ P K) :=
  Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ P K)) = xOp τ P K i c ∨
      (g : Module.End K (RootModule τ P K)) = yOp τ P K i c}

/-- `reeRelationGroup`, with the root predicate `P`. -/
def reeRelationGroup (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    Subgroup (ModGL τ P K × ModGL τ P K) :=
  Subgroup.closure {gh | ∃ (i : Fin τ.rank) (c : K),
    ((gh.1 : Module.End K (RootModule τ P K)) = xOp τ P K i c ∧
        (gh.2 : Module.End K (RootModule τ P K)) = xOp τ P K (ρ i) (c ^ e i)) ∨
      ((gh.1 : Module.End K (RootModule τ P K)) = yOp τ P K i c ∧
        (gh.2 : Module.End K (RootModule τ P K)) = yOp τ P K (ρ i) (c ^ e i))}

/-- `reeFixedGroup`, with the root predicate `P`. -/
def reeFixedGroup (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank)) (e : Fin τ.rank → ℕ) :
    Subgroup (ModGL τ P K) :=
  adjointGroup τ P K ⊓
    (reeRelationGroup τ P K ρ e).comap ((MonoidHom.id _).prod (MonoidHom.id _))

/-- `ReeTitsRelationModel`, with the root predicate `P`. -/
def ReeTitsRelationModel (G : Type) [Group G] (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
    Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient
      (reeFixedGroup τ P K ρ fun i => if i ∈ L then p ^ a else p ^ (a + 1)))

open CFSGOutside.Corpus.Blueprint.Chevalley (IsRoot)

/-- Equal subgroups have the same derived central quotients, up to isomorphism with a fixed group. -/
theorem nonempty_mulEquiv_derivedCentralQuotient_congr {M : Type} [Group M] {H H' : Subgroup M}
    (h : H = H') (G : Type) [Group G] :
    Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient H) ↔
      Nonempty (G ≃* CFSGOutside.Corpus.Blueprint.DerivedCentralQuotient H') := by
  subst h
  rfl

/-- The copied `xOp` is `xOp` for its own root predicate. -/
theorem xOp_copy (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSGOutside.Corpus.Blueprint.Chevalley.xOp τ K i c = xOp τ (IsRoot τ) K i c := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.xOp xOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

/-- The copied `yOp` is `yOp` for its own root predicate. -/
theorem yOp_copy (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    CFSGOutside.Corpus.Blueprint.Chevalley.yOp τ K i c = yOp τ (IsRoot τ) K i c := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.yOp yOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

/-- The copied `adjointGroup` is `adjointGroup` for its own root predicate. -/
theorem adjointGroup_copy (K : Type) [Field K] :
    CFSGOutside.Corpus.Blueprint.Chevalley.adjointGroup τ K = adjointGroup τ (IsRoot τ) K := by
  unfold CFSGOutside.Corpus.Blueprint.Chevalley.adjointGroup adjointGroup
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, xOp_copy, yOp_copy]

/-- The copied `reeRelationGroup` is `reeRelationGroup` for its own root predicate. -/
theorem reeRelationGroup_copy (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) :
    CFSGOutside.Corpus.Blueprint.reeRelationGroup τ K ρ e = reeRelationGroup τ (IsRoot τ) K ρ e := by
  unfold CFSGOutside.Corpus.Blueprint.reeRelationGroup reeRelationGroup
  congr 1
  ext gh
  simp only [Set.mem_setOf_eq, xOp_copy, yOp_copy]

/-- The copied `reeFixedGroup` is `reeFixedGroup` for its own root predicate. -/
theorem reeFixedGroup_copy (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) :
    CFSGOutside.Corpus.Blueprint.reeFixedGroup τ K ρ e = reeFixedGroup τ (IsRoot τ) K ρ e := by
  unfold CFSGOutside.Corpus.Blueprint.reeFixedGroup reeFixedGroup
  rw [adjointGroup_copy, reeRelationGroup_copy]

/-- The copied `ReeTitsRelationModel` is `ReeTitsRelationModel` for its own root predicate. -/
theorem reeTitsRelationModel_copy (G : Type) [Group G] (ρ : Equiv.Perm (Fin τ.rank))
    (L : Finset (Fin τ.rank)) (p f a : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsRelationModel G τ ρ L p f a ↔
      ReeTitsRelationModel τ (IsRoot τ) G ρ L p f a :=
  exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl
    (nonempty_mulEquiv_derivedCentralQuotient_congr (reeFixedGroup_copy _ _ _ _) G)

/-- The corpus `xOp` for `G₂` is `xOp` for its own root predicate. -/
theorem xOp_corpus (K : Type) [Field K] (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : K) :
    CFSG.Blueprint.Chevalley.xOp .G2 K i c =
      xOp .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) K i c := by
  unfold CFSG.Blueprint.Chevalley.xOp xOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

/-- The corpus `yOp` for `G₂` is `yOp` for its own root predicate. -/
theorem yOp_corpus (K : Type) [Field K] (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : K) :
    CFSG.Blueprint.Chevalley.yOp .G2 K i c =
      yOp .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) K i c := by
  unfold CFSG.Blueprint.Chevalley.yOp yOp
  congr 1
  funext b
  rcases b with j | α <;> rfl

/-- The corpus `adjointGroup` for `G₂` is `adjointGroup` for its own root predicate. -/
theorem adjointGroup_corpus (K : Type) [Field K] :
    CFSG.Blueprint.Chevalley.adjointGroup .G2 K =
      adjointGroup .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) K := by
  unfold CFSG.Blueprint.Chevalley.adjointGroup adjointGroup
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, xOp_corpus, yOp_corpus]
  rfl

/-- The corpus `reeRelationGroup` for `G₂` is `reeRelationGroup` for its own root predicate. -/
theorem reeRelationGroup_corpus (K : Type) [Field K] (ρ : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.G2.rank))
    (e : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank → ℕ) :
    CFSG.Blueprint.reeRelationGroup .G2 K ρ e =
      reeRelationGroup .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) K ρ e := by
  unfold CFSG.Blueprint.reeRelationGroup reeRelationGroup
  congr 1
  ext gh
  simp only [Set.mem_setOf_eq, xOp_corpus, yOp_corpus]
  rfl

/-- The corpus `reeFixedGroup` for `G₂` is `reeFixedGroup` for its own root predicate. -/
theorem reeFixedGroup_corpus (K : Type) [Field K] (ρ : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.G2.rank))
    (e : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank → ℕ) :
    CFSG.Blueprint.reeFixedGroup .G2 K ρ e =
      reeFixedGroup .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) K ρ e := by
  unfold CFSG.Blueprint.reeFixedGroup reeFixedGroup
  rw [adjointGroup_corpus, reeRelationGroup_corpus]
  rfl

/-- The corpus `ReeTitsRelationModel` for `G₂` is `ReeTitsRelationModel` for its own root predicate. -/
theorem reeTitsRelationModel_corpus (G : Type) [Group G] (ρ : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.G2.rank))
    (L : Finset (Fin CFSG.Blueprint.Chevalley.Tag.G2.rank)) (p f a : ℕ) :
    CFSG.Blueprint.ReeTitsRelationModel G .G2 ρ L p f a ↔
      ReeTitsRelationModel .G2 (CFSG.Blueprint.Chevalley.IsRoot .G2) G ρ L p f a :=
  exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl
    (nonempty_mulEquiv_derivedCentralQuotient_congr (reeFixedGroup_corpus _ _ _) G)

end ReeGen

/-- A root of the copy is a root of the corpus. -/
theorem isRoot_g2_of_copy {v : Fin CFSGOutside.Corpus.Blueprint.Chevalley.Tag.G2.rank → ℤ}
    (h : CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot .G2 v) :
    CFSG.Blueprint.Chevalley.IsRoot .G2 v := by
  induction h with
  | basis j => exact CFSG.Blueprint.Chevalley.IsRoot.basis (τ := .G2) j
  | reflect i _ ih => exact CFSG.Blueprint.Chevalley.IsRoot.reflect (τ := .G2) i ih

/-- A root of the corpus is a root of the copy. -/
theorem isRoot_g2_of_corpus {v : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank → ℤ}
    (h : CFSG.Blueprint.Chevalley.IsRoot .G2 v) :
    CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot .G2 v := by
  induction h with
  | basis j => exact CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.basis (τ := .G2) j
  | reflect i _ ih => exact CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot.reflect (τ := .G2) i ih

/-- The root predicates of `G₂` in the copy and in the corpus agree. -/
theorem isRoot_g2_eq :
    (CFSGOutside.Corpus.Blueprint.Chevalley.IsRoot .G2 :
        (Fin CFSGOutside.Corpus.Blueprint.Chevalley.Tag.G2.rank → ℤ) → Prop) =
      CFSG.Blueprint.Chevalley.IsRoot .G2 :=
  funext fun _ => propext ⟨isRoot_g2_of_copy, isRoot_g2_of_corpus⟩

/-- The copied Ree group model `ReeTitsRelationModel` for `G₂` is the corpus one. -/
private theorem reeTitsRelationModel_g2_iff {G : Type} [Group G] (p f a : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsRelationModel G .G2
        CFSGOutside.Corpus.Blueprint.reeG2Perm CFSGOutside.Corpus.Blueprint.reeG2Long p f a ↔
      CFSG.Blueprint.ReeTitsRelationModel G .G2 CFSG.Blueprint.reeG2Perm
        CFSG.Blueprint.reeG2Long p f a := by
  rw [ReeGen.reeTitsRelationModel_copy, ReeGen.reeTitsRelationModel_corpus, isRoot_g2_eq]
  rfl

/-- The copied model of the small Ree group `²G₂(p^f)` is the corpus one. -/
theorem reeTitsModel_twistedG2_iff {G : Type} [Group G] (p f : ℕ) :
    CFSGOutside.Corpus.Blueprint.ReeTitsModel G .twistedG2 p f ↔
      CFSG.Blueprint.ReeTitsModel G .twistedG2 p f :=
  and_congr Iff.rfl (exists_congr fun a => and_congr Iff.rfl (reeTitsRelationModel_g2_iff p f a))

end

end CFSGOutsideClean.Corpus
