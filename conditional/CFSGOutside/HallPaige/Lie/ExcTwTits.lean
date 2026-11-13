import CFSGOutside.HallPaige.Lie.ExcTwSplit

/-!
# The Tits system of a graph-fixed Chevalley group

Let `Γ = graphFixedRootGroup t K σ` (`t = ²E₆` or `³D₄`), with Borel subgroup `B`, monomial
subgroup `N`, Bruhat cells `C(w) = B ṅ_w B` (`w` in the relative Weyl group `W_σ = relWeylTwist t`,
`ṅ_w = canonicalRep w`) and orbit reflections `r_a`.

The corpus split `(B, N)`-pair (`graphFixed_isSplitBNPair`, whose simple reflections are not
named) gives a Tits system `T₀` (`titsOfIsSplitBNPair`); its Bruhat cells are disjoint. The map
`θ : W_σ → N / (B ∩ N)`, `w ↦ [ṅ_w]` matches `C(w)` with the `T₀`-cell of `θ w`; the corpus
multiplication rules `C(r_a) C(w) = C(r_a w)` or `C(r_a w) ∪ C(w)`
(`fixed_simple_Bruhat_multiplication`) and the disjointness of `T₀`-cells show that `θ` is a group
isomorphism. Composing with the folding isomorphism `W_σ ≅ W(t.foldedTag)` sending `r_a` to the
simple reflection `s_a` (`fixed_Weyl_folded_identification`) gives
`Φ : W(t.foldedTag) ≃* N / (B ∩ N)` with `Φ s_a = [ṅ_{r_a}]`.

Finally `CFSGOutside.HallPaige.ExcTw.titsGF` is the Tits system on `Γ` with the *named* simple reflections
`[ṅ_{r_a}]`, and `CFSGOutside.HallPaige.ExcTw.exists_weylEquiv_titsGF` provides `Φ` for it.
-/

namespace CFSGOutside.HallPaige.ExcTw

open DoubleCoset TauCeti CFSGOutside.Corpus.Exc CFSGOutside.Corpus.ExcTw
open scoped Pointwise

noncomputable section

section Canonical

variable {τ : Tag} {hA : TauCeti.IsFiniteType τ.cartan} {W : Type*} [Group W]
  (cs : CoxeterSystem (coxeterMatrix hA) W) (R : Type) [CommRing R]

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- `canonicalRep 1 = 1` (corpus: `CFSG.LieType.Chevalley.canonicalRep_one`,
CFSG/LieType/Chevalley/Canonical.lean:40; reproved). -/
theorem canonicalRep_one : canonicalRep cs R 1 = 1 := by
  have h := (cs.exists_isReduced 1).choose_spec
  have hlen : (cs.exists_isReduced 1).choose.length = 0 := by
    rw [← h.1, ← h.2, cs.length_one]
  rw [canonicalRep, List.eq_nil_of_length_eq_zero hlen, List.map_nil, List.prod_nil]

end

end Canonical

section Setup

variable (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- The graph-fixed group `Γ`. -/
abbrev GF : Subgroup (ModGL t.tag K) := graphFixedRootGroup t K σ.toRingHom

/-- The Borel subgroup of `Γ`, inside `Γ`. -/
abbrev BF : Subgroup (GF t K σ) := (graphFixedRootBorel t K σ.toRingHom).subgroupOf (GF t K σ)

/-- The monomial subgroup of `Γ`, inside `Γ`. -/
abbrev NF : Subgroup (GF t K σ) := (graphFixedRootMonomial t K σ.toRingHom).subgroupOf (GF t K σ)

end

variable {t K σ}

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

theorem borel_le_GF : graphFixedRootBorel t K σ.toRingHom ≤ GF t K σ := inf_le_right

theorem monomial_le_GF : graphFixedRootMonomial t K σ.toRingHom ≤ GF t K σ := inf_le_right

theorem torus_le_borel : graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom :=
  inf_le_inf_right _ (inf_le_inf_right _ le_sup_left)

theorem torus_le_monomial :
    graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootMonomial t K σ.toRingHom :=
  inf_le_inf_right _ (inf_le_inf_right _ le_sup_left)

theorem GF_le_twistedFixedGroup : GF t K σ ≤ twistedFixedGroup t K σ.toRingHom :=
  sup_le inf_le_right inf_le_right

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- `ṅ_w` lies in `Γ`. -/
theorem canonicalRep_mem_GF {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    canonicalRep (coxeterSystem t.tag) K w ∈ GF t K σ :=
  monomial_le_GF (Corpus.ExcTw.GraphFixed.canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hw)

/-- `ṅ_w` as an element of `N`. -/
def nrep {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) : NF t K σ :=
  ⟨⟨canonicalRep (coxeterSystem t.tag) K w, canonicalRep_mem_GF hw⟩,
    Subgroup.mem_subgroupOf.2 (Corpus.ExcTw.GraphFixed.canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hw)⟩

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- The Bruhat cell `C(w)`, inside `Γ`. -/
def cell (w : WeylGroup t.tag) : Set (GF t K σ) :=
  Subtype.val ⁻¹' graphFixedRootBruhatCell t K σ.toRingHom w

theorem mem_graphFixedRootBruhatCell {w : WeylGroup t.tag} {x : ModGL t.tag K} :
    x ∈ graphFixedRootBruhatCell t K σ.toRingHom w ↔ ∃ b ∈ graphFixedRootBorel t K σ.toRingHom,
      ∃ b' ∈ graphFixedRootBorel t K σ.toRingHom,
        b * canonicalRep (coxeterSystem t.tag) K w * b' = x := by
  simp only [graphFixedRootBruhatCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem cell_eq {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    cell (σ := σ) w = doubleCoset ((nrep (σ := σ) hw : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) := by
  ext x
  rw [cell, Set.mem_preimage, mem_graphFixedRootBruhatCell, mem_doubleCoset]
  constructor
  · rintro ⟨b, hb, b', hb', hx⟩
    refine ⟨⟨b, borel_le_GF hb⟩, hb, ⟨b', borel_le_GF hb'⟩, hb', Subtype.ext ?_⟩
    rw [← hx]
    rfl
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩

theorem mem_cell_self {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    ((nrep (σ := σ) hw : NF t K σ) : GF t K σ) ∈ cell (σ := σ) w := by
  rw [cell_eq hw]
  exact mem_doubleCoset_self _ _ _

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

theorem canonicalRep_mem_cell {w : WeylGroup t.tag} :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootBruhatCell t K σ.toRingHom w :=
  mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩

theorem mul_mem_cell_of_subset {u v x y : WeylGroup t.tag}
    (h : graphFixedRootBruhatCell t K σ.toRingHom u * graphFixedRootBruhatCell t K σ.toRingHom v ⊆
      graphFixedRootBruhatCell t K σ.toRingHom x ∪ graphFixedRootBruhatCell t K σ.toRingHom y)
    {a b : GF t K σ} (ha : a ∈ cell (σ := σ) u) (hb : b ∈ cell (σ := σ) v) :
    a * b ∈ cell (σ := σ) x ∪ cell (σ := σ) y :=
  h (Set.mul_mem_mul ha hb)

theorem mul_mem_cell_of_eq {u v x : WeylGroup t.tag}
    (h : graphFixedRootBruhatCell t K σ.toRingHom u * graphFixedRootBruhatCell t K σ.toRingHom v =
      graphFixedRootBruhatCell t K σ.toRingHom x)
    {a b : GF t K σ} (ha : a ∈ cell (σ := σ) u) (hb : b ∈ cell (σ := σ) v) :
    a * b ∈ cell (σ := σ) x := by
  have : ((a * b : GF t K σ) : ModGL t.tag K) ∈ graphFixedRootBruhatCell t K σ.toRingHom u *
      graphFixedRootBruhatCell t K σ.toRingHom v := Set.mul_mem_mul ha hb
  rw [h] at this
  exact this

end

end Setup

/-! ### Orbit lengths are Coxeter lengths in the folded Weyl group -/

section Length

variable (t : TwistTag)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem prod_map_orbitReflection (φ : relWeylTwist t ≃* WeylGroup t.foldedTag)
    (hφ : ∀ a (h : t.orbitReflection a ∈ relWeylTwist t),
      φ ⟨t.orbitReflection a, h⟩ = simple t.foldedTag a)
    (ω : List (Fin t.foldedTag.rank)) :
    ∃ h : (ω.map t.orbitReflection).prod ∈ relWeylTwist t,
      φ ⟨_, h⟩ = (coxeterSystem t.foldedTag).wordProd ω := by
  have hmem := (Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.1
  induction ω with
  | nil => exact ⟨one_mem _, by simpa using φ.map_one⟩
  | cons a ω ih =>
    obtain ⟨h, hφω⟩ := ih
    refine ⟨mul_mem (hmem a).1 h, ?_⟩
    rw [CoxeterSystem.wordProd_cons, ← hφω,
      show (coxeterSystem t.foldedTag).simple a = simple t.foldedTag a from rfl,
      ← hφ a (hmem a).1, ← map_mul]
    rfl

theorem orbitLength_eq (φ : relWeylTwist t ≃* WeylGroup t.foldedTag)
    (hφ : ∀ a (h : t.orbitReflection a ∈ relWeylTwist t),
      φ ⟨t.orbitReflection a, h⟩ = simple t.foldedTag a) (w : relWeylTwist t) :
    t.orbitLength w = (coxeterSystem t.foldedTag).length (φ w) := by
  have key : ∀ ω : List (Fin t.foldedTag.rank),
      (ω.map t.orbitReflection).prod = (w : WeylGroup t.tag) ↔
        (coxeterSystem t.foldedTag).wordProd ω = φ w := by
    intro ω
    obtain ⟨h, hφω⟩ := prod_map_orbitReflection t φ hφ ω
    constructor
    · intro he
      rw [← hφω]
      congr 1
      exact Subtype.ext he
    · intro he
      rw [← hφω] at he
      exact congrArg Subtype.val (φ.injective he)
  apply le_antisymm
  · obtain ⟨ω, hω, he⟩ := (coxeterSystem t.foldedTag).exists_isReduced (φ w)
    refine Nat.sInf_le ⟨ω, ?_, (key ω).2 he.symm⟩
    rw [← hω, ← he]
  · obtain ⟨ω, hω, he⟩ := (coxeterSystem t.foldedTag).exists_isReduced (φ w)
    refine le_csInf ⟨ω.length, ω, rfl, (key ω).2 he.symm⟩ ?_
    rintro n ⟨ω', rfl, he'⟩
    rw [← (key ω').1 he']
    exact (coxeterSystem t.foldedTag).length_wordProd_le ω'

theorem exists_foldedEquiv : ∃ φ : relWeylTwist t ≃* WeylGroup t.foldedTag,
    ∀ a (h : t.orbitReflection a ∈ relWeylTwist t),
      φ ⟨t.orbitReflection a, h⟩ = simple t.foldedTag a := by
  obtain ⟨φ, -, hφ⟩ := (Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.2.2.1
  exact ⟨φ, hφ⟩

theorem orbitReflection_mem' (a : Fin t.foldedTag.rank) : t.orbitReflection a ∈ relWeylTwist t :=
  ((Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.1 a).1

theorem orbitReflection_ne_one' (a : Fin t.foldedTag.rank) : t.orbitReflection a ≠ 1 :=
  ((Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.1 a).2.1

theorem orbitReflection_mul_self' (a : Fin t.foldedTag.rank) :
    t.orbitReflection a * t.orbitReflection a = 1 :=
  ((Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.1 a).2.2

theorem orbitLength_simple_mul {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) :
    t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1 ∨
      t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w := by
  obtain ⟨φ, hφ⟩ := exists_foldedEquiv t
  have h1 := orbitLength_eq t φ hφ ⟨_, mul_mem (orbitReflection_mem' t a) hw⟩
  have h2 := orbitLength_eq t φ hφ ⟨w, hw⟩
  have h3 : φ ⟨_, mul_mem (orbitReflection_mem' t a) hw⟩ = simple t.foldedTag a * φ ⟨w, hw⟩ := by
    rw [← hφ a (orbitReflection_mem' t a), ← map_mul]
    rfl
  simp only at h1 h2
  rw [h1, h2, h3]
  exact (coxeterSystem t.foldedTag).length_simple_mul _ a

theorem orbitLength_one : t.orbitLength 1 = 0 := by
  obtain ⟨φ, hφ⟩ := exists_foldedEquiv t
  have := orbitLength_eq t φ hφ 1
  simp only [OneMemClass.coe_one, map_one] at this
  rw [this, CoxeterSystem.length_one]

theorem orbitLength_orbitReflection (a : Fin t.foldedTag.rank) :
    t.orbitLength (t.orbitReflection a) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_foldedEquiv t
  have := orbitLength_eq t φ hφ ⟨_, orbitReflection_mem' t a⟩
  simp only at this
  rw [this, hφ, CoxeterSystem.length_simple]

end

end Length

/-! ### The Weyl group of the corpus split `(B, N)`-pair -/

section Weyl

variable (t : TwistTag) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
  [CharP K p]

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- The Tits system of the corpus split `(B, N)`-pair of `Γ` (unnamed simple reflections). -/
noncomputable def titsGF₀ : TauCeti.TitsSystem (GF t K σ) :=
  titsOfIsSplitBNPair (Corpus.ExcTw.GraphFixed.graphFixed_isSplitBNPair t K hp σ).1

/-- The class of `n ∈ N` in `N / (B ∩ N)`. -/
noncomputable def mk₀ (n : NF t K σ) : (titsGF₀ t K σ hp).WeylGroup :=
  QuotientGroup.mk (s := (titsGF₀ t K σ hp).intersection) n

open Classical in
/-- `θ w = [ṅ_w]` (and `1` off `W_σ`). -/
noncomputable def θ (w : WeylGroup t.tag) : (titsGF₀ t K σ hp).WeylGroup :=
  if hw : w ∈ relWeylTwist t then mk₀ t K σ hp (nrep (σ := σ) hw) else 1

end

variable {t K σ hp}

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem mk₀_mul (a b : NF t K σ) : mk₀ t K σ hp (a * b) = mk₀ t K σ hp a * mk₀ t K σ hp b :=
  QuotientGroup.mk_mul (N := (titsGF₀ t K σ hp).intersection) a b

theorem mk₀_one : mk₀ t K σ hp 1 = 1 :=
  QuotientGroup.mk_one (N := (titsGF₀ t K σ hp).intersection)

theorem mk₀_eq_one_iff (n : NF t K σ) : mk₀ t K σ hp n = 1 ↔ (n : GF t K σ) ∈ BF t K σ :=
  QuotientGroup.eq_one_iff (N := (titsGF₀ t K σ hp).intersection) n

theorem mk₀_surjective : Function.Surjective (mk₀ t K σ hp) :=
  QuotientGroup.mk_surjective (s := (titsGF₀ t K σ hp).intersection)

theorem bruhatCell_mk₀ (n : NF t K σ) :
    (titsGF₀ t K σ hp).bruhatCell (mk₀ t K σ hp n) =
      doubleCoset (n : GF t K σ) (BF t K σ) (BF t K σ) :=
  (titsGF₀ t K σ hp).bruhatCell_mk n

theorem mem_bruhatCell_mk₀ (n : NF t K σ) :
    (n : GF t K σ) ∈ (titsGF₀ t K σ hp).bruhatCell (mk₀ t K σ hp n) := by
  rw [bruhatCell_mk₀]
  exact mem_doubleCoset_self _ _ _

theorem θ_of_mem {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    θ t K σ hp w = mk₀ t K σ hp (nrep (σ := σ) hw) := by
  rw [θ, dif_pos hw]

theorem bruhatCell_θ {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    (titsGF₀ t K σ hp).bruhatCell (θ t K σ hp w) = cell (σ := σ) w := by
  rw [θ_of_mem hw, bruhatCell_mk₀, cell_eq hw]

theorem nrep_one : (nrep (σ := σ) (one_mem (relWeylTwist t)) : NF t K σ) = 1 :=
  Subtype.ext (Subtype.ext (canonicalRep_one _ _))

theorem θ_one : θ t K σ hp 1 = 1 := by
  rw [θ_of_mem (one_mem _), nrep_one, mk₀_one]

theorem cell_one : cell (σ := σ) (1 : WeylGroup t.tag) = (BF t K σ : Set (GF t K σ)) := by
  rw [cell_eq (one_mem _), nrep_one]
  ext x
  rw [mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using (BF t K σ).mul_mem ha hb
  · intro hx
    exact ⟨x, hx, 1, one_mem _, by simp⟩

theorem eq_of_θ_eq {w v : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (hv : v ∈ relWeylTwist t)
    (h : θ t K σ hp w = θ t K σ hp v) : w = v := by
  by_contra hne
  have h1 := mem_cell_self (σ := σ) hw
  rw [← bruhatCell_θ (hp := hp) hw, h, bruhatCell_θ hv] at h1
  exact Set.disjoint_left.1 (Corpus.ExcTw.GraphFixed.disjoint_graphFixedRootBruhatCell (σ := σ.toRingHom) hne)
    canonicalRep_mem_cell h1

theorem θ_mul_self (a : Fin t.foldedTag.rank) :
    θ t K σ hp (t.orbitReflection a) * θ t K σ hp (t.orbitReflection a) = 1 := by
  have ha := orbitReflection_mem' t a
  have hmul := (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.1 _ ha a (by
    rw [orbitReflection_mul_self', orbitLength_one, orbitLength_orbitReflection])
  rw [orbitReflection_mul_self'] at hmul
  set n := nrep (σ := σ) ha
  have h1 : ((n * n : NF t K σ) : GF t K σ) ∈
      cell (σ := σ) (1 : WeylGroup t.tag) ∪ cell (σ := σ) (t.orbitReflection a) :=
    mul_mem_cell_of_subset hmul.le (mem_cell_self ha) (mem_cell_self ha)
  rw [← bruhatCell_θ (hp := hp) (one_mem _), ← bruhatCell_θ (hp := hp) ha] at h1
  have h2 := mem_bruhatCell_mk₀ (hp := hp) (n * n)
  rw [mk₀_mul, ← θ_of_mem ha] at h2
  rcases h1 with h1 | h1
  · rw [TitsSystem.eq_of_mem_bruhatCell_of_mem _ h2 h1, θ_one]
  · have := TitsSystem.eq_of_mem_bruhatCell_of_mem _ h2 h1
    have h3 : θ t K σ hp (t.orbitReflection a) = θ t K σ hp 1 := by
      rw [θ_one]
      calc θ t K σ hp (t.orbitReflection a) =
            θ t K σ hp (t.orbitReflection a) * θ t K σ hp (t.orbitReflection a) *
              (θ t K σ hp (t.orbitReflection a))⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
    exact absurd (eq_of_θ_eq ha (one_mem _) h3) (orbitReflection_ne_one' t a)

theorem θ_mul_of_up {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (a : Fin t.foldedTag.rank)
    (h : t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1) :
    θ t K σ hp (t.orbitReflection a * w) =
      θ t K σ hp (t.orbitReflection a) * θ t K σ hp w := by
  have ha := orbitReflection_mem' t a
  have haw := mul_mem ha hw
  have hmul := (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.1 w hw a h
  have h1 : ((nrep (σ := σ) ha * nrep (σ := σ) hw : NF t K σ) : GF t K σ) ∈
      cell (σ := σ) (t.orbitReflection a * w) :=
    mul_mem_cell_of_eq hmul (mem_cell_self ha) (mem_cell_self hw)
  rw [← bruhatCell_θ (hp := hp) haw] at h1
  have h2 := mem_bruhatCell_mk₀ (hp := hp) (nrep (σ := σ) ha * nrep (σ := σ) hw)
  rw [mk₀_mul, ← θ_of_mem ha, ← θ_of_mem hw] at h2
  exact TitsSystem.eq_of_mem_bruhatCell_of_mem _ h1 h2

theorem θ_simple_mul {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (a : Fin t.foldedTag.rank) :
    θ t K σ hp (t.orbitReflection a * w) =
      θ t K σ hp (t.orbitReflection a) * θ t K σ hp w := by
  rcases orbitLength_simple_mul t hw a with h | h
  · exact θ_mul_of_up hw a h
  · have haw := mul_mem (orbitReflection_mem' t a) hw
    have hw' : t.orbitReflection a * (t.orbitReflection a * w) = w := by
      rw [← mul_assoc, orbitReflection_mul_self', one_mul]
    have := θ_mul_of_up (K := K) (σ := σ) (hp := hp) haw a (by rw [hw']; omega)
    rw [hw'] at this
    rw [this, ← mul_assoc, θ_mul_self, one_mul]

theorem relWeylTwist_eq_closure' :
    relWeylTwist t = Subgroup.closure (Set.range t.orbitReflection) :=
  (Corpus.ExcTw.GraphFixed.fixed_Weyl_folded_identification t).2.2.1

theorem θ_mul {u : WeylGroup t.tag} (hu : u ∈ relWeylTwist t) :
    ∀ w ∈ relWeylTwist t, θ t K σ hp (u * w) = θ t K σ hp u * θ t K σ hp w := by
  rw [relWeylTwist_eq_closure'] at hu
  induction hu using Subgroup.closure_induction_left with
  | one => intro w _; rw [one_mul, θ_one, one_mul]
  | mul_left x hx y hy ih =>
    obtain ⟨a, rfl⟩ := hx
    intro w hw
    have hy' : y ∈ relWeylTwist t := (relWeylTwist_eq_closure' (t := t)).symm ▸ hy
    rw [mul_assoc, θ_simple_mul (mul_mem hy' hw), ih w hw, θ_simple_mul hy', mul_assoc]
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨a, rfl⟩ := hx
    intro w hw
    have hy' : y ∈ relWeylTwist t := (relWeylTwist_eq_closure' (t := t)).symm ▸ hy
    have hinv : (t.orbitReflection a)⁻¹ = t.orbitReflection a :=
      inv_eq_of_mul_eq_one_right (orbitReflection_mul_self' t a)
    rw [hinv, mul_assoc, θ_simple_mul (mul_mem hy' hw), ih w hw, θ_simple_mul hy', mul_assoc]

end

variable (t K σ hp)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- `θ` as a homomorphism on `W_σ`. -/
noncomputable def θHom : relWeylTwist t →* (titsGF₀ t K σ hp).WeylGroup where
  toFun w := θ t K σ hp w
  map_one' := θ_one
  map_mul' u w := θ_mul u.2 w w.2

end

variable {t K σ hp}

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem θHom_injective : Function.Injective (θHom t K σ hp) :=
  fun w v h => Subtype.ext (eq_of_θ_eq w.2 v.2 h)

theorem θHom_surjective : Function.Surjective (θHom t K σ hp) := by
  intro x
  obtain ⟨n, rfl⟩ := mk₀_surjective (hp := hp) x
  let R : Subgroup (ModGL t.tag K) :=
    ((((θHom t K σ hp).range.comap
      { toFun := mk₀ t K σ hp, map_one' := mk₀_one, map_mul' := mk₀_mul }).map
        (NF t K σ).subtype).map (GF t K σ).subtype)
  have hT : graphFixedRootTorus t K σ.toRingHom ≤ R := by
    intro g hg
    have hgN := torus_le_monomial hg
    have hgΓ := monomial_le_GF hgN
    refine ⟨⟨g, hgΓ⟩, ⟨⟨⟨g, hgΓ⟩, Subgroup.mem_subgroupOf.2 hgN⟩, ?_, rfl⟩, rfl⟩
    show mk₀ t K σ hp _ ∈ (θHom t K σ hp).range
    rw [(mk₀_eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (torus_le_borel hg))]
    exact one_mem _
  have hC : Subgroup.closure (Set.range fun a => canonicalRep (coxeterSystem t.tag) K
      (t.orbitReflection a)) ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    have ha := orbitReflection_mem' t a
    refine ⟨_, ⟨nrep (σ := σ) ha, ?_, rfl⟩, rfl⟩
    exact ⟨⟨_, ha⟩, θ_of_mem ha⟩
  have hN : graphFixedRootMonomial t K σ.toRingHom ≤ R :=
    (Corpus.ExcTw.GraphFixed.graphFixedRootMonomial_eq_sup t K σ.toRingHom) ▸ sup_le hT hC
  obtain ⟨_, ⟨m, hm, rfl⟩, hmn⟩ := hN (Subgroup.mem_subgroupOf.1 n.2)
  have : m = n := Subtype.ext (Subtype.ext hmn)
  subst this
  exact hm

/-- **`θ` is an isomorphism `W_σ ≃* N / (B ∩ N)`.** -/
noncomputable def θEquiv : relWeylTwist t ≃* (titsGF₀ t K σ hp).WeylGroup :=
  MulEquiv.ofBijective (θHom t K σ hp) ⟨θHom_injective, θHom_surjective⟩

theorem exists_θ_eq (x : (titsGF₀ t K σ hp).WeylGroup) :
    ∃ v ∈ relWeylTwist t, θ t K σ hp v = x := by
  obtain ⟨v, hv⟩ := θHom_surjective (t := t) (K := K) (σ := σ) (hp := hp) x
  exact ⟨v, v.2, hv⟩

/-- **The Weyl group `W(t.foldedTag) ≅ N / (B ∩ N)`, `s_a ↦ θ r_a`.** -/
theorem exists_weylEquiv₀ : ∃ Φ : WeylGroup t.foldedTag ≃* (titsGF₀ t K σ hp).WeylGroup,
    ∀ a, Φ (simple t.foldedTag a) = θ t K σ hp (t.orbitReflection a) := by
  obtain ⟨φ, hφ⟩ := exists_foldedEquiv t
  refine ⟨φ.symm.trans θEquiv, fun a => ?_⟩
  have : φ.symm (simple t.foldedTag a) = ⟨_, orbitReflection_mem' t a⟩ := by
    rw [MulEquiv.symm_apply_eq, hφ]
  simp only [MulEquiv.trans_apply, this]
  rfl

end

end Weyl

/-! ### The Tits system with the named simple reflections -/

section Named

variable (t : TwistTag) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
  [CharP K p]

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.Liftable] [h5 : Corpus.Exc.Descent] [h6 : Corpus.Exc.BorelNormal] [h7 : Corpus.Exc.Chevalley] [h8 : Corpus.ExcTw.GraphFixed]
include h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- **The Tits system of `Γ` with simple reflections `[ṅ_{r_a}]`.** -/
noncomputable def titsGF : TauCeti.TitsSystem (GF t K σ) where
  subgroupB := BF t K σ
  subgroupN := NF t K σ
  closure_subgroupB_union_subgroupN := (titsGF₀ t K σ hp).closure_subgroupB_union_subgroupN
  intersection_normal := (titsGF₀ t K σ hp).intersection_normal
  simple := Set.range fun a => θ t K σ hp (t.orbitReflection a)
  closure_simple := by
    intro _
    obtain ⟨Φ, hΦ⟩ := exists_weylEquiv₀ (t := t) (K := K) (σ := σ) (hp := hp)
    have : (Set.range fun a => θ t K σ hp (t.orbitReflection a)) =
        Φ.toMonoidHom '' Set.range (simple t.foldedTag) := by
      rw [← Set.range_comp]
      congr 1
      funext a
      exact (hΦ a).symm
    change Subgroup.closure (Set.range fun a => θ t K σ hp (t.orbitReflection a)) = ⊤
    rw [this, ← MonoidHom.map_closure, CoxeterSystem.subgroup_closure_range_simple,
      Subgroup.map_top_of_surjective _ Φ.surjective]
  exists_simpleRep_sq_mem := by
    rintro _ ⟨a, rfl⟩
    have ha := orbitReflection_mem' t a
    refine ⟨nrep (σ := σ) ha, (θ_of_mem ha).symm, ?_⟩
    have h := θ_mul_self (K := K) (σ := σ) (hp := hp) a
    rw [θ_of_mem ha, ← mk₀_mul] at h
    exact (mk₀_eq_one_iff _).1 h
  mul_doubleCoset_subset := by
    rintro _ ⟨a, rfl⟩
    have ha := orbitReflection_mem' t a
    refine ⟨nrep (σ := σ) ha, (θ_of_mem ha).symm, fun w => ?_⟩
    obtain ⟨v, hv, hvw⟩ := exists_θ_eq (t := t) (K := K) (σ := σ) (hp := hp)
      (mk₀ t K σ hp w)
    have e1 : doubleCoset ((nrep (σ := σ) ha : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) =
        cell (σ := σ) (t.orbitReflection a) := (cell_eq ha).symm
    have e2 : doubleCoset ((w : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) =
        cell (σ := σ) v := by
      rw [← bruhatCell_θ (hp := hp) hv, hvw, bruhatCell_mk₀]
    have e3 : doubleCoset ((nrep (σ := σ) ha * w : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) =
        cell (σ := σ) (t.orbitReflection a * v) := by
      rw [← bruhatCell_θ (hp := hp) (mul_mem ha hv), θ_simple_mul hv, hvw, θ_of_mem ha,
        ← mk₀_mul, bruhatCell_mk₀]
    change doubleCoset ((nrep (σ := σ) ha : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) *
        doubleCoset ((w : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) ⊆
      doubleCoset ((nrep (σ := σ) ha * w : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ) ∪
        doubleCoset ((w : NF t K σ) : GF t K σ) (BF t K σ) (BF t K σ)
    rw [e1, e2, e3]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rcases orbitLength_simple_mul t hv a with h | h
    · exact Or.inl (mul_mem_cell_of_eq
        ((Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.1 v hv a h) hx hy)
    · exact mul_mem_cell_of_subset
        ((Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.1 v hv a h).le hx hy
  exists_conj_not_mem := by
    rintro _ ⟨a, rfl⟩
    have ha := orbitReflection_mem' t a
    refine ⟨nrep (σ := σ) ha, (θ_of_mem ha).symm, ?_⟩
    by_contra! hall
    set n : GF t K σ := ((nrep (σ := σ) ha : NF t K σ) : GF t K σ)
    have hsq : n * n ∈ BF t K σ := by
      have h := θ_mul_self (K := K) (σ := σ) (hp := hp) a
      rw [θ_of_mem ha, ← mk₀_mul] at h
      exact (mk₀_eq_one_iff _).1 h
    have hmul := (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.1 _ ha a (by
      rw [orbitReflection_mul_self', orbitLength_one, orbitLength_orbitReflection])
    have hn : n ∈ cell (σ := σ) (t.orbitReflection a) := mem_cell_self ha
    have hnn : (n : ModGL t.tag K) ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
          graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) := by
      rw [hmul]; exact Or.inr hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hnn
    have hx' : (⟨x, (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.2.2.2 _ ha hx⟩ : GF t K σ) ∈
        cell (σ := σ) (t.orbitReflection a) := hx
    have hy' : (⟨y, (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.2.2.2 _ ha hy⟩ : GF t K σ) ∈
        cell (σ := σ) (t.orbitReflection a) := hy
    rw [cell_eq ha, mem_doubleCoset] at hx' hy'
    obtain ⟨b₁, hb₁, b₂, hb₂, hx''⟩ := hx'
    obtain ⟨b₃, hb₃, b₄, hb₄, hy''⟩ := hy'
    have hnB : n ∈ BF t K σ := by
      have he : n = ⟨x, (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.2.2.2 _ ha hx⟩ *
          ⟨y, (Corpus.ExcTw.GraphFixed.fixed_simple_Bruhat_multiplication t K σ).2.2.2.2.2 _ ha hy⟩ := Subtype.ext hxy.symm
      rw [he, hx'', hy'']
      have hc := hall ⟨b₂ * b₃, (BF t K σ).mul_mem hb₂ hb₃⟩
      have : b₁ * n * b₂ * (b₃ * n * b₄) = b₁ * ((n * (b₂ * b₃) * n⁻¹) * (n * n)) * b₄ := by
        group
      rw [this]
      exact (BF t K σ).mul_mem ((BF t K σ).mul_mem hb₁ ((BF t K σ).mul_mem hc hsq)) hb₄
    have h1 : n ∈ cell (σ := σ) (1 : WeylGroup t.tag) := by
      rw [cell_one]; exact hnB
    exact Set.disjoint_left.1 (Corpus.ExcTw.GraphFixed.disjoint_graphFixedRootBruhatCell (σ := σ.toRingHom)
      (orbitReflection_ne_one' t a)) hn h1

/-- **The Weyl group of `titsGF` is `W(t.foldedTag)`, simple reflections to simple
reflections.** -/
theorem exists_weylEquiv_titsGF : ∃ Φ : WeylGroup t.foldedTag ≃* (titsGF t K σ hp).WeylGroup,
    ∀ a, Φ (simple t.foldedTag a) ∈ (titsGF t K σ hp).simple := by
  obtain ⟨Φ, hΦ⟩ := exists_weylEquiv₀ (t := t) (K := K) (σ := σ) (hp := hp)
  exact ⟨Φ, fun a => ⟨a, (hΦ a).symm⟩⟩

end

end Named

end

end CFSGOutside.HallPaige.ExcTw
