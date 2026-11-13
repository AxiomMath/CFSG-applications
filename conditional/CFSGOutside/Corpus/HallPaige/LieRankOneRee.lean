import CFSGOutside.Corpus.HallPaige.LieExcChevalley
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.CharP.Frobenius

/-!
# Corpus input for the small Ree groups `²G₂(q)`

The small Ree group `ReeTag.G2.reeGamma K a ≤ GL(L(K))` of the corpus (the fixed points of the
exceptional automorphism times the `a`-th power of the Frobenius on the adjoint Chevalley group
of type `G₂` over `K`, `|K| = 3^{2a+1}`), its unipotent and torus subgroups, and the corpus
theorems used for the Hall–Paige theorem: the bridge to the TauCeti carrier, the Bruhat
decomposition with unique expressions, the inversion of the torus by the longest Weyl element,
the coordinates of `U` and `T`, the prime-field word identities
(`ree_G2_prime_field_words`) and `n² = 1`.

All definitions are copied verbatim from AxiomMath/CFSG @ 69cb972 (only `@[expose]` and the
module-system keywords are dropped, and all names are put in the namespace
`CFSGOutside.Corpus.Ree`); the Chevalley definitions are those of `CFSGOutside.Corpus.HallPaige.LieExcChevalley`.
Each docstring gives the corpus name and file:line. Corpus theorems are stated as classes with
their exact statements; proof fields of copied definitions use restated corpus lemmas.
-/

set_option autoImplicit false

namespace CFSGOutside.Corpus.Ree

noncomputable section

open CFSGOutside.Corpus.Exc
open scoped Matrix

/-! ### `CFSG/Blueprint/Chevalley.lean`, `ChevalleyPinned.lean`, `BorelTits/WeightedMatrix.lean` -/

section Blueprint

variable {τ : Tag} {R : Type} [CommRing R]

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

variable (τ R) in
/-- Corpus: `CFSG.Blueprint.Chevalley.negUnipotent`, CFSG/Blueprint/ChevalleyPinned.lean:252. -/
def negUnipotent : Subgroup (Module.End R (RootModule τ R))ˣ :=
  rootSpan τ R {α | RootPred.IsRoot τ α ∧ height α < 0}

end

end Blueprint

/-- The Weyl group of a Chevalley type is finite. -/
class FiniteWeylGroup : Prop where
  /-- Corpus: the instance `CFSG.LieType.Chevalley.instFiniteWeylGroup`,
  CFSG/LieType/Chevalley/WeylRoots.lean:98. -/
  instFiniteWeylGroup {τ : Tag} : Finite (WeylGroup τ)

attribute [instance] Corpus.Ree.FiniteWeylGroup.instFiniteWeylGroup

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- The corpus axiom `finite_modGL` as an instance (used by `bijective_of_finite` below, as in
the corpus). -/
instance instFiniteModGL {τ : Tag} {K : Type} [Field K] [Finite K] : Finite (ModGL τ K) :=
  Corpus.Exc.Chevalley.finite_modGL

end

/-! ### `CFSG/LieType/Ree/Duality.lean` -/

/-- Corpus: `CFSG.LieType.Ree.ReeTag`, CFSG/LieType/Ree/Duality.lean:13. -/
inductive ReeTag
  | G2 | F4
  deriving DecidableEq, Repr

namespace ReeTag

/-- Corpus: `CFSG.LieType.Ree.ReeTag.tag`, CFSG/LieType/Ree/Duality.lean:19. -/
def tag : ReeTag → Tag
  | G2 => .G2
  | F4 => .F4

/-- Corpus: `CFSG.LieType.Ree.ReeTag.prime`, CFSG/LieType/Ree/Duality.lean:23. -/
def prime : ReeTag → ℕ
  | G2 => 3
  | F4 => 2

/-- Corpus: `CFSG.LieType.Ree.ReeTag.longSet`, CFSG/LieType/Ree/Duality.lean:27. -/
def longSet : (t : ReeTag) → Finset (Fin t.tag.rank)
  | G2 => ({0} : Finset (Fin 2))
  | F4 => ({0, 1} : Finset (Fin 4))

/-- Corpus: `CFSG.LieType.Ree.ReeTag.perm`, CFSG/LieType/Ree/Duality.lean:31. -/
def perm : (t : ReeTag) → Equiv.Perm (Fin t.tag.rank)
  | G2 => (Equiv.swap 0 1 : Equiv.Perm (Fin 2))
  | F4 => (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))

/-- Corpus: `CFSG.LieType.Ree.ReeTag.scale`, CFSG/LieType/Ree/Duality.lean:35. -/
def scale (t : ReeTag) (i : Fin t.tag.rank) : ℕ :=
  if i ∈ t.longSet then t.prime else 1

/-- Corpus: `CFSG.LieType.Ree.ReeTag.dualMap`, CFSG/LieType/Ree/Duality.lean:42. -/
def dualMap (t : ReeTag) : (Fin t.tag.rank → ℚ) →ₗ[ℚ] (Fin t.tag.rank → ℚ) where
  toFun v j := (t.scale (t.perm.symm j) : ℚ) * v (t.perm.symm j)
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Corpus: `CFSG.LieType.Ree.ReeTag.quadForm`, CFSG/LieType/Ree/Duality.lean:61. -/
def quadForm (t : ReeTag) (α : Fin t.tag.rank → ℤ) : ℤ :=
  α ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ α)

/-- Corpus: `CFSG.LieType.Ree.ReeTag.lengthParam`, CFSG/LieType/Ree/Duality.lean:64. -/
def lengthParam (t : ReeTag) (α : Fin t.tag.rank → ℤ) : ℚ :=
  (t.quadForm α : ℚ) / 2

/-- Corpus: `CFSG.LieType.Ree.ReeTag.duality`, CFSG/LieType/Ree/Duality.lean:67. -/
def duality (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℚ :=
  (t.lengthParam α)⁻¹ • t.dualMap fun j => (α j : ℚ)

section
variable [h0 : Corpus.Exc.RootPred]
include h0

/-- Corpus: `CFSG.LieType.Ree.ReeTag.shortRoots`, CFSG/LieType/Ree/Duality.lean:70. -/
def shortRoots (t : ReeTag) : Set (Fin t.tag.rank → ℤ) :=
  {α | RootPred.IsRoot t.tag α ∧ t.lengthParam α = 1}

/-- Corpus: `CFSG.LieType.Ree.ReeTag.longRoots`, CFSG/LieType/Ree/Duality.lean:73. -/
def longRoots (t : ReeTag) : Set (Fin t.tag.rank → ℤ) :=
  {α | RootPred.IsRoot t.tag α ∧ t.lengthParam α = t.prime}

end

/-- Corpus: `CFSG.LieType.Ree.ReeTag.dualMapInt`, CFSG/LieType/Ree/Duality.lean:76. -/
def dualMapInt (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℤ :=
  fun j => (t.scale (t.perm.symm j) : ℤ) * α (t.perm.symm j)

/-- Corpus: `CFSG.LieType.Ree.ReeTag.dualRoot`, CFSG/LieType/Ree/Duality.lean:79. -/
def dualRoot (t : ReeTag) (α : Fin t.tag.rank → ℤ) : Fin t.tag.rank → ℤ :=
  fun j => 2 * t.dualMapInt α j / t.quadForm α

/-! ### `CFSG/LieType/Ree/ShortModule.lean`, `Faithful.lean` -/

variable (t : ReeTag)

/-- Corpus: `CFSG.LieType.Ree.ReeTag.sign`, CFSG/LieType/Ree/ShortModule.lean:93. -/
def sign (α : Fin t.tag.rank → ℤ) : ℤ :=
  if t = G2 ∧ (List.ofFn α = [2, 3] ∨ List.ofFn α = [-2, -3]) then -1 else 1

variable (R : Type) [CommRing R]

variable {t}

end ReeTag

/-! ### `CFSG/LieType/Ree/Endo.lean` -/

section Entrywise

variable {τ : Tag} {K : Type} [Field K] (σ : K →+* K)

end Entrywise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K]

/-- Corpus: the instance `CFSG.LieType.Ree.ReeTag.fact_prime`, CFSG/LieType/Ree/Endo.lean:161. -/
instance fact_prime (t : ReeTag) : Fact t.prime.Prime :=
  ⟨by cases t; exacts [Nat.prime_three, Nat.prime_two]⟩

/-! ### `CFSG/LieType/Ree/ExceptionalAutomorphismData.lean`, `FixedSubgroupData.lean` -/

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime]

/-- The automorphism of the small Ree groups, as a parameter. In the corpus
(`CFSG.LieType.Ree.ReeTag.finiteReeAut`, CFSG/LieType/Ree/ExceptionalAutomorphismData.lean:26) it is the product of the
exceptional endomorphism and a power of the Frobenius automorphism, which are built from choices and from the
faithfulness of the short-root representation; its fixed points are the Ree group `Γ`. Comparing such a definition with
another copy by unfolding is not possible, so every copied definition below that mentions it takes this class instead,
and the clean build instantiates the class with the corpus automorphism. -/
class ReeAut [Corpus.Exc.RootPred] [Corpus.Exc.Ops] : Type 1 where
  finiteReeAut (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ) : MulAut (adjointGroup t.tag K)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut]
include h0 h1 h2

/-- Corpus: `CFSG.LieType.Ree.ReeTag.finiteReeAut`, CFSG/LieType/Ree/ExceptionalAutomorphismData.lean:26. -/
def finiteReeAut (a : ℕ) : MulAut (adjointGroup t.tag K) := ReeAut.finiteReeAut t K a

/-- Corpus: `CFSG.LieType.Ree.ReeTag.finiteReeFixedGroup`,
CFSG/LieType/Ree/ExceptionalAutomorphismData.lean:31. -/
def finiteReeFixedGroup
    (a : ℕ) : Subgroup (adjointGroup t.tag K) :=
  (t.finiteReeAut K a).toMonoidHom.eqLocus (MonoidHom.id _)

end

variable (a : ℕ)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut]
include h0 h1 h2

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeGamma`, CFSG/LieType/Ree/FixedSubgroupData.lean:17. -/
def reeGamma :
    Subgroup (ModGL t.tag K) :=
  (t.finiteReeFixedGroup K a).map (adjointGroup t.tag K).subtype

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedBorel`, CFSG/LieType/Ree/FixedSubgroupData.lean:21. -/
def reeFixedBorel
    : Subgroup (ModGL t.tag K) :=
  borelGroup t.tag K ⊓ t.reeGamma K a

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedTorus`, CFSG/LieType/Ree/FixedSubgroupData.lean:25. -/
def reeFixedTorus
    : Subgroup (ModGL t.tag K) :=
  torusGroup t.tag K ⊓ t.reeGamma K a

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedPosUnipotent`,
CFSG/LieType/Ree/FixedSubgroupData.lean:33. -/
def reeFixedPosUnipotent
    : Subgroup (ModGL t.tag K) :=
  posUnipotent t.tag K ⊓ t.reeGamma K a

/-- Corpus: `CFSG.LieType.Ree.ReeTag.reeFixedNegUnipotent`,
CFSG/LieType/Ree/FixedSubgroupData.lean:37. -/
def reeFixedNegUnipotent
    : Subgroup (ModGL t.tag K) :=
  negUnipotent t.tag K ⊓ t.reeGamma K a

end

end ReeTag

open ReeTag

/-! ### Small Ree coordinates: `CFSG/LieType/Ree/SmallReeCollection.lean`,
`SmallReeCoordinateData.lean`, `SmallReeTorusAction.lean`, `FixedPositiveBlocks.lean`,
`G2PrimeFieldWords.lean` -/

/-- Corpus: `CFSG.LieType.Ree.smallReeRoot`, CFSG/LieType/Ree/SmallReeCollection.lean:11. -/
def smallReeRoot (i : Fin 6) : Fin Tag.G2.rank → ℤ :=
  ![![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]] i

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.LieType.Ree.smallReeX`, CFSG/LieType/Ree/SmallReeCollection.lean:14. -/
def smallReeX
    (R : Type) [CommRing R] (i : Fin 6) (c : R) :
    (Module.End R (RootModule Tag.G2 R))ˣ :=
  pinnedX Tag.G2 R (smallReeRoot i) c

end

/-- Corpus: `CFSG.LieType.Ree.smallReeSigma`, CFSG/LieType/Ree/SmallReeCoordinateData.lean:12. -/
def smallReeSigma (a : ℕ) {K : Type} [CommRing K] (x : K) : K :=
  x ^ (3 * 3 ^ a)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.LieType.Ree.smallReeCoord`, CFSG/LieType/Ree/SmallReeCoordinateData.lean:15. -/
def smallReeCoord
    (a : ℕ) (K : Type) [CommRing K] (t b c : K) :
    (Module.End K (RootModule Tag.G2 K))ˣ :=
  smallReeX K 0 t * smallReeX K 1 (smallReeSigma a t) * smallReeX K 2 b * smallReeX K 3 c *
    smallReeX K 4 (smallReeSigma a b - t ^ 3 * smallReeSigma a t) *
    smallReeX K 5 (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2)

/-- Corpus: `CFSG.LieType.Ree.smallReeTorusElt`, CFSG/LieType/Ree/SmallReeTorusAction.lean:13. -/
def smallReeTorusElt
    (a : ℕ) (K : Type) [CommRing K] (s : Kˣ) :
    (Module.End K (RootModule Tag.G2 K))ˣ :=
  torusElt Tag.G2 K ⟨0, by decide⟩ s * torusElt Tag.G2 K ⟨1, by decide⟩ (s ^ 3 ^ a)

/-- Corpus: `CFSG.Walter.Ree.Model.smallReeH`, CFSG/Walter/Ree/Model/Cells.lean:18. -/
abbrev smallReeH
    (a : ℕ) (K : Type) [Field K] (s : Kˣ) : ModGL ReeTag.G2.tag K :=
  smallReeTorusElt a K s

end

namespace ReeTag

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2Root11`, CFSG/LieType/Ree/FixedPositiveBlocks.lean:58. -/
def g2Root11 : Fin G2.tag.rank → ℤ := ![1, 1]

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2Root13`, CFSG/LieType/Ree/FixedPositiveBlocks.lean:60. -/
def g2Root13 : Fin G2.tag.rank → ℤ := ![1, 3]

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2Root12`, CFSG/LieType/Ree/G2PrimeFieldWords.lean:66. -/
def g2Root12 : Fin G2.tag.rank → ℤ := ![1, 2]

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2Root23`, CFSG/LieType/Ree/G2PrimeFieldWords.lean:68. -/
def g2Root23 : Fin G2.tag.rank → ℤ := ![2, 3]

section Elements

variable (R : Type) [CommRing R]

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Exc.ParameterAddition] [h3 : Corpus.Exc.BorelNormal] [h4 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2U₀`, CFSG/LieType/Ree/G2PrimeFieldWords.lean:143. -/
def g2U₀
    : (Module.End R (RootModule G2.tag R))ˣ :=
  pinnedX G2.tag R g2Root12 1 * pinnedX G2.tag R g2Root23 1

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2U₁`, CFSG/LieType/Ree/G2PrimeFieldWords.lean:147. -/
def g2U₁
    : (Module.End R (RootModule G2.tag R))ˣ :=
  pinnedX G2.tag R g2Root11 1 * pinnedX G2.tag R g2Root13 1

/-- Corpus: `CFSG.LieType.Ree.ReeTag.g2U₂`, CFSG/LieType/Ree/G2PrimeFieldWords.lean:151. -/
def g2U₂
    : (Module.End R (RootModule G2.tag R))ˣ :=
  xUnit G2.tag R ⟨1, by decide⟩ 1 * xUnit G2.tag R ⟨0, by decide⟩ 1 *
    pinnedX G2.tag R g2Root13 (-1) * pinnedX G2.tag R g2Root23 (-1)

end

end Elements

end ReeTag

/-- Corpus: the instance `CFSG.AGLEmbedding.ReeModel.instCharPGaloisFieldG2`,
CFSG/LocalAnalysis/AGLEmbedding/KFactProofs/ReeModel.lean:52. -/
instance instCharPGaloisFieldG2 (n : ℕ) : CharP (GaloisField 3 n) ReeTag.G2.prime :=
  inferInstanceAs (CharP (GaloisField 3 n) 3)

/-! ### Corpus theorems -/

/-- The Ree groups: identification with the catalogue, Bruhat data and small Ree groups. -/
class ReeModel [Corpus.Exc.RootPred] [Corpus.Exc.Ops] [Corpus.Ree.ReeTag.ReeAut] [Corpus.Exc.ParameterAddition] : Prop where
  /-- Corpus: `CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv`,
  CFSG/LocalAnalysis/AGLEmbedding/KFactProofs/ReeModel.lean:55. The small Ree group of the corpus is
  the TauCeti carrier of `²G₂(3^{2a+1})`. -/
  nonempty_reeGamma_equiv (a : ℕ) (ha : 1 ≤ a)
    (hv : (TauCeti.LieTypeIndex.reeG2 a).Valid) :
    Nonempty (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.reeG2 a, hv⟩)
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.canonicalRep_longest_conj_torus`,
  CFSG/LieType/Ree/NormalPositiveGeneration.lean:57. -/
  canonicalRep_longest_conj_torus {t : ReeTag} {K : Type} [Field K] [Finite K]
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    {h : ModGL t.tag K} (hh : h ∈ torusGroup t.tag K) :
    canonicalRep (coxeterSystem t.tag) K w₀ * h * (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ =
      h⁻¹
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.canonicalRep_longest_mem_reeGamma`,
  CFSG/LieType/Ree/SmallReeBorelCosetAction.lean:70. -/
  canonicalRep_longest_mem_reeGamma
    {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ} {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    canonicalRep (coxeterSystem G2.tag) K w₀ ∈ G2.reeGamma K a
  /-- Corpus: `CFSG.Walter.Ree.Model.reeGamma_G2_cases`, CFSG/Walter/Ree/Model/Cells.lean:247.
  The Bruhat decomposition `Γ = B ⊔ U T n U`. -/
  reeGamma_G2_cases
    {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ} {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeGamma K a) :
    (∃ u ∈ G2.reeFixedPosUnipotent K a, ∃ h ∈ G2.reeFixedTorus K a, u * h = g) ∨
      (g ∉ G2.reeFixedBorel K a ∧ ∃ u ∈ G2.reeFixedPosUnipotent K a,
        ∃ h ∈ G2.reeFixedTorus K a, ∃ v ∈ G2.reeFixedPosUnipotent K a,
          u * h * canonicalRep (coxeterSystem G2.tag) K w₀ * v = g)
  /-- Corpus: `CFSG.Walter.Ree.Model.eq_of_mul_canonicalRep_mul_eq`,
  CFSG/Walter/Ree/Model/Cells.lean:277. Uniqueness of the Bruhat expressions. -/
  eq_of_mul_canonicalRep_mul_eq
    {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ} {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
    {u u' h h' v v' : ModGL G2.tag K}
    (hu : u ∈ G2.reeFixedPosUnipotent K a) (hu' : u' ∈ G2.reeFixedPosUnipotent K a)
    (hh : h ∈ G2.reeFixedTorus K a) (hh' : h' ∈ G2.reeFixedTorus K a)
    (hv : v ∈ G2.reeFixedPosUnipotent K a) (hv' : v' ∈ G2.reeFixedPosUnipotent K a)
    (heq : u * h * canonicalRep (coxeterSystem G2.tag) K w₀ * v =
      u' * h' * canonicalRep (coxeterSystem G2.tag) K w₀ * v') : u = u' ∧ h = h' ∧ v = v'
  /-- Corpus: `CFSG.LieType.Ree.small_Ree_positive_fixed_coordinates`,
  CFSG/LieType/Ree/SmallReeFixedCoordinates.lean:329. -/
  small_Ree_positive_fixed_coordinates
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × K × K => smallReeCoord a K p.1 p.2.1 p.2.2) Set.univ
        (ReeTag.G2.reeFixedPosUnipotent K a : Set (ModGL ReeTag.G2.tag K)) ∧
      Nat.card (ReeTag.G2.reeFixedPosUnipotent K a) = (3 ^ (2 * a + 1)) ^ 3
  /-- Corpus: `CFSG.LieType.Ree.small_Ree_positive_torus_action`,
  CFSG/LieType/Ree/SmallReeTorusAction.lean:171. -/
  small_Ree_positive_torus_action
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∃ φ : Kˣ ≃* ReeTag.G2.reeFixedTorus K a,
      ∀ s, (φ s : ModGL ReeTag.G2.tag K) = smallReeTorusElt a K s) ∧
    (∀ (s : Kˣ) (t b c : K),
      smallReeTorusElt a K s * smallReeCoord a K t b c * (smallReeTorusElt a K s)⁻¹ =
        smallReeCoord a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t)
          (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b) ((s : K) ^ 3 ^ a * c)) ∧
    Function.Bijective (fun s : Kˣ => s ^ (2 * 3 ^ a - 1)) ∧
    Nat.card (Set.range fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))) = (3 ^ (2 * a + 1) - 1) / 2
  /-- Corpus: `CFSG.LieType.Ree.ReeTag.ree_G2_prime_field_words`,
  CFSG/LieType/Ree/G2PrimeFieldWords.lean:345. Word identities over the prime field, verified in
  the corpus by kernel computation (`constCheck`): in particular `h(-1) ∈ U V V V U V` and
  `n ∈ U V U`. -/
  ree_G2_prime_field_words
    (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ)
    {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    (g2U₀ K ∈ G2.reeFixedPosUnipotent K a ∧ g2U₁ K ∈ G2.reeFixedPosUnipotent K a ∧
      g2U₂ K ∈ G2.reeFixedPosUnipotent K a) ∧
    (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a ∧
      canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a ∧
      canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₂ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ ∈ G2.reeFixedNegUnipotent K a) ∧
    torusElt G2.tag K ⟨0, by decide⟩ (-1) * torusElt G2.tag K ⟨1, by decide⟩ (-1) =
      g2U₀ K * (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) * g2U₂ K *
        (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) ∧
    canonicalRep (coxeterSystem G2.tag) K w₀ =
      g2U₁ K * (canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K *
          (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹) * g2U₁ K
  /-- Corpus: `CFSG.Walter.Ree.Model.smallReeE8_relations`, CFSG/Walter/Ree/Model/Fusion.lean:216.
  In particular `n² = 1`. -/
  smallReeE8_relations
    {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
    (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀) :
    Commute (smallReeH a K (-1)) (canonicalRep (coxeterSystem G2.tag) K w₀) ∧
    Commute (smallReeH a K (-1))
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) ∧
    Commute (canonicalRep (coxeterSystem G2.tag) K w₀)
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) ∧
    smallReeH a K (-1) * smallReeH a K (-1) = 1 ∧
    canonicalRep (coxeterSystem G2.tag) K w₀ * canonicalRep (coxeterSystem G2.tag) K w₀ = 1 ∧
    (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) *
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) = 1

end

end CFSGOutside.Corpus.Ree
