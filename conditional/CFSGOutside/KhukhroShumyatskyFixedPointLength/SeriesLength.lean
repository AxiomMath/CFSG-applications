import CFSGOutside.KhukhroShumyatskyFixedPointLength.Definitions
import CFSGOutside.Common.UpperNonsolubleSeries

/-!
# Khukhro–Shumyatsky, fixed points: monotonicity and extension of the nonsoluble length

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. The nonsoluble length does not increase under surjections, is monotone for normal
subgroups, and satisfies `λ(X) ≤ λ(N) + λ(X/N)` (`NonsolubleLengthLE.extension`).
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

universe u

section Semisimple

/-- A normal subgroup of a finite direct product of nonabelian simple groups is again such a
product (namely of the factors it contains). -/
lemma isSemisimpleProd_of_normal {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, Group (S i)]
    (hS : ∀ i, IsSimpleGroup (S i)) (hnab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (W : Subgroup (∀ i, S i)) [hW : W.Normal] : IsSemisimpleProd W := by
  classical
  haveI := Fintype.ofFinite ι
  let I : Set ι := {i | ∀ s : S i, Pi.mulSingle i s ∈ W}
  have hcenter : ∀ i (z : S i), (∀ g, z * g = g * z) → z = 1 := by
    intro i z hz
    haveI := hS i
    rcases (inferInstance : (center (S i)).Normal).eq_bot_or_eq_top with h | h
    · have : z ∈ center (S i) := mem_center_iff.2 fun g => (hz g).symm
      rwa [h, mem_bot] at this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab i
      have : b ∈ center (S i) := h ▸ mem_top b
      exact hab (mem_center_iff.1 this a)
  have hout : ∀ w ∈ W, ∀ i ∉ I, w i = 1 := by
    intro w hw i hi
    haveI := hS i
    let Wi : Subgroup (S i) := W.comap (MonoidHom.mulSingle S i)
    have hWi : Wi = ⊥ := by
      rcases (hW.comap (MonoidHom.mulSingle S i)).eq_bot_or_eq_top with h | h
      · exact h
      · exact absurd (fun s => by
          have : s ∈ Wi := by
            show s ∈ comap (MonoidHom.mulSingle S i) W
            rw [h]; exact mem_top s
          exact this) hi
    refine hcenter i (w i) fun g => ?_
    have hc : w * Pi.mulSingle i g * w⁻¹ * (Pi.mulSingle i g)⁻¹ ∈ W := by
      have := hW.conj_mem _ (inv_mem hw) (Pi.mulSingle i g)
      simpa [mul_assoc] using mul_mem hw this
    have hc' : w * Pi.mulSingle i g * w⁻¹ * (Pi.mulSingle i g)⁻¹ =
        Pi.mulSingle i (w i * g * (w i)⁻¹ * g⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hc'] at hc
    have : w i * g * (w i)⁻¹ * g⁻¹ ∈ Wi := hc
    rw [hWi, mem_bot] at this
    have h2 := this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  let φ : W →* (∀ i : I, S i) :=
    { toFun := fun w i => (w : ∀ i, S i) i.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [mem_bot]
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · exact congrFun hw ⟨i, hi⟩
    · exact hout w w.2 i hi
  have hsurj : Function.Surjective φ := by
    intro f
    let g : ∀ i, S i := fun j => if h : j ∈ I then f ⟨j, h⟩ else 1
    have hg : g ∈ W := by
      rw [← Finset.noncommProd_mulSingle g]
      refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
      by_cases hj : j ∈ I
      · exact hj (g j)
      · simp [g, hj]
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    simp [φ, g, i.2]
  exact ⟨I, fun i => S i, fun i => inferInstance, inferInstance, fun i => hS i,
    fun i => hnab i, ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩⟩

end Semisimple

section Factors

variable {X : Type} [Group X] [Finite X]

lemma semisimpleFactor_inf {N M : Subgroup X} (K : Subgroup X) [N.Normal] [K.Normal]
    (h : SemisimpleFactor N M) : SemisimpleFactor (K ⊓ N) (K ⊓ M) := by
  obtain ⟨_, ι, S, _, hfin, hS, hnab, ⟨e⟩⟩ := h
  refine ⟨inferInstance, ?_⟩
  let ψ : (K ⊓ M : Subgroup X) →* M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' _).comp (inclusion inf_le_right)
  have hker : ψ.ker = (K ⊓ N).subgroupOf (K ⊓ M) := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
  set R := ψ.range
  haveI hR : R.Normal := by
    refine ⟨fun r hr q => ?_⟩
    obtain ⟨x, rfl⟩ := hr
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
    refine ⟨⟨(m : X) * x * (m : X)⁻¹, ‹K.Normal›.conj_mem _ (mem_inf.1 x.2).1 m,
      M.mul_mem (M.mul_mem m.2 (mem_inf.1 x.2).2) (M.inv_mem m.2)⟩, ?_⟩
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  haveI := hfin
  haveI : (R.map e.toMonoidHom).Normal := hR.map e.toMonoidHom e.surjective
  have hss := isSemisimpleProd_of_normal hS hnab (R.map e.toMonoidHom)
  exact hss.of_mulEquiv (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans (R.equivMapOfInjective _ e.injective))

lemma NonsolubleLengthLE.mono {h h' : ℕ} (hh : h ≤ h') (H : NonsolubleLengthLE X h) :
    NonsolubleLengthLE X h' :=
  nonsolubleLengthLE_iff_upperSeries.2 (eq_top_iff.2 (by
    rw [← nonsolubleLengthLE_iff_upperSeries.1 H]
    exact upperSeries_mono (by omega)))

end Factors


section Mono

lemma map_solvableRadical_le {Y Z : Type*} [Group Y] [Group Z] [Finite Y] (f : Y →* Z)
    (hf : Function.Surjective f) : (solvableRadical Y).map f ≤ solvableRadical Z := by
  haveI := isSolvable_solvableRadical (G := Y)
  refine le_solvableRadical
    (Normal.map inferInstance _ hf) ?_
  exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

/-- The upper nonsoluble series maps into the upper nonsoluble series of a quotient. -/
lemma map_upperSeries_le (f : X →* Y) (hf : Function.Surjective f) (j : ℕ) :
    (upperSeries X j).map f ≤ upperSeries Y j := by
  induction j with
  | zero => rw [upperSeries_zero, upperSeries_zero, Subgroup.map_bot]
  | succ j ih =>
    let φ : X ⧸ upperSeries X j →* Y ⧸ upperSeries Y j :=
      QuotientGroup.map _ _ f (map_le_iff_le_comap.1 ih)
    have hφ : Function.Surjective φ := by
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x, rfl⟩
    have key : ∀ (F : Subgroup (X ⧸ upperSeries X j)) (F' : Subgroup (Y ⧸ upperSeries Y j)),
        F.map φ ≤ F' → (F.comap (QuotientGroup.mk' _)).map f ≤ F'.comap (QuotientGroup.mk' _) := by
      rintro F F' hFF' _ ⟨x, hx, rfl⟩
      exact hFF' ⟨_, hx, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [upperSeries_odd, upperSeries_odd]
      exact key _ _ (map_solvableRadical_le φ hφ)
    · rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, upperSeries_even, upperSeries_even]
      exact key _ _ (map_layer_le φ hφ)

/-- `λ` does not increase under surjective homomorphisms. -/
lemma NonsolubleLengthLE.of_surjective {f : X →* Y} (hf : Function.Surjective f) {l : ℕ}
    (h : NonsolubleLengthLE X l) : NonsolubleLengthLE Y l := by
  rw [nonsolubleLengthLE_iff_upperSeries] at h ⊢
  have := map_upperSeries_le f hf (2 * l + 1)
  rwa [h, map_top_of_surjective f hf, top_le_iff] at this

lemma NonsolubleLengthLE.of_mulEquiv (e : X ≃* Y) {l : ℕ} (h : NonsolubleLengthLE X l) :
    NonsolubleLengthLE Y l :=
  NonsolubleLengthLE.of_surjective (f := e.toMonoidHom) e.surjective h

/-- The upper series of `X`, intersected with a normal subgroup `N`, lies in that of `N`. -/
lemma inf_upperSeries_le (N : Subgroup X) [N.Normal] (j : ℕ) :
    N ⊓ upperSeries X j ≤ (upperSeries N j).map N.subtype := by
  induction j with
  | zero =>
    rw [upperSeries_zero, inf_bot_eq]; exact bot_le
  | succ j ih =>
    have ih' : (upperSeries X j).subgroupOf N ≤ upperSeries N j := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := ih ⟨x.2, hx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    suffices h : (upperSeries X (j + 1)).subgroupOf N ≤ upperSeries N (j + 1) by
      rintro x ⟨hxN, hx⟩
      exact ⟨⟨x, hxN⟩, h hx, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · -- soluble step
      set A := upperSeries N (2 * k)
      set W := (upperSeries X (2 * k + 1)).subgroupOf N
      obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := X) k
      have hW : dA b W ≤ A := by
        refine le_trans ?_ ih'
        intro x hx
        rw [mem_subgroupOf]
        have : (dA b W).map N.subtype ≤ upperSeries X (2 * k) := by
          rw [map_dA]
          refine (dA_mono b ?_).trans hb
          rintro _ ⟨y, hy, rfl⟩; exact hy
        exact this ⟨x, hx, rfl⟩
      have hle : W.map (QuotientGroup.mk' A) ≤ solvableRadical (N ⧸ A) := by
        refine le_solvableRadical
          (Normal.map inferInstance _ (QuotientGroup.mk'_surjective A)) ?_
        rw [isSolvable_subgroup_iff]
        refine ⟨b, ?_⟩
        rw [← map_dA, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact hW
      intro x hx
      rw [upperSeries_odd]
      exact hle ⟨x, hx, rfl⟩
    · -- semisimple step
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring]
      set B := upperSeries N (2 * k + 1)
      set M := upperSeries X (2 * k + 1)
      set L := upperSeries X (2 * k + 2)
      have hss : SemisimpleFactor (N ⊓ M) (N ⊓ L) :=
        semisimpleFactor_inf N (semisimpleFactor_upperSeries k)
      obtain ⟨_, hQ⟩ := hss
      let f : (N ⊓ L : Subgroup X) ⧸ (N ⊓ M).subgroupOf (N ⊓ L) →* N ⧸ B :=
        QuotientGroup.lift _ ((QuotientGroup.mk' B).comp (inclusion inf_le_left)) (by
          intro x hx
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff]
          rw [mem_subgroupOf] at hx
          exact ih' (show ((inclusion inf_le_left x : N) : X) ∈ M from (mem_inf.1 hx).2))
      have hrange : f.range = (L.subgroupOf N).map (QuotientGroup.mk' B) := by
        ext y
        constructor
        · rintro ⟨q, rfl⟩
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
          exact ⟨inclusion inf_le_left x, (mem_inf.1 x.2).2, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨QuotientGroup.mk ⟨x, ⟨x.2, hx⟩⟩, rfl⟩
      have hle := range_le_layer_of_semisimple hQ f (by
        rw [hrange]; exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective B))
      rw [hrange] at hle
      intro x hx
      rw [upperSeries_even]
      exact hle ⟨x, hx, rfl⟩

/-- `λ(N) ≤ λ(X)` for a normal subgroup `N`. -/
lemma NonsolubleLengthLE.of_normal (N : Subgroup X) [N.Normal] {l : ℕ}
    (h : NonsolubleLengthLE X l) : NonsolubleLengthLE N l := by
  rw [nonsolubleLengthLE_iff_upperSeries] at h ⊢
  have := inf_upperSeries_le N (2 * l + 1)
  rw [h, inf_top_eq] at this
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := this x.2
  rwa [show y = x from Subtype.ext hyx] at hy

end Mono

section Extension

variable {X : Type} [Group X] [Finite X]

/-- A series from `1` up to a normal subgroup `N`. -/
structure LowSeries (X : Type) [Group X] (N : Subgroup X) (a : ℕ) where
  G : ℕ → Subgroup X
  normal : ∀ i, (G i).Normal
  mono : ∀ i < 2 * a + 1, G i ≤ G (i + 1)
  zero : G 0 = ⊥
  top : G (2 * a + 1) = N
  sol : ∀ i ≤ a, SolubleFactor (G (2 * i)) (G (2 * i + 1))
  semisimple : ∀ i < a, SemisimpleFactor (G (2 * i + 1)) (G (2 * i + 2))

/-- Concatenate a series `1 → N` with a series `N → X`. -/
def LowSeries.concat {N : Subgroup X} [N.Normal] {a b : ℕ} (t : LowSeries X N a)
    (s : NSeries X N b) : NSeries X ⊥ (a + b) := by
  let G' : ℕ → Subgroup X := fun i => if i ≤ 2 * a then t.G i else s.G (i - 2 * a)
  have hlo : ∀ i, i ≤ 2 * a → G' i = t.G i := fun i hi => if_pos hi
  have hhi : ∀ i, 2 * a < i → G' i = s.G (i - 2 * a) := fun i hi => if_neg (by omega)
  exact
  { G := G'
    normal := fun i => by
      by_cases hi : i ≤ 2 * a
      · rw [hlo i hi]; exact t.normal i
      · rw [hhi i (by omega)]; exact s.normal _
    mono := fun i hi => by
      by_cases h1 : i < 2 * a
      · rw [hlo i h1.le, hlo (i + 1) h1]; exact t.mono i (by omega)
      · by_cases h2 : i = 2 * a
        · subst h2
          rw [hlo _ le_rfl, hhi _ (by omega), show 2 * a + 1 - 2 * a = 0 + 1 by omega]
          have h3 := t.mono (2 * a) (by omega)
          have h4 := s.mono 0 (by omega)
          rw [t.top] at h3; rw [s.zero] at h4
          exact h3.trans h4
        · rw [hhi i (by omega), hhi (i + 1) (by omega),
            show i + 1 - 2 * a = i - 2 * a + 1 by omega]
          exact s.mono _ (by omega)
    zero := by rw [hlo 0 (Nat.zero_le _), t.zero]
    top := by
      rw [hhi _ (by omega), show 2 * (a + b) + 1 - 2 * a = 2 * b + 1 by omega]; exact s.top
    sol := fun i hi => by
      by_cases h1 : i < a
      · rw [hlo _ (by omega), hlo _ (by omega)]
        exact t.sol i h1.le
      · by_cases h2 : i = a
        · subst h2
          rw [hlo _ le_rfl, hhi _ (by omega), show 2 * i + 1 - 2 * i = 1 by omega]
          haveI := t.normal (2 * i)
          haveI := s.normal 0
          obtain ⟨k, hk⟩ := solubleFactor_iff.1 (t.sol i le_rfl)
          obtain ⟨j, hj⟩ := solubleFactor_iff.1 (s.sol 0 (Nat.zero_le _))
          rw [t.top] at hk
          rw [s.zero] at hj
          refine solubleFactor_iff.2 ⟨k + j, ?_⟩
          rw [dA_add]
          exact (dA_mono k hj).trans hk
        · rw [hhi _ (by omega), hhi _ (by omega), show 2 * i - 2 * a = 2 * (i - a) by omega,
            show 2 * i + 1 - 2 * a = 2 * (i - a) + 1 by omega]
          exact s.sol _ (by omega)
    semisimple := fun i hi => by
      by_cases h1 : i < a
      · rw [hlo _ (by omega), hlo _ (by omega)]
        exact t.semisimple i h1
      · rw [hhi _ (by omega), hhi _ (by omega), show 2 * i + 1 - 2 * a = 2 * (i - a) + 1 by omega,
          show 2 * i + 2 - 2 * a = 2 * (i - a) + 2 by omega]
        exact s.semisimple _ (by omega) }

lemma upperSeries_map_normal (N : Subgroup X) [hN : N.Normal] (j : ℕ) :
    ((upperSeries N j).map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h := map_upperSeries (MulAut.conjNormal g : MulAut N) j
  have hmem : (MulAut.conjNormal g : MulAut N) y ∈ upperSeries N j := by
    rw [← h]; exact ⟨y, hy, rfl⟩
  exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩

/-- Factor isomorphism along an injective homomorphism. -/
noncomputable def mapFactorEquiv {Z : Type} [Group Z] (f : Z →* X)
    (hf : Function.Injective f) (A B : Subgroup Z) [(A.subgroupOf B).Normal]
    [((A.map f).subgroupOf (B.map f)).Normal] :
    (B.map f) ⧸ (A.map f).subgroupOf (B.map f) ≃* B ⧸ A.subgroupOf B := by
  let e0 := B.equivMapOfInjective f hf
  refine (QuotientGroup.congr (A.subgroupOf B) ((A.map f).subgroupOf (B.map f)) e0 ?_).symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    rw [mem_subgroupOf]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [mem_subgroupOf] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨⟨w, hwB⟩, rfl⟩ := e0.surjective x
    have : z = w := hf (by rw [hzx]; rfl)
    subst this
    exact ⟨⟨z, hwB⟩, (mem_subgroupOf).2 hz, rfl⟩

/-- **Extension**: `λ(X) ≤ λ(N) + λ(X/N)`. -/
lemma NonsolubleLengthLE.extension (N : Subgroup X) [hN : N.Normal] {a b : ℕ}
    (hNa : NonsolubleLengthLE N a) (hQ : NonsolubleLengthLE (X ⧸ N) b) :
    NonsolubleLengthLE X (a + b) := by
  have htop := upperSeries_eq_top_of_nonsolubleLengthLE hNa
  obtain ⟨sQ⟩ := hQ
  have s := (sQ.comap (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).cast
    (QuotientGroup.ker_mk' N)
  let t : LowSeries X N a :=
    { G := fun i => (upperSeries N i).map N.subtype
      normal := fun i => upperSeries_map_normal N i
      mono := fun i _ => map_mono (upperSeries_le_succ i)
      zero := by rw [upperSeries_zero, Subgroup.map_bot]
      top := by rw [htop, ← MonoidHom.range_eq_map, range_subtype]
      sol := fun i _ => by
        haveI := upperSeries_map_normal N (2 * i)
        obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := N) i
        exact solubleFactor_iff.2 ⟨b, by rw [← map_dA]; exact map_mono hb⟩
      semisimple := fun i _ => by
        haveI := upperSeries_map_normal N (2 * i + 1)
        obtain ⟨_, h⟩ := semisimpleFactor_upperSeries (X := N) i
        exact ⟨inferInstance, h.of_mulEquiv (mapFactorEquiv N.subtype N.subtype_injective _ _)⟩ }
  exact ⟨t.concat s⟩

end Extension

end CFSGOutside.KhukhroShumyatskyFixedPointLength
