import CFSGOutside.HallPaige.Lie.RankOneWords
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.Corpus.HallPaige.LieRankOneRee
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The catalogue case `²G₂(q)`

The small Ree group `Γ = ReeTag.G2.reeGamma K a` of the corpus (`|K| = q = 3^{2a+1}`) with
`U = Γ ∩ U⁺`, `T = Γ ∩ H` (cyclic of order `q - 1`) and `n` the longest Weyl element is a
rank-one split group (corpus Bruhat decomposition with unique expressions). The corpus
prime-field word identities give `h(-1) ∈ U V V V U V` and `n ∈ U V U`; with
`CFSGOutside.HallPaige.rankOne_tn_mem_of_words` this gives `T n ⊆ UnUnU` (Wilcox, Lemma 20), and Wilcox's
Lemma 23 (`CFSGOutside.HallPaige.hasCompleteMapping_of_rankOne_split`) gives a complete mapping of `Γ`
(`CFSGOutside.HallPaige.Ree.hasCompleteMapping_reeGamma`), hence `CFSGOutside.HallPaige.catalogueCase_reeG2`.
-/

namespace CFSGOutside.HallPaige.Ree

noncomputable section

open Corpus.Exc Corpus.Ree Corpus.Ree.ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
  (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley]
include h0 h1 h2 h3 h4 h5

/-- The unipotent subgroup of `Γ`. -/
abbrev Ug (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ) :
    Subgroup (G2.reeGamma K a) :=
  (G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeGamma K a)

/-- The torus of `Γ`. -/
abbrev Tg (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ) :
    Subgroup (G2.reeGamma K a) :=
  (G2.reeFixedTorus K a).subgroupOf (G2.reeGamma K a)

theorem mem_Ug {x : G2.reeGamma K a} :
    x ∈ Ug K a ↔ (x : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a :=
  Subgroup.mem_subgroupOf

theorem mem_Tg {x : G2.reeGamma K a} :
    x ∈ Tg K a ↔ (x : ModGL G2.tag K) ∈ G2.reeFixedTorus K a :=
  Subgroup.mem_subgroupOf

theorem reeFixedPosUnipotent_le : G2.reeFixedPosUnipotent K a ≤ G2.reeGamma K a :=
  fun _ h => (Subgroup.mem_inf.1 h).2

theorem reeFixedTorus_le : G2.reeFixedTorus K a ≤ G2.reeGamma K a :=
  fun _ h => (Subgroup.mem_inf.1 h).2

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley] [h6 : Corpus.Ree.ReeModel]
include h0 h1 h2 h3 h4 h5 h6

include hK in
theorem hTU : ∀ t ∈ Tg K a, ∀ u ∈ Ug K a, t * u * t⁻¹ ∈ Ug K a := by
  intro t ht u hu
  obtain ⟨⟨φ, hφ⟩, hconj, -, -⟩ := Corpus.Ree.ReeModel.small_Ree_positive_torus_action a K hK
  obtain ⟨hbij, -⟩ := Corpus.Ree.ReeModel.small_Ree_positive_fixed_coordinates a K hK
  rw [mem_Tg] at ht
  rw [mem_Ug] at hu ⊢
  obtain ⟨s, hs⟩ := φ.surjective ⟨_, ht⟩
  obtain ⟨⟨p, q, r⟩, -, hp⟩ := hbij.2.2 hu
  have hts : (t : ModGL G2.tag K) = smallReeTorusElt a K s := by
    rw [← hφ, hs]
  have hup : (u : ModGL G2.tag K) = smallReeCoord a K p q r := hp.symm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hts, hup]
  have hm := hbij.1 (Set.mem_univ (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * p,
    ((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * q, (s : K) ^ 3 ^ a * r))
  simp only at hm
  erw [hconj s p q r]
  exact hm

/-- The longest Weyl element in `Γ`. -/
noncomputable def ng : G2.reeGamma K a :=
  ⟨canonicalRep (coxeterSystem G2.tag) K w₀, Corpus.Ree.ReeModel.canonicalRep_longest_mem_reeGamma hw₀⟩

include hK hw₀ in
theorem ng_mul_ng : (ng hw₀ : G2.reeGamma K a) * ng hw₀ = 1 :=
  Subtype.ext (Corpus.Ree.ReeModel.smallReeE8_relations hK hw₀).2.2.2.2.1

theorem coe_ng : ((ng hw₀ : G2.reeGamma K a) : ModGL G2.tag K) =
    canonicalRep (coxeterSystem G2.tag) K w₀ := rfl

include hK hw₀ in
theorem coe_ng_inv : (canonicalRep (coxeterSystem G2.tag) K w₀)⁻¹ =
    canonicalRep (coxeterSystem G2.tag) K w₀ :=
  inv_eq_of_mul_eq_one_right (Corpus.Ree.ReeModel.smallReeE8_relations hK hw₀).2.2.2.2.1

include hw₀ in
theorem hUT : ∀ u ∈ Ug K a, u ∈ Tg K a → u = 1 := by
  intro u hu ht
  rw [mem_Ug] at hu
  rw [mem_Tg] at ht
  have h1U : (1 : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a := Subgroup.one_mem _
  have h1T : (1 : ModGL G2.tag K) ∈ G2.reeFixedTorus K a := Subgroup.one_mem _
  have := (Corpus.Ree.ReeModel.eq_of_mul_canonicalRep_mul_eq hw₀ hu h1U h1T ht h1U h1U
    (by simp)).1
  exact Subtype.ext this

include hK hw₀ in
theorem hV : ∀ u ∈ Ug K a, ng hw₀ * u * ng hw₀ ∈ borelOf (Ug K a) (Tg K a) (hTU hK) → u = 1 := by
  rintro u hu ⟨t, ht, u', hu', h⟩
  rw [mem_Ug] at hu hu'
  rw [mem_Tg] at ht
  set N := canonicalRep (coxeterSystem G2.tag) K w₀
  have hNN : N * N = 1 := (Corpus.Ree.ReeModel.smallReeE8_relations hK hw₀).2.2.2.2.1
  have h' : N * (u : ModGL G2.tag K) * N = t * u' := by
    have := congrArg Subtype.val h
    simpa [coe_ng] using this
  have htu : (t : ModGL G2.tag K) * u' * (t : ModGL G2.tag K)⁻¹ ∈ G2.reeFixedPosUnipotent K a := by
    have := (mem_Ug).1 (hTU hK t ((mem_Tg).2 ht) u' ((mem_Ug).2 hu'))
    simpa using this
  have h1U : (1 : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a := Subgroup.one_mem _
  have h1T : (1 : ModGL G2.tag K) ∈ G2.reeFixedTorus K a := Subgroup.one_mem _
  have e : (1 : ModGL G2.tag K) * 1 * N * u = ((t : ModGL G2.tag K) * u' * (t : ModGL G2.tag K)⁻¹) *
      t * N * 1 := by
    calc (1 : ModGL G2.tag K) * 1 * N * u = N * u * N * N := by rw [mul_assoc _ N N, hNN]; group
      _ = (t : ModGL G2.tag K) * u' * N := by rw [h']
      _ = _ := by group
  have := (Corpus.Ree.ReeModel.eq_of_mul_canonicalRep_mul_eq hw₀ h1U htu h1T ht hu h1U e).2.2
  exact Subtype.ext this

include hK hw₀ in
theorem hcover (g : G2.reeGamma K a) : g ∈ borelOf (Ug K a) (Tg K a) (hTU hK) ∨
    ∃ u ∈ Ug K a, ∃ t ∈ Tg K a, ∃ u' ∈ Ug K a, g = u * ng hw₀ * t * u' := by
  rcases Corpus.Ree.ReeModel.reeGamma_G2_cases hw₀ g.2 with ⟨u, hu, h, hh, e⟩ | ⟨-, u, hu, h, hh, v, hv, e⟩
  · left
    have hUΓ := reeFixedPosUnipotent_le (K := K) (a := a)
    have hTΓ := reeFixedTorus_le (K := K) (a := a)
    let hg : G2.reeGamma K a := ⟨h, hTΓ hh⟩
    let ug : G2.reeGamma K a := ⟨u, hUΓ hu⟩
    refine ⟨hg, (mem_Tg).2 hh, hg⁻¹ * ug * hg, ?_, ?_⟩
    · have := hTU hK hg⁻¹ ((Tg K a).inv_mem ((mem_Tg).2 hh)) ug ((mem_Ug).2 hu)
      simpa using this
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg, ug]
      rw [← e]; group
  · right
    have hUΓ := reeFixedPosUnipotent_le (K := K) (a := a)
    have hTΓ := reeFixedTorus_le (K := K) (a := a)
    set N := canonicalRep (coxeterSystem G2.tag) K w₀
    have hNi : N⁻¹ = N := coe_ng_inv hK hw₀
    have hconj : N * h * N⁻¹ = h⁻¹ :=
      Corpus.Ree.ReeModel.canonicalRep_longest_conj_torus hw₀ (Subgroup.mem_inf.1 hh).1
    refine ⟨⟨u, hUΓ hu⟩, (mem_Ug).2 hu, ⟨h⁻¹, hTΓ (inv_mem hh)⟩, (mem_Tg).2 (inv_mem hh),
      ⟨v, hUΓ hv⟩, (mem_Ug).2 hv, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_ng]
    rw [← e, ← hconj]
    calc u * h * N * v = u * N * (N⁻¹ * h * N) * v := by group
      _ = u * N * (N * h * N⁻¹) * v := by rw [hNi]

include hK hw₀ in
theorem ng_not_mem : ng hw₀ ∉ borelOf (Ug K a) (Tg K a) (hTU hK) := by
  intro hn
  obtain ⟨hbij, hcard⟩ := Corpus.Ree.ReeModel.small_Ree_positive_fixed_coordinates a K hK
  have hU1 : ∀ u ∈ Ug K a, u = 1 := fun u hu =>
    hV hK hw₀ u hu (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn
      (le_borelOf_right _ _ (hTU hK) hu)) hn)
  have hbot : Ug K a = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hU1
  have hcardU : Nat.card (Ug K a) = (3 ^ (2 * a + 1)) ^ 3 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe reeFixedPosUnipotent_le).toEquiv
  rw [hbot, Subgroup.card_bot] at hcardU
  have : 1 < (3 ^ (2 * a + 1)) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega)
    (by norm_num))
  omega

include hK hw₀ in
theorem hinvT : ∀ t ∈ Tg K a, ng hw₀ * t * ng hw₀ = t⁻¹ := by
  intro t ht
  rw [mem_Tg] at ht
  apply Subtype.ext
  have h := Corpus.Ree.ReeModel.canonicalRep_longest_conj_torus hw₀ (Subgroup.mem_inf.1 ht).1
  rw [coe_ng_inv hK hw₀] at h
  simpa [coe_ng] using h

include hK in
theorem isCyclic_Tg : IsCyclic (Tg K a) := by
  obtain ⟨⟨φ, -⟩, -⟩ := Corpus.Ree.ReeModel.small_Ree_positive_torus_action a K hK
  let e : Kˣ ≃* Tg K a := φ.trans (Subgroup.subgroupOfEquivOfLe reeFixedTorus_le).symm
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

end

theorem three_pow_mod_four (a : ℕ) : 3 ^ (2 * a + 1) % 4 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

include hK in
theorem neg_one_ne_one : (-1 : K) ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := by linear_combination -h
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  rw [CharP.cast_eq_zero_iff K G2.prime] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by decide)

include hK in
theorem not_isSquare_neg_one : ¬ IsSquare (-1 : K) := by
  have := Fintype.ofFinite K
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK, three_pow_mod_four]
  simp

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley] [h6 : Corpus.Ree.ReeModel]
include h0 h1 h2 h3 h4 h5 h6

include hK in
theorem even_card_Tg : Even (Nat.card (Tg K a)) := by
  obtain ⟨⟨φ, -⟩, -⟩ := Corpus.Ree.ReeModel.small_Ree_positive_torus_action a K hK
  let e : Kˣ ≃* Tg K a := φ.trans (Subgroup.subgroupOfEquivOfLe reeFixedTorus_le).symm
  have hτ : orderOf (e (-1)) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, neg_one_sq, map_one]
    · rw [Ne, ← map_one e, e.injective.eq_iff, ← Units.val_eq_one]
      simpa using neg_one_ne_one hK
  have := orderOf_dvd_natCard (e (-1))
  rw [hτ] at this
  exact (even_iff_two_dvd).2 this

include hK in
theorem odd_card_Ug : Odd (Nat.card (Ug K a)) := by
  obtain ⟨-, hcard⟩ := Corpus.Ree.ReeModel.small_Ree_positive_fixed_coordinates a K hK
  have : Nat.card (Ug K a) = (3 ^ (2 * a + 1)) ^ 3 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe reeFixedPosUnipotent_le).toEquiv
  rw [this]
  exact (Odd.pow (by decide)).pow

end

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley] [h6 : Corpus.Ree.FiniteWeylGroup] [h7 : Corpus.Ree.ReeModel]
include h0 h1 h2 h3 h4 h5 h6 h7

include hK in
/-- **Hall–Paige for the small Ree groups** (corpus model): `Γ = ²G₂(3^{2a+1})` has a complete
mapping. -/
theorem hasCompleteMapping_reeGamma : HasCompleteMapping (G2.reeGamma K a) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : WeylGroup G2.tag => (coxeterSystem G2.tag).length w
  obtain ⟨⟨hu0, hu1, hu2⟩, -, htor, hlong⟩ := Corpus.Ree.ReeModel.ree_G2_prime_field_words K a hw₀
  obtain ⟨⟨φ, hφ⟩, -⟩ := Corpus.Ree.ReeModel.small_Ree_positive_torus_action a K hK
  have hUΓ := reeFixedPosUnipotent_le (K := K) (a := a)
  have hTΓ := reeFixedTorus_le (K := K) (a := a)
  set N := canonicalRep (coxeterSystem G2.tag) K w₀ with hN
  -- the non-square torus element `h(-1)`
  have hh : torusElt G2.tag K ⟨0, by decide⟩ (-1) * torusElt G2.tag K ⟨1, by decide⟩ (-1) =
      (φ (-1) : ModGL G2.tag K) := by
    rw [hφ, smallReeTorusElt, Odd.neg_one_pow (Odd.pow (by decide))]
    rfl
  have hhT : (φ (-1) : ModGL G2.tag K) ∈ G2.reeFixedTorus K a := (φ (-1)).2
  let u₀ : G2.reeGamma K a := ⟨g2U₀ K, hUΓ hu0⟩
  let u₁ : G2.reeGamma K a := ⟨g2U₁ K, hUΓ hu1⟩
  let u₂ : G2.reeGamma K a := ⟨g2U₂ K, hUΓ hu2⟩
  let h : G2.reeGamma K a := ⟨φ (-1), hTΓ hhT⟩
  have hns : ∀ m ∈ Tg K a, h ≠ m * m := by
    intro m hm hhm
    obtain ⟨r, hr⟩ := φ.surjective ⟨m, (mem_Tg).1 hm⟩
    have e1 : φ (-1) = φ (r * r) := by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hr]
      exact congrArg Subtype.val hhm
    have e2 : (-1 : Kˣ) = r * r := φ.injective e1
    apply not_isSquare_neg_one hK
    exact ⟨(r : K), by have := congrArg Units.val e2; simpa using this⟩
  have hA : ng hw₀ = u₁ * (ng hw₀ * u₁ * (ng hw₀)⁻¹) * u₁ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ng, u₁]
    exact hlong
  have hB : h = u₀ * (ng hw₀ * u₀ * (ng hw₀)⁻¹) * (ng hw₀ * u₀ * (ng hw₀)⁻¹) *
      (ng hw₀ * u₁ * (ng hw₀)⁻¹) * u₂ * (ng hw₀ * u₁ * (ng hw₀)⁻¹) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ng, u₀, u₁, u₂, h]
    rw [← hh]
    exact htor
  have hTn := rankOne_tn_mem_of_words (hTU := hTU hK) (ng hw₀) (ng_mul_ng hK hw₀) (hUT hw₀)
    (ng_not_mem hK hw₀) (hV hK hw₀) (hcover hK hw₀) (hinvT hK hw₀) (isCyclic_Tg hK)
    ((mem_Ug (x := u₀)).2 hu0) ((mem_Ug (x := u₁)).2 hu1) ((mem_Ug (x := u₂)).2 hu2)
    ((mem_Tg (x := h)).2 hhT) hns hA hB
  exact hasCompleteMapping_of_rankOne_split (hTU := hTU hK) (ng hw₀) (odd_card_Ug hK)
    (ng_mul_ng hK hw₀) (hUT hw₀) (ng_not_mem hK hw₀) (hV hK hw₀) (hcover hK hw₀) hTn
    (isCyclic_Tg hK) (even_card_Tg hK)

end

end

end CFSGOutside.HallPaige.Ree

namespace CFSGOutside.HallPaige

open TauCeti Corpus.Ree

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.Ree.ReeTag.ReeAut] [h3 : Corpus.Exc.ParameterAddition] [h4 : Corpus.Exc.BorelNormal] [h5 : Corpus.Exc.Chevalley] [h6 : Corpus.Ree.FiniteWeylGroup] [h7 : Corpus.Ree.ReeModel]
include h0 h1 h2 h3 h4 h5 h6 h7

/-- **Hall–Paige for `²G₂(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) :
    CatalogueCase (.lie ⟨.reeG2 m, hv⟩) := by
  intro _ _
  have hm : 1 ≤ m := ((LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1)
  obtain ⟨e⟩ := Corpus.Ree.ReeModel.nonempty_reeGamma_equiv m hm hv
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  exact HasCompleteMapping.of_mulEquiv e (Ree.hasCompleteMapping_reeGamma hK)

end

end CFSGOutside.HallPaige
