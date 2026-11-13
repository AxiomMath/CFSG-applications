import CFSGOutside.ChillagSonn.Lemma18
import CFSGOutside.ChillagSonn.CyclicSylow
import CFSGOutside.ChillagSonn.Lemma12

/-!
# Theorem 1 of Chillag–Sonn, Case 1: `G/S(G)` simple

If `G` is a nonsolvable Sylow-metacyclic group with `G/S(G)` simple, then `G = O(G) A` with `O(G) ∩ A = 1`, where `A`
is a perfect central extension of `G/S(G)` by a group of order at most 2, hence in the list `M₁₁, A₇, Ã₇, PSL(2, q),
SL(2, q)`. We take `A` of minimal order with `G = S(G) A` and `|S(G) ∩ A| ≤ 2` (Lemma (1.8)); it is perfect, and
Lemma (1.2)(a), applied inside a Sylow 2-subgroup of `G`, shows that a Sylow 2-subgroup of `S(G)` lies in `S(G) ∩ A`.
Then `S(G)` has a normal 2-complement, which is `O(G)`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter CFSGOutside.Corpus.GroupTheory Subgroup
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

/-- A nonabelian simple group is perfect. -/
theorem commutator_eq_top_of_simple {X : Type*} [Group X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    commutator X = ⊤ := by
  refine (inferInstance : (commutator X).Normal).eq_bot_or_eq_top.resolve_left fun h => ?_
  obtain ⟨a, b, hab⟩ := hnab
  have : ⁅a, b⁆ ∈ commutator X := commutator_mem_commutator (mem_top a) (mem_top b)
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact hab this

omit [Finite G] in
/-- If `S ⊔ A = ⊤` with `S` normal, then `A → G/S` is onto. -/
theorem surjective_mk_comp_subtype {S A : Subgroup G} [S.Normal] (h : S ⊔ A = ⊤) :
    Function.Surjective ((QuotientGroup.mk' S).comp A.subtype) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S y
  obtain ⟨s, hs, a, ha, rfl⟩ := mem_sup_of_normal_left.mp (h ▸ mem_top g)
  refine ⟨⟨a, ha⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  simpa [mul_assoc] using (inferInstance : S.Normal).conj_mem s hs a⁻¹

omit [Finite G] in
/-- If `S ⊔ A = ⊤` with `S` normal, then `A` maps onto `G/S`. -/
theorem map_mk_eq_top {S A : Subgroup G} [S.Normal] (h : S ⊔ A = ⊤) : A.map (QuotientGroup.mk' S) = ⊤ := by
  rw [← range_subtype A, MonoidHom.map_range, MonoidHom.range_eq_top]
  exact surjective_mk_comp_subtype h

/-- A subgroup of odd order meets a subgroup of order at most 2 trivially. -/
theorem inf_eq_bot_of_odd {H L : Subgroup G} (hH : Odd (Nat.card H)) (hL : Nat.card L ≤ 2) : H ⊓ L = ⊥ := by
  have hle := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (inf_le_right : H ⊓ L ≤ L))
  have hodd := Odd.of_dvd_nat hH (card_dvd_of_le (inf_le_left : H ⊓ L ≤ H))
  have hpos : 0 < Nat.card (H ⊓ L : Subgroup G) := Nat.card_pos
  refine eq_bot_of_card_eq _ ?_
  have : Nat.card (H ⊓ L : Subgroup G) ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  omega

omit [Finite G] in
/-- A characteristic subgroup of a normal subgroup is normal. -/
theorem normal_map_subtype_of_characteristic {S : Subgroup G} [S.Normal] (K : Subgroup S) [hK : K.Characteristic] :
    (K.map S.subtype).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ g
  refine ⟨MulAut.conjNormal g k, ?_, by simp [MulAut.conjNormal_apply]⟩
  rw [← characteristic_iff_map_eq.1 hK (MulAut.conjNormal g)]
  exact mem_map_of_mem _ hk

/-- If `P` is a Sylow `p`-subgroup of `G` and `N ⊴ G`, then `P ∩ N` is a Sylow `p`-subgroup of `N`. -/
theorem exists_sylow_map_eq_inf {p : ℕ} [Fact p.Prime] (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ Q : Sylow p N, (Q : Subgroup N).map N.subtype = (P : Subgroup G) ⊓ N := by
  have h1 := relIndex_mul_card (P : Subgroup G) N
  have h2 := relIndex_mul_card (P : Subgroup G) ((P : Subgroup G) ⊔ N)
  have h3 := relIndex_mul_card N (P : Subgroup G)
  have h4 := relIndex_mul_card N ((P : Subgroup G) ⊔ N)
  rw [inf_of_le_left (le_sup_left : (P : Subgroup G) ≤ (P : Subgroup G) ⊔ N)] at h2
  rw [inf_of_le_left (le_sup_right : N ≤ (P : Subgroup G) ⊔ N), relIndex_sup_right] at h4
  rw [inf_comm] at h3
  have hc : 0 < N.relIndex P * Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) := by rw [h3]; exact Nat.card_pos
  have hr : (P : Subgroup G).relIndex N = (P : Subgroup G).relIndex ((P : Subgroup G) ⊔ N) := by
    refine Nat.eq_of_mul_eq_mul_right hc ?_
    calc (P : Subgroup G).relIndex N * (N.relIndex P * Nat.card ((P : Subgroup G) ⊓ N : Subgroup G))
        = N.relIndex P * Nat.card N := by rw [← h1]; ring
      _ = (P : Subgroup G).relIndex ((P : Subgroup G) ⊔ N) * (N.relIndex P * Nat.card ((P : Subgroup G) ⊓ N : Subgroup G)) := by
        rw [h4, h3, h2]
  have hnd : ¬ p ∣ ((P : Subgroup G).subgroupOf N).index := by
    show ¬ p ∣ (P : Subgroup G).relIndex N
    rw [hr]
    exact fun h => P.not_dvd_index (h.trans (relIndex_dvd_index_of_le le_sup_left))
  exact ⟨IsPGroup.toSylow (P := (P : Subgroup G).subgroupOf N)
    (P.2.comap_of_injective N.subtype N.subtype_injective) hnd, subgroupOf_map_subtype _ _⟩

/-- Lemma (1.2)(a) inside `N ⊔ B`: if `B` normalizes `N`, `N ∩ B = 1`, `N ⊔ B` is a metacyclic `p`-group and `B` is
not cyclic, then `N = 1`. -/
theorem eq_bot_of_not_isCyclic [FrattiniElementaryQuotient.{0}] {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {N B : Subgroup H} (hp : IsPGroup p (N ⊔ B : Subgroup H))
    (hM : IsMetacyclic (N ⊔ B : Subgroup H)) (hB : B ≤ normalizer (N : Set H)) (hinf : N ⊓ B = ⊥)
    (hc : ¬ IsCyclic B) : N = ⊥ := by
  by_contra hN
  have : (N.subgroupOf (N ⊔ B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hB)
  have h := lemma_1_2_a hp hM (N.subgroupOf (N ⊔ B)) (B.subgroupOf (N ⊔ B))
    (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
    (by
      rw [eq_bot_iff]
      rintro x ⟨h1, h2⟩
      have : (x : H) ∈ N ⊓ B := mem_inf.2 ⟨h1, h2⟩
      rw [hinf, mem_bot] at this
      exact mem_bot.2 (Subtype.ext this))
    (fun h => hN (disjoint_self.1 ((subgroupOf_eq_bot.1 h).mono_right le_sup_left)))
  have := h
  exact hc (isCyclic_of_surjective (subgroupOfEquivOfLe (le_sup_right : B ≤ N ⊔ B)).toMonoidHom
    (MulEquiv.surjective _))

end Helpers

section Sylow

variable {G : Type} [Group G] [Finite G]

/-- The Sylow 2-argument of Case 1. Let `D = S ∩ A` be central in `A` of order at most 2, `D ≤ B ≤ A ∩ G₂` with
`G₂` a Sylow 2-subgroup, `G₂ = (G₂ ∩ S) B`, and the image of `B` in `G/S` not cyclic. Then `D` centralizes `G₂ ∩ S`
(else Lemma (1.2)(a) applies to `Z(G₂ ∩ S) ⋊ B`), and Lemma (1.2)(a) in `G₂/D` gives `G₂ ∩ S ≤ D`. -/
theorem inf_le_of_sylow [FrattiniElementaryQuotient.{0}] (hG : SylowMetacyclic G) {S A B : Subgroup G} [S.Normal]
    (G₂ : Sylow 2 G) (hcard : Nat.card (S ⊓ A : Subgroup G) ≤ 2)
    (hcent : A ≤ centralizer ((S ⊓ A : Subgroup G) : Set G)) (hBA : B ≤ A) (hBG : B ≤ G₂) (hDB : S ⊓ A ≤ B)
    (hG₂ : (G₂ : Subgroup G) ≤ (G₂ : Subgroup G) ⊓ S ⊔ B) (hc : ¬ IsCyclic (B.map (QuotientGroup.mk' S))) :
    (G₂ : Subgroup G) ⊓ S ≤ S ⊓ A := by
  set P : Subgroup G := (G₂ : Subgroup G) with hP
  set D : Subgroup G := S ⊓ A with hD
  set S₂ : Subgroup G := P ⊓ S with hS₂
  have hDP : D ≤ P := hDB.trans hBG
  have hDS₂ : D ≤ S₂ := le_inf hDP inf_le_left
  have hinfB : S₂ ⊓ B ≤ D := fun x hx => mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).2, hBA (mem_inf.1 hx).2⟩
  have hcB : ¬ IsCyclic B := fun h => hc (by
    have := h; exact isCyclic_of_surjective _ ((QuotientGroup.mk' S).subgroupMap_surjective B))
  -- `D` centralizes `S₂`
  have hZ : D ≤ centralizer (S₂ : Set G) := by
    by_contra hDZ
    set Z : Subgroup G := S₂ ⊓ centralizer (S₂ : Set G) with hZdef
    have hconj : ∀ g ∈ P, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
      intro g hg z hz
      obtain ⟨hzS₂, hz⟩ := mem_inf.1 hz
      obtain ⟨hzP, hzS⟩ := mem_inf.1 hzS₂
      refine mem_inf.2 ⟨mem_inf.2 ⟨P.mul_mem (P.mul_mem hg hzP) (P.inv_mem hg),
        ‹S.Normal›.conj_mem z hzS g⟩, mem_centralizer_iff.2 fun s hs => ?_⟩
      obtain ⟨hsP, hsS⟩ := mem_inf.1 hs
      have hs' : g⁻¹ * s * g ∈ S₂ := mem_inf.2 ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hsP) hg,
        by simpa using ‹S.Normal›.conj_mem s hsS g⁻¹⟩
      have key := mem_centralizer_iff.1 hz _ hs'
      calc s * (g * z * g⁻¹) = g * (g⁻¹ * s * g * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
        _ = g * z * g⁻¹ * s := by group
    have hPZ : P ≤ normalizer (Z : Set G) := fun g hg => mem_normalizer_iff.2 fun h =>
      ⟨hconj g hg h, fun h' => by simpa [mul_assoc] using hconj g⁻¹ (P.inv_mem hg) _ h'⟩
    have hZB : Z ⊓ B = ⊥ := by
      by_contra hne
      have hle : Z ⊓ B ≤ D := (inf_le_inf_right B inf_le_left).trans hinfB
      have h2 : 1 < Nat.card (Z ⊓ B : Subgroup G) := (one_lt_card_iff_ne_bot _).2 hne
      have heq : Z ⊓ B = D := eq_of_le_of_card_ge hle (by omega)
      exact hDZ (heq ▸ inf_le_left.trans inf_le_right)
    have hZp : IsPGroup 2 (Z ⊔ B : Subgroup G) := G₂.2.to_le (sup_le (inf_le_left.trans inf_le_left) hBG)
    have hZbot := eq_bot_of_not_isCyclic hZp (hG.isMetacyclic_of_isPGroup _ hZp) (hBG.trans hPZ) hZB hcB
    have : Nontrivial S₂ := by
      rw [nontrivial_iff_ne_bot]
      intro h
      exact hDZ ((le_bot_iff.1 (h ▸ hDS₂)) ▸ bot_le)
    have := (G₂.2.to_le (inf_le_left : S₂ ≤ P)).center_nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : center S₂)
    have hxZ : ((x : S₂) : G) ∈ Z := mem_inf.2 ⟨(x : S₂).2, mem_centralizer_iff.2 fun s hs =>
      congrArg Subtype.val (mem_center_iff.1 x.2 ⟨s, hs⟩)⟩
    rw [hZbot, mem_bot] at hxZ
    exact hx (Subtype.ext (Subtype.ext hxZ))
  -- hence `D` is central in `G₂`
  have hPc : P ≤ centralizer (D : Set G) := hG₂.trans (sup_le (le_centralizer_iff.1 hZ) (hBA.trans hcent))
  have : (D.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDP).2 (hPc.trans (centralizer_le_normalizer _))
  -- Lemma (1.2)(a) in `G₂ / D`
  have hker : D.subgroupOf P ≤ ((QuotientGroup.mk' S).comp P.subtype).ker := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_inf.1 (mem_subgroupOf.1 hx)).1
  let μ := QuotientGroup.mk' (D.subgroupOf P)
  let ψ := QuotientGroup.lift (D.subgroupOf P) ((QuotientGroup.mk' S).comp P.subtype) hker
  have hψ : ((B.subgroupOf P).map μ).map ψ = B.map (QuotientGroup.mk' S) := by
    rw [map_map, show ψ.comp μ = (QuotientGroup.mk' S).comp P.subtype from MonoidHom.ext fun _ => rfl,
      ← map_map, subgroupOf_map_subtype, inf_of_le_left hBG]
  have : ((S.subgroupOf P).map μ).Normal := Normal.map inferInstance μ (QuotientGroup.mk'_surjective _)
  have hP₁ : (S.subgroupOf P).map μ = ⊥ := by
    refine eq_bot_of_not_isCyclic (B := (B.subgroupOf P).map μ) ((G₂.2.to_quotient _).to_subgroup _)
      (((hG 2 G₂).of_surjective μ (QuotientGroup.mk'_surjective _)).subgroup _)
      (le_top.trans_eq (normalizer_eq_top _).symm) ?_ ?_
    · rw [eq_bot_iff]
      intro z hz
      obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩ := mem_inf.1 hz
      rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have hA := A.mul_mem (hBA (mem_subgroupOf.1 hy)) (mem_inf.1 (mem_subgroupOf.1 hyx)).2
      exact mem_inf.2 ⟨mem_subgroupOf.1 hx, by simpa using hA⟩
    · intro h
      have := h
      apply hc
      rw [← hψ]
      exact isCyclic_of_surjective _ (ψ.subgroupMap_surjective _)
  intro x hx
  have hmem : μ ⟨x, (mem_inf.1 hx).1⟩ ∈ (S.subgroupOf P).map μ :=
    mem_map_of_mem _ (mem_subgroupOf.2 (mem_inf.1 hx).2)
  rw [hP₁, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
  exact hmem

/-- Case 1 from a supplement: if `G = S A` with `S ⊴ G`, `O(G) ≤ S`, `D = S ∩ A` central in `A` of order at most 2
and the Sylow 2-subgroups of `G/S` not cyclic, then `G = O(G) A` and `O(G) ∩ A = 1`. -/
theorem split_of_supplement [FrattiniElementaryQuotient.{0}] [FrobeniusNormalPComplement.{0}]
    (hG : SylowMetacyclic G) {S A : Subgroup G} [S.Normal] (hOS : oddCore G ≤ S) (hsup : S ⊔ A = ⊤)
    (hcard : Nat.card (S ⊓ A : Subgroup G) ≤ 2) (hcent : A ≤ centralizer ((S ⊓ A : Subgroup G) : Set G))
    (hc : ∀ P : Sylow 2 (G ⧸ S), ¬ IsCyclic P) : oddCore G ⊓ A = ⊥ ∧ oddCore G ⊔ A = ⊤ := by
  have hsurj := surjective_mk_comp_subtype hsup
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = ((default : Sylow 2 A) : Subgroup A).map A.subtype := ⟨_, rfl⟩
  have hBA : B ≤ A := hB ▸ map_subtype_le _
  have hBp : IsPGroup 2 B := hB ▸ (default : Sylow 2 A).2.map A.subtype
  obtain ⟨G₂, hBG⟩ := hBp.exists_le_sylow
  have hDcard : Nat.card (S.subgroupOf A) = Nat.card (S ⊓ A : Subgroup G) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective A.subtype_injective]
  have hDp : IsPGroup 2 (S.subgroupOf A) := by
    have : 0 < Nat.card (S.subgroupOf A) := Nat.card_pos
    rcases (show Nat.card (S.subgroupOf A) = 2 ^ 0 ∨ Nat.card (S.subgroupOf A) = 2 ^ 1 by omega) with h | h <;>
      exact IsPGroup.of_card h
  have hDB : S ⊓ A ≤ B := by
    rw [hB, ← subgroupOf_map_subtype]; exact map_mono (hDp.le_sylow_of_normal _)
  have hPX : (((default : Sylow 2 A).mapSurjective hsurj : Sylow 2 (G ⧸ S)) : Subgroup (G ⧸ S)) =
      B.map (QuotientGroup.mk' S) := by
    rw [Sylow.coe_mapSurjective, hB, map_map]
  have hπ : B.map (QuotientGroup.mk' S) = (G₂ : Subgroup G).map (QuotientGroup.mk' S) := by
    refine eq_of_le_of_card_ge (map_mono hBG) ?_
    have h1 : Nat.card (B.map (QuotientGroup.mk' S)) = 2 ^ (Nat.card (G ⧸ S)).factorization 2 := by
      rw [← hPX]; exact Sylow.card_eq_multiplicity _
    have h2 : Nat.card ((G₂ : Subgroup G).map (QuotientGroup.mk' S)) =
        2 ^ (Nat.card (G ⧸ S)).factorization 2 :=
      Sylow.card_eq_multiplicity (G₂.mapSurjective (QuotientGroup.mk'_surjective S))
    rw [h1, h2]
  have hG₂ : (G₂ : Subgroup G) ≤ (G₂ : Subgroup G) ⊓ S ⊔ B := by
    intro g hg
    have hmem : QuotientGroup.mk' S g ∈ B.map (QuotientGroup.mk' S) := by
      rw [hπ]; exact mem_map_of_mem _ hg
    obtain ⟨b, hb, hbg⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hbg
    rw [show g = b * (b⁻¹ * g) by group]
    exact mul_mem (mem_sup_right hb) (mem_sup_left (mem_inf.2 ⟨mul_mem (inv_mem (hBG hb)) hg, hbg⟩))
  have hcB : ¬ IsCyclic (B.map (QuotientGroup.mk' S)) := by rw [← hPX]; exact hc _
  have hS₂ := inf_le_of_sylow hG G₂ hcard hcent hBA hBG hDB hG₂ hcB
  -- a Sylow 2-subgroup of `S` lies in `S ∩ A`, so `S` has a normal 2-complement `K ≤ O(G)`
  obtain ⟨Q, hQ⟩ := exists_sylow_map_eq_inf G₂ S
  have hQ2 : ∀ P : Sylow 2 S, Nat.card P ≤ 2 := by
    intro P
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity Q]
    calc Nat.card Q = Nat.card ((Q : Subgroup S).map S.subtype) :=
          (card_map_of_injective S.subtype_injective).symm
      _ ≤ Nat.card (S ⊓ A : Subgroup G) := card_le_of_le (by rw [hQ]; exact hS₂)
      _ ≤ 2 := hcard
  obtain ⟨K, hKn, hKcop, k, hk⟩ := exists_normalTwoComplement_of_card_le_two hQ2
  have := (FrobeniusNormalPComplement.frobenius_normal_p_complement (G := S) 2).2.2 K ⟨hKn, hKcop, k, hk⟩
  have hKodd : Odd (Nat.card (K.map S.subtype)) := by
    rw [card_map_of_injective S.subtype_injective]; exact Nat.coprime_two_right.mp hKcop
  have hKO : K.map S.subtype ≤ oddCore G := le_oddCore (normal_map_subtype_of_characteristic K) hKodd
  have hKQ : K ⊔ (Q : Subgroup S) = ⊤ := by
    rw [← index_eq_one]
    have h1 : (K ⊔ (Q : Subgroup S)).index ∣ 2 ^ k := by rw [← hk]; exact index_dvd_of_le le_sup_left
    have h2 : (K ⊔ (Q : Subgroup S)).index ∣ (Q : Subgroup S).index := index_dvd_of_le le_sup_right
    have hcop : Nat.Coprime (2 ^ k) (Q : Subgroup S).index :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 Q.not_dvd_index)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have hSle : S ≤ K.map S.subtype ⊔ ((G₂ : Subgroup G) ⊓ S) := by
    rw [← hQ, ← Subgroup.map_sup, hKQ, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨eq_bot_iff.2 ((le_inf inf_le_left (inf_le_inf_right A hOS)).trans
    (inf_eq_bot_of_odd odd_card_oddCore hcard).le), ?_⟩
  rw [eq_top_iff, ← hsup]
  exact sup_le (hSle.trans (sup_le (hKO.trans le_sup_left) (hS₂.trans (inf_le_right.trans le_sup_right))))
    le_sup_right

end Sylow

section Main

variable {G : Type} [Group G] [Finite G]

/-- Steps 1–2: a supplement `A` of `S(G)` with `|S(G) ∩ A| ≤ 2` of minimal order is perfect. -/
theorem exists_perfect_supplement [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
    [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
    [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hsimp : IsSimpleGroup (G ⧸ solvableRadical G)) (hnab : ∃ a b : G ⧸ solvableRadical G, a * b ≠ b * a) :
    ∃ A : Subgroup G, solvableRadical G ⊔ A = ⊤ ∧ Nat.card (solvableRadical G ⊓ A : Subgroup G) ≤ 2 ∧
      commutator A = ⊤ := by
  classical
  have := hsimp
  have hex : ∃ n, ∃ A : Subgroup G, solvableRadical G ⊔ A = ⊤ ∧
      Nat.card (solvableRadical G ⊓ A : Subgroup G) ≤ 2 ∧ Nat.card A = n := by
    obtain ⟨A, h1, h2⟩ := lemma_1_8 hG hns hsimp
    exact ⟨_, A, h1, h2, rfl⟩
  obtain ⟨A, hA1, hA2, hAn⟩ := Nat.find_spec hex
  refine ⟨A, hA1, hA2, ?_⟩
  have hle : ⁅A, A⁆ ≤ A := commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hmap : (⁅A, A⁆).map (QuotientGroup.mk' (solvableRadical G)) = ⊤ := by
    rw [map_commutator, map_mk_eq_top hA1, ← commutator_def, commutator_eq_top_of_simple hnab]
  have h1 : solvableRadical G ⊔ ⁅A, A⁆ = ⊤ := sup_eq_top_of_map_eq_top hmap
  have h2 : Nat.card (solvableRadical G ⊓ ⁅A, A⁆ : Subgroup G) ≤ 2 :=
    (card_le_of_le (inf_le_inf_left _ hle)).trans hA2
  have heq : ⁅A, A⁆ = A := eq_of_le_of_card_ge hle (by rw [hAn]; exact Nat.find_min' hex ⟨_, h1, h2, rfl⟩)
  apply map_injective A.subtype_injective
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, heq]

/-- **Case 1 of Theorem 1.** -/
theorem case1_split [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
    [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
    [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
    {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hsimp : IsSimpleGroup (G ⧸ solvableRadical G)) :
    ∃ A : Subgroup G, oddCore G ⊓ A = ⊥ ∧ oddCore G ⊔ A = ⊤ ∧ PerfectList A ∧ IsQuasisimple A ∧
      Nat.card (Subgroup.center A) ≤ 2 ∧ Nonempty (A ⧸ Subgroup.center A ≃* G ⧸ solvableRadical G) := by
  have := hsimp
  have hnab : ∃ a b : G ⧸ solvableRadical G, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : Group.IsSolvable (G ⧸ solvableRadical G) := Group.isSolvable_of_comm h
    have : Group.IsSolvable (solvableRadical G) := isSolvable_solvableRadical
    exact hns (Group.isSolvable_of_subgroup_quotient (solvableRadical G))
  obtain ⟨A, hsup, hcard, hperf⟩ := exists_perfect_supplement hG hns hsimp hnab
  -- Step 3: `A` is a stem extension of `G/S(G)`
  have hDcard : Nat.card ((solvableRadical G).subgroupOf A) = Nat.card (solvableRadical G ⊓ A : Subgroup G) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective A.subtype_injective]
  have hDc := le_center_of_card_le_two ((solvableRadical G).subgroupOf A) (hDcard ▸ hcard)
  obtain ⟨e⟩ := nonempty_quotient_subgroupOf_equiv hsup
  have hZ := center_eq_of_simple_quotient _ hDc e hnab
  -- Step 4: the splitting
  have hOS : oddCore G ≤ solvableRadical G := le_solvableRadical inferInstance
    (isSolvable_of_odd_of_sylowMetacyclic (hG.subgroup _) odd_card_oddCore)
  have hcent : A ≤ centralizer ((solvableRadical G ⊓ A : Subgroup G) : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun x hx => (congrArg Subtype.val (mem_center_iff.1
      (hDc (mem_subgroupOf.2 (mem_inf.1 hx).1 : (⟨x, (mem_inf.1 hx).2⟩ : A) ∈ _)) ⟨a, ha⟩)).symm
  have hc : ∀ P : Sylow 2 (G ⧸ solvableRadical G), ¬ IsCyclic P := by
    intro P hP
    obtain ⟨m, hm⟩ := odd_card_of_perfect_of_cyclic (commutator_eq_top_of_simple hnab) P hP
    obtain ⟨E, -, -, hE⟩ := exists_elem4 (G ⧸ solvableRadical G) hnab
    obtain ⟨j, hj⟩ := hE ▸ card_subgroup_dvd_card E
    omega
  obtain ⟨hinf, hsup'⟩ := split_of_supplement hG hOS hsup hcard hcent hc
  exact ⟨A, hinf, hsup', perfectList_of_stem hperf _ hDc (hDcard ▸ hcard) e hnab (lemma_1_5 hnab (hG.quotient _)),
    isQuasisimple_of_central hperf _ hDc e hnab, by rw [hZ, hDcard]; exact hcard,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans e⟩⟩

end Main

end CFSGOutside.ChillagSonn
