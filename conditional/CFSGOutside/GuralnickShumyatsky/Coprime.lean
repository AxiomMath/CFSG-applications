import CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime
import CFSGOutside.GuralnickShumyatsky.Defs

/-!
# Coprime action and Sylow lemmas (Guralnick–Shumyatsky, Lemma 2.1)
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

variable {X : Type} [Group X]

theorem isSylowOf_eq_of_le {p : ℕ} {P K : Subgroup X}
    (h : IsSylowOf p P K) {Q : Subgroup X} (hPQ : P ≤ Q) (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    Q = P := by
  obtain ⟨Q0, rfl⟩ := h
  have h1 : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  have h2 : (Q0 : Subgroup K) ≤ Q.subgroupOf K := map_le_iff_le_comap.mp hPQ
  have h3 : Q.subgroupOf K = Q0 := Q0.is_maximal' h1 h2
  calc Q = (Q.subgroupOf K).map K.subtype := (map_subgroupOf_eq_of_le hQK).symm
    _ = _ := by rw [h3]

theorem isSylowOf_map [Finite X] {Z : Type} [Group Z] {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (h : IsSylowOf p P K) (f : X →* Z) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  rw [Subgroup.map_map]
  rfl

/-- Guralnick–Shumyatsky, Lemma 2.1(4). -/
theorem isSylowOf_inf_centralizer [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}] [Finite X] {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime)
    {A K R : Subgroup X} (hA : IsPGroup q A) (hAK : A ≤ normalizer (K : Set X))
    (hK : ¬ q ∣ Nat.card K) (hR : IsSylowOf p R K) (hAR : A ≤ normalizer (R : Set X)) :
    IsSylowOf p (R ⊓ centralizer (A : Set X)) (K ⊓ centralizer (A : Set X)) := by
  have hRK := hR.le
  have hRp := hR.isPGroup
  set C := K ⊓ centralizer (A : Set X) with hC
  set S := R ⊓ centralizer (A : Set X) with hS
  have hSC : S ≤ C := inf_le_inf_right _ hRK
  have hSp : IsPGroup p S := hRp.to_le inf_le_left
  obtain ⟨Q0, hQ0⟩ := (hSp.comap_subtype (K := C)).exists_le_sylow
  set Q : Subgroup X := (Q0 : Subgroup C).map C.subtype with hQdef
  have hQ : IsSylowOf p Q C := ⟨Q0, rfl⟩
  have hQC : Q ≤ C := hQ.le
  have hQp : IsPGroup p Q := hQ.isPGroup
  have hSQ : S ≤ Q := by
    intro s hs
    have : (⟨s, hSC hs⟩ : C) ∈ (Q0 : Subgroup C) := hQ0 (mem_subgroupOf.2 hs)
    exact ⟨_, this, rfl⟩
  have hcomm : ∀ g ∈ A, ∀ t ∈ Q, g * t = t * g := fun g hg t ht =>
    mem_centralizer_iff.1 (hQC ht).2 g hg
  have hAQ : A ≤ normalizer (Q : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro t
    have key : g * t * g⁻¹ = t → (t ∈ Q ↔ g * t * g⁻¹ ∈ Q) := fun e => by rw [e]
    constructor
    · intro ht
      have e : g * t * g⁻¹ = t := mul_inv_eq_iff_eq_mul.2 (hcomm g hg t ht)
      rw [e]; exact ht
    · intro ht
      have h2 := hcomm g hg _ ht
      have h3 : g * t = g * (g * t * g⁻¹) := by
        calc g * t = (g * t * g⁻¹) * g := by group
          _ = g * (g * t * g⁻¹) := h2.symm
      have e : g * t * g⁻¹ = t := (mul_left_cancel h3).symm
      rw [e] at ht; exact ht
  obtain ⟨R', hR', hQR', hAR'⟩ :=
    CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.exists_isSylowOf_normalized_ge_of_coprime
      (p := q) (r := p) hq Fact.out hA hAK hK (hQC.trans inf_le_left) hQp hAQ
  obtain ⟨c, hc, hconj⟩ :=
    CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.exists_conj_eq_of_isSylowOf_normalized_of_coprime
      (p := q) (r := p) hq Fact.out hA hAK hK hR hR' hAR hAR'
  have hmem : ∀ t ∈ Q, c⁻¹ * t * c ∈ S := by
    intro t ht
    have ht' : t ∈ R.map (MulAut.conj c).toMonoidHom := hconj ▸ hQR' ht
    obtain ⟨r, hrR, hr⟩ := ht'
    have hr' : c⁻¹ * t * c = r := by
      rw [← hr]
      show c⁻¹ * (c * r * c⁻¹) * c = r
      group
    rw [hr']
    refine ⟨hrR, mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgc : Commute g c := mem_centralizer_iff.1 hc.2 g hg
    have hgt : Commute g t := hcomm g hg t ht
    have : Commute g r := by
      rw [← hr']; exact ((hgc.inv_right).mul_right hgt).mul_right hgc
    exact this.eq
  let φ : Q → S := fun t => ⟨c⁻¹ * t.1 * c, hmem t.1 t.2⟩
  have hφ : Function.Injective φ := by
    intro t t' h
    have h' : c⁻¹ * t.1 * c = c⁻¹ * t'.1 * c := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hcard : Nat.card Q ≤ Nat.card S := Nat.card_le_card_of_injective φ hφ
  have hSQeq : S = Q := eq_of_le_of_card_ge hSQ hcard
  rw [hSQeq]; exact hQ

theorem map_inf_eq_of_isSylowOf [Finite X] {Z : Type} [Group Z] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (hP : IsPGroup p P) (hPK : IsSylowOf p (P ⊓ K) K) (f : X →* Z) :
    P.map f ⊓ K.map f = (P ⊓ K).map f := by
  refine le_antisymm ?_ (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
  exact isSylowOf_eq_of_le (isSylowOf_map hPK f) (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
    inf_le_right ((hP.map f).to_le inf_le_left) |>.le

/-- A `q`-element acting on a coset of a normal `q'`-subgroup has a fixed point. -/
theorem exists_mul_comm_of_coset [Finite X] {Z : Type*} [Group Z] {q : ℕ} (hq : q.Prime)
    (f : X →* Z) {a x : X} (ha : a ^ q = 1) (hk : ¬ q ∣ Nat.card f.ker)
    (hx : f x * f a = f a * f x) : ∃ n ∈ f.ker, (x * n) * a = a * (x * n) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hfg : ∀ g ∈ zpowers a, f g * f x = f x * f g := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    rw [map_zpow]
    exact ((Commute.zpow_right (show Commute (f x) (f a) from hx) k).eq).symm
  let T := {y : X // f y = f x}
  have hmem : ∀ (g : zpowers a) (y : T), f (g.1 * y.1 * g.1⁻¹) = f x := by
    intro g y
    rw [map_mul, map_mul, map_inv, y.2, hfg g.1 g.2, mul_assoc, mul_inv_cancel, mul_one]
  letI : SMul (zpowers a) T := ⟨fun g y => ⟨g.1 * y.1 * g.1⁻¹, hmem g y⟩⟩
  have hsmul : ∀ (g : zpowers a) (y : T), (g • y).1 = g.1 * y.1 * g.1⁻¹ := fun g y => rfl
  letI : MulAction (zpowers a) T :=
    { one_smul := fun y => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun g h y => Subtype.ext (by
        rw [hsmul, hsmul, hsmul]; simp [mul_assoc]) }
  have hZ : IsPGroup q (zpowers a) := by
    rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one ha) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hT : Nat.card T = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, by simp [MonoidHom.mem_ker, y.2]⟩
        invFun := fun n => ⟨x * n.1, by simp [MonoidHom.mem_ker.1 n.2]⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hmod := hZ.card_modEq_card_fixedPoints (α := T)
  have hpos : Nat.card (MulAction.fixedPoints (zpowers a) T) ≠ 0 := by
    intro h0
    rw [h0, hT] at hmod
    exact hk ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨y, hy⟩⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hpos) |>.1
  have hya : (⟨a, mem_zpowers a⟩ : zpowers a) • y = y := hy ⟨a, mem_zpowers a⟩
  have hya' : a * y.1 * a⁻¹ = y.1 := congrArg Subtype.val hya
  refine ⟨x⁻¹ * y.1, by simp [MonoidHom.mem_ker, y.2], ?_⟩
  rw [mul_inv_cancel_left]
  exact (mul_inv_eq_iff_eq_mul.1 hya').symm

/-- Guralnick–Shumyatsky, Lemma 2.1(1) for one element: `C_{G/N}(a) = C_G(a)N/N`. -/
theorem map_cen [Finite X] {Z : Type*} [Group Z] {q : ℕ} (hq : q.Prime) (f : X →* Z)
    {G : Subgroup X} (hkG : f.ker ≤ G) (hG : ¬ q ∣ Nat.card G) {a : X} (ha : a ^ q = 1) :
    (cen G a).map f = cen (G.map f) (f a) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxG, hxc⟩, rfl⟩
    refine ⟨⟨x, hxG, rfl⟩, mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul,
      mem_centralizer_iff.1 hxc a rfl]
  · rintro ⟨⟨x, hxG, rfl⟩, hz⟩
    have hx : f x * f a = f a * f x := (mem_centralizer_iff.1 hz (f a) rfl).symm
    have hk : ¬ q ∣ Nat.card f.ker := fun h => hG (h.trans (card_dvd_of_le hkG))
    obtain ⟨n, hn, hnc⟩ := exists_mul_comm_of_coset hq f ha hk hx
    refine ⟨x * n, ⟨mul_mem hxG (hkG hn), mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
    · rw [Set.mem_singleton_iff.1 hh]; exact hnc.symm
    · rw [map_mul, MonoidHom.mem_ker.1 hn, mul_one]

end CFSGOutside.GuralnickShumyatsky
