import CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime
import CFSGOutside.GuralnickShumyatsky.Gen
import CFSGOutside.GuralnickShumyatsky.Transport

/-!
# Helpers for the induction: monotonicity, invariant subgroups and the quotient step
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

variable {X : Type} [Group X]

theorem gens_le (P G A : Subgroup X) : gens P G A ≤ P :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem gens_mono {P P' G G' : Subgroup X} (A : Subgroup X) (hP : P ≤ P') (hG : G ≤ G') :
    gens P G A ≤ gens P' G' A :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf hP (commutator_mono (inf_le_inf_right _ hG) (inf_le_inf_right _ hG))

theorem commutator_self_le (H : Subgroup X) : ⁅H, H⁆ ≤ H := by
  refine commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem le_normalizer_of_normal' (H : Subgroup X) [H.Normal] (K : Subgroup X) :
    K ≤ normalizer (H : Set X) := by
  rw [normalizer_eq_top_iff.mpr inferInstance]; exact le_top

theorem le_normalizer_inf' {A H K : Subgroup X} (hH : A ≤ normalizer (H : Set X))
    (hK : A ≤ normalizer (K : Set X)) : A ≤ normalizer ((H ⊓ K : Subgroup X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at *
  rw [map_inf_eq _ _ _ (MulAut.conj g).injective, mem_normalizer_iff_map_conj_eq.1 (hH hg),
    mem_normalizer_iff_map_conj_eq.1 (hK hg)]

theorem le_normalizer_commutator' {A H K : Subgroup X} (hH : A ≤ normalizer (H : Set X))
    (hK : A ≤ normalizer (K : Set X)) : A ≤ normalizer ((⁅H, K⁆ : Subgroup X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator, mem_normalizer_iff_map_conj_eq.1 (hH hg),
    mem_normalizer_iff_map_conj_eq.1 (hK hg)]

theorem normal_of_le_normalizer {G A M : Subgroup X} (hGA : G ⊔ A = ⊤)
    (hG : G ≤ normalizer (M : Set X)) (hA : A ≤ normalizer (M : Set X)) : M.Normal := by
  have h : G ⊔ A ≤ normalizer (M : Set X) := sup_le hG hA
  rw [hGA] at h
  exact normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem CopAct.mono {q : ℕ} {G H A : Subgroup X} (h : CopAct q G A) (hHG : H ≤ G)
    (hAH : A ≤ normalizer (H : Set X)) : CopAct q H A where
  prime := h.prime
  norm := hAH
  coprime := fun hd => h.coprime (hd.trans (card_dvd_of_le hHG))
  comm := h.comm
  exp := h.exp

/-- `P ∩ C_G(a)'` is a Sylow subgroup of `C_G(a)'`. -/
theorem isSylowOf_inf_commutator_cen [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}] [Finite X] {q p : ℕ}
    [Fact p.Prime] {G A P : Subgroup X}
    (hA : CopAct q G A) (hP : IsSylowOf p P G) (hAP : A ≤ normalizer (P : Set X)) {a : X}
    (ha : a ∈ A) : IsSylowOf p (P ⊓ ⁅cen G a, cen G a⁆) ⁅cen G a, cen G a⁆ := by
  have hq := hA.prime
  have haq := hA.exp a ha
  have hZ : IsPGroup q (zpowers a) := by
    rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one haq) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hZG : zpowers a ≤ normalizer (G : Set X) := zpowers_le.2 (hA.norm ha)
  have hZP : zpowers a ≤ normalizer (P : Set X) := zpowers_le.2 (hAP ha)
  have hS := isSylowOf_inf_centralizer hq hZ hZG hA.coprime hP hZP
  have hcz : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) := by
    ext x
    simp only [mem_centralizer_iff]
    constructor
    · intro h b hb
      rw [Set.mem_singleton_iff.1 hb]
      exact h a (mem_zpowers a)
    · intro h g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
      have hc : Commute a x := h a rfl
      exact (hc.zpow_left k).eq
  rw [hcz] at hS
  have hC : cen G a = G ⊓ centralizer ({a} : Set X) := rfl
  have h2 := hS.inf_of_le_normalizer (N := ⁅cen G a, cen G a⁆) (commutator_self_le _)
    (le_normalizer_commutator' (le_normalizer (H := cen G a)) (le_normalizer (H := cen G a)))
  have e : P ⊓ centralizer ({a} : Set X) ⊓ ⁅cen G a, cen G a⁆ = P ⊓ ⁅cen G a, cen G a⁆ := by
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨hP, _⟩, h⟩; exact ⟨hP, h⟩
    · rintro ⟨hP, h⟩; exact ⟨⟨hP, (commutator_self_le _ h).2⟩, h⟩
  rw [e] at h2
  exact h2

/-- Transport of the conclusion of Theorem 3.1 from a subgroup `K` containing everything. -/
theorem le_gens_of_subgroupOf {G A P K : Subgroup X} (hGK : G ≤ K) (hAK : A ≤ K) (hPK : P ≤ K)
    (h : P.subgroupOf K ⊓ ⁅G.subgroupOf K, G.subgroupOf K⁆ ≤
      gens (P.subgroupOf K) (G.subgroupOf K) (A.subgroupOf K)) :
    P ⊓ ⁅G, G⁆ ≤ gens P G A := by
  have e1 : (P.subgroupOf K ⊓ ⁅G.subgroupOf K, G.subgroupOf K⁆).map K.subtype
      = P ⊓ ⁅G, G⁆ := by
    rw [map_inf_eq _ _ _ K.subtype_injective, map_commutator, map_subgroupOf_eq_of_le hPK,
      map_subgroupOf_eq_of_le hGK]
  have e2 : (gens (P.subgroupOf K) (G.subgroupOf K) (A.subgroupOf K)).map K.subtype
      = gens P G A := by
    rw [map_gens_of_injective _ K.subtype_injective, map_subgroupOf_eq_of_le hPK,
      map_subgroupOf_eq_of_le hGK, map_subgroupOf_eq_of_le hAK]
  rw [← e1, ← e2]
  exact map_mono h

section Quot

variable [Finite X] {N : Subgroup X} [N.Normal]

theorem CopAct.quot {q : ℕ} {G A : Subgroup X} (h : CopAct q G A) :
    CopAct q (G.map (QuotientGroup.mk' N)) (A.map (QuotientGroup.mk' N)) where
  prime := h.prime
  norm := (map_mono h.norm).trans (le_normalizer_map _)
  coprime := fun hd => h.coprime (hd.trans (card_map_dvd _ _))
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.comm a ha b hb]
  exp := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.exp a ha, map_one]

theorem card_map_mk_of_coprime {q : ℕ} {G A : Subgroup X} (h : CopAct q G A) (hNG : N ≤ G) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  symm
  refine Nat.card_congr (Equiv.ofBijective ((QuotientGroup.mk' N).subgroupMap A)
    ⟨?_, (QuotientGroup.mk' N).subgroupMap_surjective A⟩)
  intro a b hab
  have hab' : (QuotientGroup.mk' N) a.1 = (QuotientGroup.mk' N) b.1 :=
    congrArg Subtype.val hab
  have hn : a.1⁻¹ * b.1 ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
  have hq := h.prime
  have hpow : (a.1⁻¹ * b.1) ^ q = 1 := by
    rw [(Commute.mul_pow (show Commute a.1⁻¹ b.1 from
      (Commute.inv_left (h.comm a.1 a.2 b.1 b.2)))), inv_pow, h.exp _ a.2, h.exp _ b.2]; simp
  have hd1 : orderOf (a.1⁻¹ * b.1) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (a.1⁻¹ * b.1) ∣ Nat.card G :=
    (Subgroup.orderOf_dvd_natCard N hn).trans (card_dvd_of_le hNG)
  have h1 : orderOf (a.1⁻¹ * b.1) = 1 := by
    rcases (Nat.dvd_prime hq).1 hd1 with hh | hh
    · exact hh
    · exact absurd (hh ▸ hd2) h.coprime
  have : a.1⁻¹ * b.1 = 1 := orderOf_eq_one_iff.1 h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

theorem card_map_mk_lt {G : Subgroup X} (hNG : N ≤ G) (hN : N ≠ ⊥) :
    Nat.card (G.map (QuotientGroup.mk' N)) < Nat.card G := by
  have hs := (QuotientGroup.mk' N).subgroupMap_surjective G
  have hni : ¬ Function.Injective ((QuotientGroup.mk' N).subgroupMap G) := by
    intro hinj
    obtain ⟨n, hn⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hN
    apply hn
    have : (⟨n.1, hNG n.2⟩ : G) = 1 := by
      apply hinj
      apply Subtype.ext
      show (QuotientGroup.mk' N) n.1 = (QuotientGroup.mk' N) 1
      rw [map_one]
      exact (QuotientGroup.eq_one_iff n.1).2 n.2
    have h3 : n.1 = 1 := congrArg Subtype.val this
    exact Subtype.ext h3
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (G.map (QuotientGroup.mk' N))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective _ hs hni

theorem gens_quot_le [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    {q p : ℕ} [Fact p.Prime] {G A P : Subgroup X} (hA : CopAct q G A)
    (hP : IsSylowOf p P G) (hAP : A ≤ normalizer (P : Set X)) (hNG : N ≤ G) :
    gens (P.map (QuotientGroup.mk' N)) (G.map (QuotientGroup.mk' N))
        (A.map (QuotientGroup.mk' N)) ≤ (gens P G A).map (QuotientGroup.mk' N) := by
  have hker : (QuotientGroup.mk' N).ker ≤ G := by rw [QuotientGroup.ker_mk']; exact hNG
  refine iSup_le fun z => iSup_le fun hz => iSup_le fun hz1 => ?_
  obtain ⟨a, ha, rfl⟩ := hz
  have ha1 : a ≠ 1 := fun h => hz1 (by rw [h, map_one])
  rw [← map_cen hA.prime _ hker hA.coprime (hA.exp a ha), ← map_commutator,
    map_inf_eq_of_isSylowOf hP.isPGroup (isSylowOf_inf_commutator_cen hA hP hAP ha)]
  exact map_mono (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl)))

/-- The quotient step of the proof of Theorem 3.1. -/
theorem quot_step_normal [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    {q p : ℕ} [Fact p.Prime] {G A P : Subgroup X} (hA : CopAct q G A)
    (hP : IsSylowOf p P G) (hAP : A ≤ normalizer (P : Set X)) (hNG : N ≤ G)
    (hbar : P.map (QuotientGroup.mk' N) ⊓
        ⁅G.map (QuotientGroup.mk' N), G.map (QuotientGroup.mk' N)⁆ ≤
      gens (P.map (QuotientGroup.mk' N)) (G.map (QuotientGroup.mk' N))
        (A.map (QuotientGroup.mk' N))) :
    P ⊓ ⁅G, G⁆ ≤ gens P G A ⊔ (P ⊓ N) := by
  rintro x ⟨hxP, hxG⟩
  have h1 : QuotientGroup.mk' N x ∈ P.map (QuotientGroup.mk' N) ⊓
      ⁅G.map (QuotientGroup.mk' N), G.map (QuotientGroup.mk' N)⁆ :=
    ⟨mem_map_of_mem _ hxP, by rw [← map_commutator]; exact mem_map_of_mem _ hxG⟩
  obtain ⟨g, hg, hgx⟩ := gens_quot_le hA hP hAP hNG (hbar h1)
  have hn : g⁻¹ * x ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hgx, inv_mul_cancel]
  have hgP : g ∈ P := gens_le P G A hg
  have := mul_mem_sup hg (show g⁻¹ * x ∈ P ⊓ N from ⟨P.mul_mem (P.inv_mem hgP) hxP, hn⟩)
  rwa [mul_inv_cancel_left] at this

end Quot

end CFSGOutside.GuralnickShumyatsky
