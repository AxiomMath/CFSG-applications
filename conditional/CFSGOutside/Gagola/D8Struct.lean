import CFSGOutside.Corpus.ASevenOrExistsNormalPsl2
import CFSGOutside.Corpus.CardMulAutPsl2GF
import CFSGOutside.Gagola.PSL2Dihedral
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective

/-!
# Structure of `Y / O(Y)` when `Y` has dihedral Sylow 2-subgroups of order 8 and no normal 2-quotient

Let `Y` be a finite group with Sylow 2-subgroups `≃ D₈` and no proper normal subgroup with 2-group quotient.
Then `Ybar = Y / O(Y)` has dihedral Sylow 2-subgroups, trivial odd core and no normal 2-complement, so by the
corpus theorem `aSeven_or_exists_normal_psl2` it is `A₇` or has a normal subgroup `N ≅ PSL(2, q)` with trivial
centraliser. We show that `N` is characteristic, that `q ≠ 3`, and that `[Ybar : N] ∣ 2 f` for `q = p ^ f`.
-/

open scoped MatrixGroups

namespace CFSGOutside.Gagola

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter CFSGOutside.Corpus.AGLEmbedding

noncomputable section

/-! ### The odd core -/

section OddCore

variable {Y : Type*} [Group Y]

theorem odd_card_sup_of_normal [Finite Y] {N M : Subgroup Y} [N.Normal] [M.Normal]
    (hN : Odd (Nat.card N)) (hM : Odd (Nat.card M)) : Odd (Nat.card (N ⊔ M : Subgroup Y)) := by
  have hrel : N.relIndex (N ⊔ M) = N.relIndex M := Subgroup.relIndex_sup_left M N
  have hrelodd : Odd (N.relIndex (N ⊔ M)) := by
    rw [hrel]
    have : N.relIndex M ∣ Nat.card M := Subgroup.index_dvd_card _
    exact Odd.of_dvd_nat hM this
  have hle : N ≤ N ⊔ M := le_sup_left
  have h1 := Subgroup.relIndex_mul_index hle
  have h2 := Subgroup.card_mul_index N
  have h3 := Subgroup.card_mul_index (N ⊔ M)
  have hpos : 0 < (N ⊔ M).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : Nat.card (N ⊔ M : Subgroup Y) = Nat.card N * N.relIndex (N ⊔ M) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (N ⊔ M : Subgroup Y) * (N ⊔ M).index = Nat.card Y := h3
      _ = Nat.card N * N.index := h2.symm
      _ = Nat.card N * (N.relIndex (N ⊔ M) * (N ⊔ M).index) := by rw [h1]
      _ = _ := by ring
  rw [this]
  exact hN.mul hrelodd

theorem odd_card_sSup_normal [Finite Y] (T : Set (Subgroup Y))
    (hT : ∀ N ∈ T, N.Normal ∧ Odd (Nat.card N)) : Odd (Nat.card (sSup T : Subgroup Y)) := by
  have hfin : T.Finite := Set.toFinite T
  induction T, hfin using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha hs ih =>
    rw [sSup_insert]
    have ih' := ih (fun N hN => hT N (Set.mem_insert_of_mem _ hN))
    haveI : (sSup s : Subgroup Y).Normal :=
      Subgroup.sSup_normal _ fun N hN => (hT N (Set.mem_insert_of_mem _ hN)).1
    haveI : a.Normal := (hT a (Set.mem_insert _ _)).1
    rw [sup_comm]
    exact odd_card_sup_of_normal ih' (hT a (Set.mem_insert _ _)).2

theorem odd_card_oddCore [Finite Y] : Odd (Nat.card (oddCore Y)) :=
  odd_card_sSup_normal _ fun _ hN => hN

theorem le_oddCore_of_normal_odd {N : Subgroup Y} [N.Normal] (h : Odd (Nat.card N)) : N ≤ oddCore Y :=
  le_sSup ⟨inferInstance, h⟩

/-- The odd core is characteristic (this also gives `Normal`, see `CFSGOutside.Corpus.oddCore_normal`). -/
theorem oddCore_characteristic {Y : Type*} [Group Y] [Finite Y] : (oddCore Y).Characteristic := by
  have key : ∀ φ : Y ≃* Y, (oddCore Y).map φ.toMonoidHom ≤ oddCore Y := by
    intro φ
    haveI : ((oddCore Y).map φ.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective
    apply le_oddCore_of_normal_odd
    rw [Subgroup.card_map_of_injective φ.injective]
    exact odd_card_oddCore
  refine ⟨fun φ => le_antisymm ?_ ?_⟩
  · have h : (oddCore Y).comap (φ : Y →* Y) = (oddCore Y).map (φ.symm : Y →* Y) :=
      Subgroup.comap_equiv_eq_map_symm φ _
    rw [show (oddCore Y).comap φ.toMonoidHom = _ from h]
    exact key φ.symm
  · intro x hx
    exact key φ ⟨x, hx, rfl⟩

end OddCore

/-! ### `Ybar = Y / O(Y)` -/

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

/-- A Sylow 2-subgroup of `Y` maps isomorphically into `Y / O(Y)`. -/
theorem sylow_equiv_map (P : Sylow 2 Y) :
    Nonempty ((P : Subgroup Y) ≃* (P : Subgroup Y).map (QuotientGroup.mk' (oddCore Y))) := by
  let f : (P : Subgroup Y) →* Y ⧸ oddCore Y := (QuotientGroup.mk' (oddCore Y)).comp (P : Subgroup Y).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : Y) ∈ oddCore Y := by
      have : QuotientGroup.mk' (oddCore Y) (x : Y) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (x : Y) ∣ Nat.card (oddCore Y) := Subgroup.orderOf_dvd_natCard _ hx'
    have h3 : orderOf x = orderOf (x : Y) := (Subgroup.orderOf_coe x).symm
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddCore Y)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr odd_card_oddCore)
    have hcop' : Nat.Coprime (orderOf x) (Nat.card (oddCore Y)) := Nat.Coprime.coprime_dvd_left h1 hcop
    have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop' (h3 ▸ h2)
    exact orderOf_eq_one_iff.mp this
  have hrange : f.range = (P : Subgroup Y).map (QuotientGroup.mk' (oddCore Y)) := by
    ext y
    simp [f, MonoidHom.mem_range, Subgroup.mem_map]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem sylow_quotient_dihedral
    (hD8 : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4))
    (S : Sylow 2 (Y ⧸ oddCore Y)) : Nonempty ((S : Subgroup (Y ⧸ oddCore Y)) ≃* DihedralGroup 4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (oddCore Y)) 2 S
  obtain ⟨e1⟩ := sylow_equiv_map P
  obtain ⟨e2⟩ := hD8 P
  rw [Sylow.coe_mapSurjective]
  exact ⟨e1.symm.trans e2⟩

theorem hasDihedralSylowTwo_quotient
    (hD8 : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4)) :
    HasDihedralSylowTwo (Y ⧸ oddCore Y) := by
  intro S
  obtain ⟨e⟩ := sylow_quotient_dihedral hD8 S
  exact ⟨2, by norm_num, ⟨e⟩⟩

theorem eight_dvd_card_quotient
    (hD8 : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4)) :
    8 ∣ Nat.card (Y ⧸ oddCore Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := sylow_quotient_dihedral hD8 (default : Sylow 2 (Y ⧸ oddCore Y))
  have h1 : Nat.card ((default : Sylow 2 (Y ⧸ oddCore Y)) : Subgroup (Y ⧸ oddCore Y)) = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rw [← h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem oddCore_quotient_eq_bot : oddCore (Y ⧸ oddCore Y) = ⊥ := by
  set K := oddCore (Y ⧸ oddCore Y) with hKdef
  set π := QuotientGroup.mk' (oddCore Y) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : (K.comap π).Normal := Subgroup.Normal.comap inferInstance π
  have hcard : Nat.card (K.comap π) = Nat.card K * Nat.card (oddCore Y) := by
    have hidx : (K.comap π).index = K.index := Subgroup.index_comap_of_surjective K hsurj
    have h1 := Subgroup.card_mul_index (K.comap π)
    have h2 := Subgroup.card_mul_index K
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore Y)
    have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← hidx]
    calc Nat.card (K.comap π) * (K.comap π).index = Nat.card Y := h1
      _ = Nat.card (Y ⧸ oddCore Y) * Nat.card (oddCore Y) := h3
      _ = (Nat.card K * K.index) * Nat.card (oddCore Y) := by rw [h2]
      _ = _ := by rw [hidx]; ring
  have hodd : Odd (Nat.card (K.comap π)) := by
    rw [hcard]; exact odd_card_oddCore.mul odd_card_oddCore
  have hle : K.comap π ≤ oddCore Y := le_oddCore_of_normal_odd hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have : y ∈ K.comap π := hx
  have := hle this
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr this

theorem top_of_isPGroup_quotient
    (hno2 : ∀ (N : Subgroup Y) (_ : N.Normal), IsPGroup 2 (Y ⧸ N) → N = ⊤)
    (T : Subgroup (Y ⧸ oddCore Y)) [T.Normal] (hT : IsPGroup 2 ((Y ⧸ oddCore Y) ⧸ T)) : T = ⊤ := by
  let π : Y →* (Y ⧸ oddCore Y) ⧸ T := (QuotientGroup.mk' T).comp (QuotientGroup.mk' (oddCore Y))
  have hsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective T).comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = T.comap (QuotientGroup.mk' (oddCore Y)) := by
    ext y
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hP : IsPGroup 2 (Y ⧸ π.ker) :=
    hT.of_equiv (QuotientGroup.quotientKerEquivOfSurjective π hsurj).symm
  have htop := hno2 π.ker (MonoidHom.normal_ker π) hP
  rw [hker] at htop
  rw [eq_top_iff]
  intro q _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have : y ∈ T.comap (QuotientGroup.mk' (oddCore Y)) := by rw [htop]; trivial
  exact this

theorem not_hasNormalPComplement_quotient
    (hD8 : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4))
    (hno2 : ∀ (N : Subgroup Y) (_ : N.Normal), IsPGroup 2 (Y ⧸ N) → N = ⊤) :
    ¬ HasNormalPComplement 2 (Y ⧸ oddCore Y) := by
  rintro ⟨T, hTn, hcop, hp⟩
  have hT := top_of_isPGroup_quotient hno2 T hp
  subst hT
  rw [Subgroup.card_top] at hcop
  have h8 := eight_dvd_card_quotient hD8
  have : 2 ∣ Nat.card (Y ⧸ oddCore Y) := dvd_trans (by norm_num) h8
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop this) (by norm_num)

end Ybar

/-! ### The `PSL(2, q)` branch -/

section Psl

theorem card_psl2_mul_two (F : Type) [Field F] [Fintype F] (hodd : Odd (Fintype.card F)) :
    Nat.card PSL(2, F) * 2 = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have hne : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have h2 : ringChar F ≠ 2 := fun h => by
      have h1 := (FiniteField.even_card_iff_char_two (F := F)).mp h
      have h2 := Nat.odd_iff.mp hodd
      omega
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp at this
    exact Ring.neg_one_ne_one_of_char_ne_two h2 this
  have hc := Matrix.SpecialLinearGroup.card_center_eq_two (R := F) hne
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  rw [hc, card_SL2] at h1
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have : Nat.card PSL(2, F) = Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) := rfl
  rw [this]
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = k + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hk] at h1 ⊢
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have e : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    omega
  rw [e]
  nlinarith [h1]

/-- `PSL(2, ·)` is functorial in ring isomorphisms. -/
def psl2Congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) : PSL2 R ≃* PSL2 S :=
  MonoidHom.toMulEquiv (TauCeti.SpecialLinear.projectiveMap 2 (e : R →+* S))
    (TauCeti.SpecialLinear.projectiveMap 2 (e.symm : S →+* R))
    (by
      rw [TauCeti.SpecialLinear.projectiveMap_comp]
      have : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by ext; simp
      rw [this, TauCeti.SpecialLinear.projectiveMap_id])
    (by
      rw [TauCeti.SpecialLinear.projectiveMap_comp]
      have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext; simp
      rw [this, TauCeti.SpecialLinear.projectiveMap_id])

theorem characteristic_of_simple {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) [hNn : N.Normal]
    [IsSimpleGroup N] (hc : Subgroup.centralizer (N : Set Q) = ⊥) : N.Characteristic := by
  have key : ∀ ψ : Q ≃* Q, N.map ψ.toMonoidHom = N := by
    intro ψ
    set N' := N.map ψ.toMonoidHom with hN'
    haveI : N'.Normal := Subgroup.Normal.map hNn ψ.toMonoidHom ψ.surjective
    have hcard : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective ψ.injective
    by_cases hle : N ≤ N'
    · exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
    · exfalso
      have hM : (N ⊓ N').subgroupOf N = ⊥ := by
        haveI : ((N ⊓ N').subgroupOf N).Normal := by
          apply Subgroup.Normal.subgroupOf
          infer_instance
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ N').subgroupOf N) with h | h
        · exact h
        · exfalso
          apply hle
          intro x hx
          have : (⟨x, hx⟩ : N) ∈ (N ⊓ N').subgroupOf N := by rw [h]; trivial
          exact (Subgroup.mem_inf.mp this).2
      have hN'le : N' ≤ Subgroup.centralizer (N : Set Q) := by
        intro m hm
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        have h1 : n * m * n⁻¹ * m⁻¹ ∈ N' :=
          N'.mul_mem (‹N'.Normal›.conj_mem m hm n) (N'.inv_mem hm)
        have h2 : n * m * n⁻¹ * m⁻¹ ∈ N := by
          have := hNn.conj_mem n⁻¹ (N.inv_mem hn) m
          have h3 : m * n⁻¹ * m⁻¹ ∈ N := by simpa using hNn.conj_mem n⁻¹ (N.inv_mem hn) m
          simpa [mul_assoc] using N.mul_mem hn h3
        have h4 : (⟨n * m * n⁻¹ * m⁻¹, h2⟩ : N) ∈ (N ⊓ N').subgroupOf N :=
          Subgroup.mem_inf.mpr ⟨h2, h1⟩
        rw [hM] at h4
        have h5 : n * m * n⁻¹ * m⁻¹ = 1 := by
          have := (Subgroup.mem_bot.mp h4)
          simpa using congrArg Subtype.val this
        have : n * m = m * n := by
          calc n * m = (n * m * n⁻¹ * m⁻¹) * (m * n) := by group
            _ = m * n := by rw [h5, one_mul]
        exact this
      rw [hc] at hN'le
      have : N' = ⊥ := le_bot_iff.mp hN'le
      rw [this, Subgroup.card_bot] at hcard
      have : Nat.card N = 1 := hcard.symm
      have hsub := Nat.card_eq_one_iff_unique.mp this
      exact (not_subsingleton N) hsub.1
  refine ⟨fun ψ => ?_⟩
  have h : N.comap (ψ : Q →* Q) = N.map (ψ.symm : Q →* Q) :=
    Subgroup.comap_equiv_eq_map_symm ψ _
  rw [show N.comap ψ.toMonoidHom = _ from h]
  exact key ψ.symm

/-- The `PSL(2, q)` branch. -/
theorem psl_branch [CardMulAutPsl2GF] {Q : Type} [Group Q] [Finite Q]
    (h8 : 8 ∣ Nat.card Q)
    (htop : ∀ (T : Subgroup Q) (_ : T.Normal), IsPGroup 2 (Q ⧸ T) → T = ⊤)
    (F : Type) [Field F] [Finite F] (hq : IsOddPrimePower (Nat.card F))
    (N : Subgroup Q) [hNn : N.Normal] (eN : N ≃* PSL2 F)
    (hcent : Subgroup.centralizer (N : Set Q) = ⊥) :
    N.Characteristic ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (p f : ℕ) (_ : Fact p.Prime),
        Fintype.card F = p ^ f ∧ 1 ≤ f ∧ Odd (p ^ f) ∧ 5 ≤ p ^ f ∧ Nonempty (N ≃* PSL(2, F)) ∧
          N.index ∣ 2 * f := by
  obtain ⟨p, f, hp, hpodd, hf1, hcardF⟩ := hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hqF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hcardF
  have hqodd : Odd (p ^ f) := hpodd.pow
  -- the order of `N`
  have hN2 : Nat.card N * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr eN.toEquiv, ← hqF]
    exact card_psl2_mul_two F (hqF ▸ hqodd)
  -- `Q` embeds in `Aut N`
  let GF := GaloisField p f
  haveI : Fintype GF := Fintype.ofFinite GF
  have hGF : Nat.card GF = p ^ f := GaloisField.card p f (by omega)
  have eF : F ≃+* GF := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, hcardF])
  let φ : N ≃* PSL2GF p f := eN.trans (psl2Congr eF)
  have hAut : Nat.card (MulAut N) = p ^ f * ((p ^ f) ^ 2 - 1) * f := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact CardMulAutPsl2GF.card_mulAut_psl2GF p f hf1
  have hinj : Function.Injective (MulAut.conjNormal : Q →* MulAut N) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.centralizer (N : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := congrArg (fun a : MulAut N => (a ⟨h, hh⟩ : N).1) hg
      simp at this
      calc h * g = (g * h * g⁻¹) * g := by rw [this]
        _ = g * h := by group
    rw [hcent] at hg'
    exact Subgroup.mem_bot.mp hg'
  have hdvd : Nat.card Q ∣ p ^ f * ((p ^ f) ^ 2 - 1) * f := by
    rw [← hAut]; exact Subgroup.card_dvd_of_injective _ hinj
  have hidx : Nat.card N * N.index = Nat.card Q := Subgroup.card_mul_index N
  have hNpos : 0 < Nat.card N := Nat.card_pos
  -- exclude `q = 3`
  have hq3 : p ^ f ≠ 3 := by
    intro h3
    have hf : f = 1 := by
      by_contra hne
      have : 2 ≤ f := by omega
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos this
      have := hp.two_le
      nlinarith
    subst hf
    have hp3 : p = 3 := by simpa using h3
    subst hp3
    norm_num at hN2 hdvd
    have hN12 : Nat.card N = 12 := by omega
    have hQle : Nat.card Q ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have h12 : 12 ∣ Nat.card Q := ⟨N.index, by rw [← hidx, hN12]⟩
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hQ24 : Nat.card Q = 24 := by omega
    have hidx2 : N.index = 2 := by rw [hN12, hQ24] at hidx; omega
    have hp2 : IsPGroup 2 (Q ⧸ N) := IsPGroup.of_card (n := 1) (by
      rw [pow_one]; exact hidx2)
    have := htop N hNn hp2
    rw [this, Subgroup.index_top] at hidx2
    omega
  have hq5 : 5 ≤ p ^ f := by
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by
        have := hp.two_le
        rcases hpodd with ⟨k, hk⟩
        omega
      calc 3 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf1
    obtain ⟨k, hk⟩ := hqodd
    omega
  -- simplicity and characteristic
  haveI : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [hcardF]; omega)
  haveI : IsSimpleGroup N := eN.isSimpleGroup
  refine ⟨characteristic_of_simple N hcent, F, inferInstance, inferInstance, p, f, ⟨hp⟩, hqF, hf1,
    hqodd, hq5, ⟨eN⟩, ?_⟩
  have h2 : Nat.card N * N.index ∣ Nat.card N * (2 * f) := by
    rw [hidx]
    refine dvd_trans hdvd ?_
    have : p ^ f * ((p ^ f) ^ 2 - 1) * f = Nat.card N * 2 * f := by rw [hN2]
    rw [this]
    exact ⟨1, by ring⟩
  exact Nat.dvd_of_mul_dvd_mul_left hNpos h2

end Psl

/-! ### Main theorem -/

theorem ybar_structure [ASevenOrExistsNormalPsl2] [CardMulAutPsl2GF] {Y : Type} [Group Y] [Finite Y]
    (hD8 : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4))
    (hno2 : ∀ (N : Subgroup Y) (_ : N.Normal), IsPGroup 2 (Y ⧸ N) → N = ⊤) :
    ∃ N : Subgroup (Y ⧸ oddCore Y), N.Characteristic ∧ Subgroup.centralizer (N : Set (Y ⧸ oddCore Y)) = ⊥ ∧
      ((N = ⊤ ∧ Nonempty (N ≃* alternatingGroup (Fin 7))) ∨
       ∃ (F : Type) (_ : Field F) (_ : Fintype F) (p f : ℕ) (_ : Fact p.Prime),
         Fintype.card F = p ^ f ∧ 1 ≤ f ∧ Odd (p ^ f) ∧ 5 ≤ p ^ f ∧ Nonempty (N ≃* PSL(2, F)) ∧
           N.index ∣ 2 * f) := by
  have hDih := hasDihedralSylowTwo_quotient hD8
  have hNC := not_hasNormalPComplement_quotient hD8 hno2
  have hO := oddCore_quotient_eq_bot (Y := Y)
  rcases ASevenOrExistsNormalPsl2.aSeven_or_exists_normal_psl2 hDih hNC hO with
    ⟨⟨e⟩⟩ | ⟨F, _, _, hq, N, hNn, ⟨eN⟩, hcent⟩
  · refine ⟨⊤, inferInstance, ?_, Or.inl ⟨rfl, ⟨Subgroup.topEquiv.trans e⟩⟩⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    have hz : e g ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have := hg (e.symm a) trivial
      have := congrArg e this
      simpa using this
    rw [alternatingGroup.center_eq_bot (by simp)] at hz
    have : e g = 1 := Subgroup.mem_bot.mp hz
    exact Subgroup.mem_bot.mpr (e.injective (by simpa using this))
  · obtain ⟨hch, rest⟩ := psl_branch (eight_dvd_card_quotient hD8)
      (fun T hT hp => haveI := hT; top_of_isPGroup_quotient hno2 T hp) F hq N eN hcent
    exact ⟨N, hch, hcent, Or.inr rest⟩

end

end CFSGOutside.Gagola
