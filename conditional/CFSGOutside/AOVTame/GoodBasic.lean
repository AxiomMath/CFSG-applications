import CFSGOutside.AOVTame.MinDecomp
import CFSGOutside.AOVTame.Focal
import CFSGOutside.AOVTame.Factor2

/-!
# AOV tameness: the group-level consequences of reducedness

`Good T` holds for a group `G` with `O(G) = 1` realizing a reduced fusion system, and passes to
retracts `A → P → A` (such as the factors of a direct product) with `O(A) = 1`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

section Reduced
variable {S : Type} [Group S] [Finite S] {F : FusionSystem S} {G : Type} [Group G] [Finite G]
  {T : Sylow 2 G} {E : S →* G}

/-- **`Good` from reducedness.** -/
theorem good_of_reduced (hE : Function.Injective E) (hr : E.range = T) (hR : RealizedBy F E)
    (hred : F.Reduced 2) (hodd : goldschmidtOddCore G = ⊥) : Good T where
  odd := hodd
  two := oTwo_of_normal hR hE T hr hred.2.1
  norm := by
    intro G₀ hN hTG₀ hidx P hP g hg
    obtain ⟨φ, hφ, hφe⟩ := hR.exists_mem hE (P := P.comap E) (Q := ⊤) g⁻¹ (by
      rintro ⟨x, hx⟩
      have : g⁻¹ * E x * g⁻¹⁻¹ ∈ (T : Subgroup G) := hg ⟨E x, hx, rfl⟩
      rw [← hr] at this
      obtain ⟨y, hy⟩ := this
      exact ⟨y, trivial, hy⟩)
    haveI := hN
    obtain ⟨g₀, hg₀, hg₀e⟩ := realized_by_normal hE hr hR hTG₀ hred hidx (P.comap E) ⊤ φ hφ
    refine ⟨g₀⁻¹, inv_mem hg₀, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ : x ∈ E.range := hr ▸ hP hx
    have e1 := hφe ⟨y, hx⟩
    have e2 := hg₀e ⟨y, hx⟩
    rw [e1] at e2
    rw [inv_inv] at e2 ⊢
    exact e2.symm
  foc := le_commutator hE hr hR hred

end Reduced

lemma goldschmidtOddCore_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : goldschmidtOddCore A = ⊥) (hB : goldschmidtOddCore B = ⊥) :
    goldschmidtOddCore (A × B) = ⊥ := by
  rw [eq_bot_iff]
  apply sSup_le
  rintro N ⟨hN, hodd⟩
  have key : ∀ {C : Type} [Group C] [Finite C], goldschmidtOddCore C = ⊥ → ∀ (f : A × B →* C),
      Function.Surjective f → N.map f = ⊥ := by
    intro C _ _ hC f hf
    rw [eq_bot_iff, ← hC]
    apply le_sSup
    refine ⟨hN.map f hf, Odd.of_dvd_nat hodd ?_⟩
    exact Subgroup.card_map_dvd N f
  have h1 := key hA (MonoidHom.fst A B) Prod.fst_surjective
  have h2 := key hB (MonoidHom.snd A B) Prod.snd_surjective
  intro x hx
  rw [mem_bot]
  refine Prod.ext ?_ ?_
  · have : x.1 ∈ N.map (MonoidHom.fst A B) := ⟨x, hx, rfl⟩
    rw [h1, mem_bot] at this; exact this
  · have : x.2 ∈ N.map (MonoidHom.snd A B) := ⟨x, hx, rfl⟩
    rw [h2, mem_bot] at this; exact this

section Retract
variable {A P : Type} [Group A] [Group P] (ι : A →* P) (π : P →* A)
  (hπι : ∀ a, π (ι a) = a) (hconj : ∀ g a, g * ι a * g⁻¹ = ι (π g * a * (π g)⁻¹))
include hπι

lemma retract_injective : Function.Injective ι := fun a b h => by rw [← hπι a, ← hπι b, h]

lemma retract_surjective : Function.Surjective π := fun a => ⟨ι a, hπι a⟩

include hconj

/-- Conjugation in `A` is conjugation in `P` through a retract. -/
lemma realizedBy_retract (X : Subgroup A) : RealizedBy (ofGroup A X) (ι.comp X.subtype) := by
  intro P' Q' φ
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨ι g, fun x => by simp [hg x]⟩
  · rintro ⟨g, hg⟩
    refine ⟨π g, fun x => ?_⟩
    have := hg x
    simp only [MonoidHom.comp_apply, coe_subtype] at this
    rw [hconj] at this
    exact retract_injective ι π hπι this

variable [Finite A] [Finite P] {SA : Sylow 2 A} {TP : Sylow 2 P}

/-- **`Good` passes to retracts.** -/
theorem Good.retract (hP : Good TP) (hιS : (SA : Subgroup A).map ι ≤ TP)
    (hπT : (TP : Subgroup P).map π ≤ SA) (hodd : goldschmidtOddCore A = ⊥) : Good SA where
  odd := hodd
  two D hD hDp := by
    have hD' : (D.map ι).Normal := ⟨fun x hx g => by
      obtain ⟨d, hd, rfl⟩ := hx
      rw [hconj]; exact ⟨_, hD.conj_mem d hd (π g), rfl⟩⟩
    have := hP.two _ hD' (hDp.map ι)
    exact (map_eq_bot_iff_of_injective D (retract_injective ι π hπι)).1 this
  norm G₀ hN hS hidx Q hQ g hg := by
    have hN' : (G₀.comap π).Normal := hN.comap π
    have hT' : (TP : Subgroup P) ≤ G₀.comap π := fun t ht => hS (hπT ⟨t, ht, rfl⟩)
    have hidx' : ¬ 2 ∣ (G₀.comap π).index := by
      rwa [index_comap_of_surjective _ (retract_surjective ι π hπι)]
    have hQ' : Q.map ι ≤ TP := (map_mono hQ).trans hιS
    have hg' : (Q.map ι).map (MulAut.conj (ι g)⁻¹).toMonoidHom ≤ TP := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      apply hιS
      refine ⟨g⁻¹ * x * g⁻¹⁻¹, hg ⟨x, hx, rfl⟩, ?_⟩
      simp
    obtain ⟨g₀, hg₀, hx⟩ := hP.norm _ hN' hT' hidx' (Q.map ι) hQ' (ι g) hg'
    refine ⟨π g₀, hg₀, fun x hx' => ?_⟩
    have := congrArg π (hx (ι x) ⟨x, hx', rfl⟩)
    simpa [hπι] using this
  foc := by
    intro s hs
    have h1 : ι s ∈ commutator P := hP.foc (hιS ⟨s, hs, rfl⟩)
    have h2 : π (ι s) ∈ (commutator P).map π := mem_map_of_mem _ h1
    rw [hπι] at h2
    have h3 : (commutator P).map π ≤ commutator A := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact commutator_mono le_top le_top
    exact h3 h2

end Retract

section Prod
variable {A B : Type} [Group A] [Group B]

lemma inl_retract : ∀ a : A, MonoidHom.fst A B (MonoidHom.inl A B a) = a := fun _ => rfl

lemma inl_conj : ∀ (g : A × B) (a : A), g * MonoidHom.inl A B a * g⁻¹ =
    MonoidHom.inl A B (MonoidHom.fst A B g * a * (MonoidHom.fst A B g)⁻¹) := by
  intro g a; ext <;> simp

lemma inr_retract : ∀ b : B, MonoidHom.snd A B (MonoidHom.inr A B b) = b := fun _ => rfl

lemma inr_conj : ∀ (g : A × B) (b : B), g * MonoidHom.inr A B b * g⁻¹ =
    MonoidHom.inr A B (MonoidHom.snd A B g * b * (MonoidHom.snd A B g)⁻¹) := by
  intro g b; ext <;> simp

end Prod

end AndersenOliverVentura.Tame
