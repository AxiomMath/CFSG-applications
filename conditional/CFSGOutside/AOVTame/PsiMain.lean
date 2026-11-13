import CFSGOutside.AOVTame.PsiInd

/-!
# AOV tameness: `α([(g, 1)])` is pure for every morphism `[g]` of `L(A)`
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

lemma mem_transporter_conjSub {G : Type*} [Group G] (g : G) (P : Subgroup G) :
    g ∈ transporter P (conjSub g P) := fun x hx => by
  rw [mem_conjSub]; simpa [mul_assoc] using hx

/-- `S_A` is fully normalized. -/
lemma isSylowIn_top_normalizer (T : Sylow p A) :
    IsSylowIn p (normalizer ((T : Subgroup A) : Set A) ⊓ T) (normalizer ((T : Subgroup A) : Set A)) := by
  have he : normalizer ((T : Subgroup A) : Set A) ⊓ T = T := inf_eq_right.2 le_normalizer
  rw [he]
  refine ⟨le_normalizer, T.isPGroup', fun h => T.not_dvd_index ?_⟩
  exact h.trans (relIndex_dvd_index_of_le le_normalizer)

section
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

lemma pure_liftA_incl {P Q : Obj p (SA : Subgroup A)} (h : P.val ≤ Q.val) :
    Pure (α.fn.map (liftA SB (incl p _ h : P ⟶ Q))) := by
  rw [liftA_incl]
  obtain ⟨h', e⟩ := hα.2 (prodObj SB P) (prodObj SB Q)
    (prod_mono h le_rfl : (prodObj SB P).val ≤ (prodObj SB Q).val)
  rw [e]; exact pure_incl h'

lemma pure_liftA_comp {P Q R : Obj p (SA : Subgroup A)} {f : P ⟶ Q} {g : Q ⟶ R}
    (h₁ : Pure (α.fn.map (liftA SB f))) (h₂ : Pure (α.fn.map (liftA SB g))) :
    Pure (α.fn.map (liftA SB (f ≫ g))) := by
  rw [liftA_comp, α.fn.map_comp]; exact pure_comp h₁ h₂

/-- Restriction: purity passes from `[g] : P̂ → Q̂` to `[g] : P → Q`. -/
lemma pure_restrict {P Q P' Q' : Obj p (SA : Subgroup A)} (hP : P.val ≤ P'.val) (hQ : Q.val ≤ Q'.val)
    {g : A} (hg : g ∈ transporter P.val Q.val) (hg' : g ∈ transporter P'.val Q'.val)
    (h : Pure (α.fn.map (liftA SB (show P' ⟶ Q' from Tame.mk p g hg')))) :
    Pure (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg))) := by
  have e : (incl p _ hP : P ⟶ P') ≫ (show P' ⟶ Q' from Tame.mk p g hg') =
      (show P ⟶ Q from Tame.mk p g hg) ≫ (incl p _ hQ : Q ⟶ Q') :=
    mk_congr p (by simp) _ _
  have h1 : Pure (α.fn.map (liftA SB ((incl p _ hP : P ⟶ P') ≫ (show P' ⟶ Q' from Tame.mk p g hg')))) :=
    pure_liftA_comp hα hf (pure_liftA_incl hα hf hP) h
  rw [e, liftA_comp, α.fn.map_comp] at h1
  exact pure_cancel_right (pure_liftA_incl hα hf hQ) h1

/-- The elements of `S_A`, on `S_A` itself. -/
lemma pure_top {x : A} (hx : x ∈ (SA : Subgroup A)) :
    Pure (α.fn.map (liftA SB (show topObj SA ⟶ topObj SA from
      Tame.mk p x (mem_transporter_self hx)))) := by
  change Pure (α.fn.map (show topObj (prodSylow SA SB) ⟶ topObj (prodSylow SA SB) from
    Tame.mk p ((x, 1) : A × B) (mem_transporter_self (mem_prodSylow hx (one_mem _)))))
  rw [map_mk_top hα ⟨(x, 1), mem_prodSylow hx (one_mem _)⟩]
  have e := betaFun_pair hα hf x hx 1 (one_mem _)
  have hb1 : bB hα (1 : B) (one_mem _) = 1 := by
    have : betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ = 1 := by
      rw [show (⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ :
        ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) = 1 from rfl, ← beta_apply]
      exact map_one _
    show ((betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ : _) : A × B).2 = 1
    rw [this]; rfl
  rw [hb1] at e
  have hmem : ((bA hα x hx, 1) : A × B) ∈ transporter (α.fn.obj (topObj (prodSylow SA SB))).val
      (α.fn.obj (topObj (prodSylow SA SB))).val := by
    rw [← e, val_obj_top hα]; exact mem_transporter_self (betaFun hα _).2
  exact ⟨bA hα x hx, hmem, mk_congr p e _ _⟩

/-- At a fully normalized `P`, every automorphism `[g]` of `P` gives a pure `α([(g,1)])`. -/
lemma pure_aut {P : Obj p (SA : Subgroup A)}
    (hfn : IsSylowIn p (normalizer (P.val : Set A) ⊓ SA) (normalizer (P.val : Set A)))
    {g : A} (hg : g ∈ transporter P.val P.val) :
    Pure (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg))) := by
  let U : Subgroup A :=
    { carrier := {g | ∃ hg : g ∈ transporter P.val P.val,
        Pure (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg)))}
      mul_mem' := by
        rintro a b ⟨ha, pa⟩ ⟨hb, pb⟩
        refine ⟨mul_mem_transporter ha hb, ?_⟩
        have := pure_liftA_comp hα hf pb pa
        exact this
      one_mem' := ⟨one_mem_transporter le_rfl, by
        change Pure (α.fn.map (liftA SB (𝟙 P)))
        rw [liftA_id, α.fn.map_id]; exact pure_id⟩
      inv_mem' := by
        rintro a ⟨ha, pa⟩
        have ha' : a⁻¹ ∈ transporter P.val P.val :=
          mem_transporter_of_normalizer (inv_mem (mem_normalizer_of_transporter ha))
        refine ⟨ha', ?_⟩
        have e : (show P ⟶ P from Tame.mk p a ha) ≫ (show P ⟶ P from Tame.mk p a⁻¹ ha') = 𝟙 P :=
          mk_congr p (by simp) _ _
        have h1 : Pure (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p a ha)) ≫
            α.fn.map (liftA SB (show P ⟶ P from Tame.mk p a⁻¹ ha'))) := by
          rw [← α.fn.map_comp, ← liftA_comp, e, liftA_id, α.fn.map_id]; exact pure_id
        exact pure_cancel_left rfl pa h1 }
  have hUN : U ≤ normalizer (P.val : Set A) := fun g ⟨hg, _⟩ => mem_normalizer_of_transporter hg
  have hUnorm : (U.subgroupOf (normalizer (P.val : Set A))).Normal := by
    constructor
    rintro ⟨u, huN⟩ hx ⟨n, hn⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hu, pu⟩ := hx
    have hn' : n ∈ transporter P.val P.val := mem_transporter_of_normalizer hn
    have hni : n⁻¹ ∈ transporter P.val P.val := mem_transporter_of_normalizer (inv_mem hn)
    have hconj : n * u * n⁻¹ ∈ transporter P.val P.val :=
      mul_mem_transporter (mul_mem_transporter hn' hu) hni
    refine ⟨hconj, ?_⟩
    have e1 : (show P ⟶ P from Tame.mk p n⁻¹ hni) ≫ (show P ⟶ P from Tame.mk p n hn') = 𝟙 P :=
      mk_congr p (by simp) _ _
    have e2 : (show P ⟶ P from Tame.mk p (n * u * n⁻¹) hconj) =
        (show P ⟶ P from Tame.mk p n⁻¹ hni) ≫ (show P ⟶ P from Tame.mk p u hu) ≫
          (show P ⟶ P from Tame.mk p n hn') := mk_congr p (by group) _ _
    change Pure (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p (n * u * n⁻¹) hconj)))
    rw [e2, liftA_comp, liftA_comp, α.fn.map_comp, α.fn.map_comp]
    refine pure_conj ?_ pu rfl
    rw [← α.fn.map_comp, ← liftA_comp, e1, liftA_id, α.fn.map_id]
  have hQU : normalizer (P.val : Set A) ⊓ SA ≤ U := by
    intro x hx
    have hxS : x ∈ (SA : Subgroup A) := (mem_inf.1 hx).2
    have hxP : x ∈ transporter P.val P.val := mem_transporter_of_normalizer (mem_inf.1 hx).1
    exact ⟨hxP, pure_restrict hα hf (P' := topObj SA) (Q' := topObj SA) P.2.1 P.2.1 hxP
      (mem_transporter_self hxS) (pure_top hα hf hxS)⟩
  have hle := le_of_sylow_pprime hUN hUnorm hQU hfn (fun g hg m hm hgm =>
    ⟨mem_transporter_of_normalizer hg,
      pure_pprime hα hf (mem_transporter_of_normalizer hg) hm hgm⟩)
  obtain ⟨_, h⟩ := hle (mem_normalizer_of_transporter hg)
  exact h

/-- **Claim (3.6b).** For every morphism `[g] : P → Q` of `L(A)`, `α([(g, 1)])` is pure. -/
theorem pure_liftA (P Q : Obj p (SA : Subgroup A)) {g : A} (hg : g ∈ transporter P.val Q.val) :
    Pure (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg))) := by
  suffices H : ∀ n : ℕ, ∀ (P Q : Obj p (SA : Subgroup A)) (g : A) (hg : g ∈ transporter P.val Q.val),
      Nat.card (SA : Subgroup A) - Nat.card P.val = n →
        Pure (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg))) from H _ P Q g hg rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q g hg hn
  have hPS : P.val ≤ SA := P.2.1
  have hQS : Q.val ≤ SA := Q.2.1
  have hcardle : ∀ R : Subgroup A, R ≤ SA → Nat.card R ≤ Nat.card (SA : Subgroup A) :=
    fun R hR => Subgroup.card_le_of_le hR
  by_cases htop : P.val = SA
  · -- `P = S_A`: then `Q = S_A` and `[g]` is an automorphism.
    have hcQ : Nat.card (conjSub g P.val) ≤ Nat.card Q.val := Subgroup.card_le_of_le (by
      rintro _ ⟨x, hx, rfl⟩; exact hg x hx)
    rw [card_conjSub, htop] at hcQ
    have hQ : Q.val = SA := Subgroup.eq_of_le_of_card_ge hQS hcQ
    have hPQ : P = Q := Obj.ext (htop.trans hQ.symm)
    subst hPQ
    have hfn : IsSylowIn p (normalizer (P.val : Set A) ⊓ SA) (normalizer (P.val : Set A)) := by
      rw [htop]; exact isSylowIn_top_normalizer SA
    exact pure_aut hα hf hfn hg
  -- the image `P' = gPg⁻¹`
  have hle : conjSub g P.val ≤ SA := fun _ ⟨x, hx, e⟩ => e ▸ hQS (hg x hx)
  let P' : Obj p (SA : Subgroup A) := ⟨conjSub g P.val, isCentric_conjSub P.2 hle⟩
  have hgP' : g ∈ transporter P.val P'.val := mem_transporter_conjSub g P.val
  have hP'Q : P'.val ≤ Q.val := fun _ ⟨x, hx, e⟩ => e ▸ hg x hx
  have e0 : (show P ⟶ Q from Tame.mk p g hg) =
      (show P ⟶ P' from Tame.mk p g hgP') ≫ (incl p _ hP'Q : P' ⟶ Q) := mk_congr p (by simp) _ _
  rw [e0]
  refine pure_liftA_comp hα hf ?_ (pure_liftA_incl hα hf hP'Q)
  -- a fully normalized conjugate `P*`
  obtain ⟨a, haS, hfn⟩ := exists_fullyNormalized SA hPS
  let Ps : Obj p (SA : Subgroup A) := ⟨conjSub a P.val, isCentric_conjSub P.2 haS⟩
  obtain ⟨y, hyP, hyN⟩ := exists_adjust SA hPS (x := a) rfl hfn
  have hP'S : P'.val ≤ SA := hle
  have hx' : conjSub (a * g⁻¹) P'.val = conjSub a P.val := by
    change conjSub (a * g⁻¹) (conjSub g P.val) = _
    rw [conjSub_conjSub, inv_mul_cancel_right]
  obtain ⟨y', hy'P, hy'N⟩ := exists_adjust SA hP'S hx' hfn
  -- the normalizers, as objects
  let NP : Obj p (SA : Subgroup A) := ⟨normalizer (P.val : Set A) ⊓ SA,
    isCentric_mono P.2 (le_inf le_normalizer hPS) inf_le_right⟩
  let NP' : Obj p (SA : Subgroup A) := ⟨normalizer (P'.val : Set A) ⊓ SA,
    isCentric_mono P'.2 (le_inf le_normalizer hP'S) inf_le_right⟩
  let NPs : Obj p (SA : Subgroup A) := ⟨normalizer (Ps.val : Set A) ⊓ SA,
    isCentric_mono Ps.2 (le_inf le_normalizer haS) inf_le_right⟩
  have hyT : y ∈ transporter NP.val NPs.val := fun x hx => hyN ⟨x, hx, rfl⟩
  have hy'T : y' ∈ transporter NP'.val NPs.val := fun x hx => hy'N ⟨x, hx, rfl⟩
  have hyP' : y ∈ transporter P.val Ps.val := fun x hx => by
    change y * x * y⁻¹ ∈ conjSub a P.val
    rw [← hyP]; exact mem_transporter_conjSub y P.val x hx
  have hy'P' : y' ∈ transporter P'.val Ps.val := fun x hx => by
    change y' * x * y'⁻¹ ∈ conjSub a P.val
    rw [← hy'P]; exact mem_transporter_conjSub y' P'.val x hx
  have hlt : Nat.card P.val < Nat.card NP.val := card_lt_normalizer_inf SA hPS htop
  have hP'ne : P'.val ≠ SA := by
    intro h
    have : Nat.card P'.val = Nat.card P.val := card_conjSub g P.val
    rw [h] at this
    exact htop (Subgroup.eq_of_le_of_card_ge hPS this.le)
  have hlt' : Nat.card P'.val < Nat.card NP'.val := card_lt_normalizer_inf SA hP'S hP'ne
  have hcP' : Nat.card P'.val = Nat.card P.val := card_conjSub g P.val
  have h1 : Pure (α.fn.map (liftA SB (show P ⟶ Ps from Tame.mk p y hyP'))) := by
    refine pure_restrict hα hf (P' := NP) (Q' := NPs) (le_inf le_normalizer hPS)
      (le_inf le_normalizer haS) hyP' hyT ?_
    refine ih _ ?_ NP NPs y hyT rfl
    have := hcardle NP.val inf_le_right
    omega
  have h2 : Pure (α.fn.map (liftA SB (show P' ⟶ Ps from Tame.mk p y' hy'P'))) := by
    refine pure_restrict hα hf (P' := NP') (Q' := NPs) (le_inf le_normalizer hP'S)
      (le_inf le_normalizer haS) hy'P' hy'T ?_
    refine ih _ ?_ NP' NPs y' hy'T rfl
    have := hcardle NP'.val inf_le_right
    omega
  -- the automorphism `[y' g y⁻¹]` of `P*`
  have hyi : y⁻¹ ∈ transporter Ps.val P.val := fun x hx => by
    change x ∈ conjSub a P.val at hx
    rw [← hyP, mem_conjSub] at hx
    simpa using hx
  have hautT : y' * g * y⁻¹ ∈ transporter Ps.val Ps.val :=
    mul_mem_transporter (mul_mem_transporter hy'P' hgP') hyi
  have h3 : Pure (α.fn.map (liftA SB (show Ps ⟶ Ps from Tame.mk p (y' * g * y⁻¹) hautT))) :=
    pure_aut hα hf (P := Ps) hfn hautT
  have e1 : (show P ⟶ Ps from Tame.mk p y hyP') ≫ (show Ps ⟶ Ps from Tame.mk p (y' * g * y⁻¹) hautT) =
      (show P ⟶ P' from Tame.mk p g hgP') ≫ (show P' ⟶ Ps from Tame.mk p y' hy'P') :=
    mk_congr p (by group) _ _
  have h4 := pure_liftA_comp hα hf h1 h3
  rw [e1, liftA_comp, α.fn.map_comp] at h4
  exact pure_cancel_right h2 h4

end

end AndersenOliverVentura.Tame
