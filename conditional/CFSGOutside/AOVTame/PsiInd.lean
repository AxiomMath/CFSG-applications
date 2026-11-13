import CFSGOutside.AOVTame.PsiPure

/-!
# AOV tameness: purity of `α([(g, 1)])` (claim (3.6b) of AOV, proof of Theorem 3.6)
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

lemma mem_prodSylow {a : A} {b : B} (ha : a ∈ (SA : Subgroup A)) (hb : b ∈ (SB : Subgroup B)) :
    ((a, b) : A × B) ∈ ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) := ⟨ha, hb⟩

/-- `β` preserves `S_A × 1` and `1 × S_B`. -/
structure PresFactors {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) : Prop where
  fst : ∀ (a : A) (ha : a ∈ (SA : Subgroup A)),
    ((betaFun hα ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ : _) : A × B).2 = 1
  snd : ∀ (b : B) (hb : b ∈ (SB : Subgroup B)),
    ((betaFun hα ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ : _) : A × B).1 = 1

lemma mem_normalizer_of_transporter {G : Type*} [Group G] [Finite G] {P : Subgroup G} {g : G}
    (hg : g ∈ transporter P P) : g ∈ normalizer (P : Set G) := by
  have hc : conjSub g P = P := Subgroup.eq_of_le_of_card_ge (fun _ ⟨x, hx, e⟩ => e ▸ hg x hx)
    (Nat.card_congr (equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv.symm).ge
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact hg x hx
  · intro hx
    have : g * x * g⁻¹ ∈ conjSub g P := by rw [hc]; exact hx
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this

lemma mem_transporter_of_normalizer {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (P : Set G)) : g ∈ transporter P P :=
  fun x hx => (mem_normalizer_iff.1 hg x).1 hx

section
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)

/-- `β_A`. -/
noncomputable def bA (a : A) (ha : a ∈ (SA : Subgroup A)) : A :=
  ((betaFun hα ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ : _) : A × B).1

/-- `β_B`. -/
noncomputable def bB (b : B) (hb : b ∈ (SB : Subgroup B)) : B :=
  ((betaFun hα ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ : _) : A × B).2

lemma bA_mem (a : A) (ha : a ∈ (SA : Subgroup A)) : bA hα a ha ∈ (SA : Subgroup A) :=
  (betaFun hα ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩).2.1

lemma bB_mem (b : B) (hb : b ∈ (SB : Subgroup B)) : bB hα b hb ∈ (SB : Subgroup B) :=
  (betaFun hα ⟨(1, b), mem_prodSylow (one_mem _) hb⟩).2.2

include hf in
lemma betaFun_pair (a : A) (ha : a ∈ (SA : Subgroup A)) (b : B) (hb : b ∈ (SB : Subgroup B)) :
    ((betaFun hα ⟨(a, b), mem_prodSylow ha hb⟩ : _) : A × B) = (bA hα a ha, bB hα b hb) := by
  have e : (⟨(a, b), mem_prodSylow ha hb⟩ : ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) =
      ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ * ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ :=
    Subtype.ext (Prod.ext (mul_one a).symm (one_mul b).symm)
  rw [e, betaFun_mul]
  ext
  · change _ * _ = _
    rw [hf.snd b hb, mul_one]; rfl
  · change _ * _ = _
    rw [hf.fst a ha, one_mul]; rfl

include hf in
lemma bB_injective {b b' : B} (hb : b ∈ (SB : Subgroup B)) (hb' : b' ∈ (SB : Subgroup B))
    (e : bB hα b hb = bB hα b' hb') : b = b' := by
  have h1 := betaFun_pair hα hf 1 (one_mem _) b hb
  have h2 := betaFun_pair hα hf 1 (one_mem _) b' hb'
  have : betaFun hα ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ =
      betaFun hα ⟨(1, b'), mem_prodSylow (one_mem _) hb'⟩ := Subtype.ext (by rw [h1, h2, e])
  have h3 := congrArg Subtype.val (betaFun_injective hα this)
  simpa using congrArg Prod.snd h3

include hf in
lemma bB_surj {y : B} (hy : y ∈ (SB : Subgroup B)) : ∃ b, ∃ hb : b ∈ (SB : Subgroup B), bB hα b hb = y := by
  let f : ↥(SB : Subgroup B) → ↥(SB : Subgroup B) := fun c => ⟨bB hα (c : B) c.2, bB_mem hα (c : B) c.2⟩
  have hinj : Function.Injective f := fun b b' e =>
    Subtype.ext (bB_injective hα hf b.2 b'.2 (congrArg Subtype.val e))
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨y, hy⟩
  exact ⟨b, b.2, congrArg Subtype.val hb⟩

/-- `α_A` on objects: the first projection of `α(P × S_B)`. -/
noncomputable def objA (P : Obj p (SA : Subgroup A)) : Obj p (SA : Subgroup A) :=
  ⟨(α.fn.obj (prodObj SB P)).val.map (MonoidHom.fst A B), isCentric_fst (α.fn.obj (prodObj SB P)).2⟩

include hf in
lemma obj_prodObj (P : Obj p (SA : Subgroup A)) :
    α.fn.obj (prodObj SB P) = prodObj SB (objA (α := α) P) := by
  apply Obj.ext
  change _ = ((α.fn.obj (prodObj SB P)).val.map (MonoidHom.fst A B)).prod (SB : Subgroup B)
  ext ⟨x, y⟩
  constructor
  · intro h
    exact ⟨⟨(x, y), h, rfl⟩, ((α.fn.obj (prodObj SB P)).2.1 h).2⟩
  · rintro ⟨⟨r, hr, rfl⟩, hy⟩
    have hr' := hr
    rw [obj_val_eq hα] at hr'
    obtain ⟨hrS, hzX⟩ := (mem_bmap_iff (beta hα)).1 hr'
    set z := (beta hα).symm ⟨r, hrS⟩ with hz_def
    have hrz : r = (((beta hα) z : _) : A × B) := by rw [hz_def, MulEquiv.apply_symm_apply]
    obtain ⟨w, hw, hwy⟩ := bB_surj hα hf hy
    have hz1 : (z : A × B).1 ∈ (SA : Subgroup A) := z.2.1
    have hzP : (z : A × B).1 ∈ P.val := (show (z : A × B) ∈ P.val.prod (SB : Subgroup B) from hzX).1
    have hmem : (((z : A × B).1, w) : A × B) ∈ (prodObj SB P).val := ⟨hzP, hw⟩
    rw [obj_val_eq hα]
    have := mem_bmap (β := beta hα) (⟨((z : A × B).1, w), mem_prodSylow hz1 hw⟩ : _) hmem
    rw [beta_apply, betaFun_pair hα hf _ hz1 w hw] at this
    convert this using 1
    have h1 : r.1 = bA hα (z : A × B).1 hz1 := by
      rw [hrz, beta_apply]
      have := betaFun_pair hα hf (z : A × B).1 hz1 (z : A × B).2 z.2.2
      have h2 := congrArg Prod.fst this
      exact h2
    simp only [MonoidHom.coe_fst, Prod.mk.injEq]
    exact ⟨h1, hwy.symm⟩

include hf in
lemma snd_obj (P : Obj p (SA : Subgroup A)) :
    (α.fn.obj (prodObj SB P)).val.map (MonoidHom.snd A B) = SB := by
  rw [obj_prodObj hα hf]; exact map_snd_prod _ _

end

/-- `f ≫ ⋯ ≫ f` (`n` times). -/
def iterComp {C : Type*} [Category C] {X : C} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterComp f n ≫ f

lemma map_iterComp {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X : C} (f : X ⟶ X) :
    ∀ n, F.map (iterComp f n) = iterComp (F.map f) n
  | 0 => F.map_id X
  | n + 1 => by simp only [iterComp, F.map_comp, map_iterComp F f n]

lemma pow_mem_transporter {G : Type*} [Group G] {P : Subgroup G} {h : G}
    (hh : h ∈ transporter P P) : ∀ n : ℕ, h ^ n ∈ transporter P P
  | 0 => by simpa using one_mem_transporter (le_refl P)
  | n + 1 => by rw [pow_succ']; exact mul_mem_transporter hh (pow_mem_transporter hh n)

lemma iterComp_mk {G : Type*} [Group G] [Finite G] {S : Subgroup G} {X : Obj p S} {h : G}
    (hh : h ∈ transporter X.val X.val) : ∀ n,
    iterComp (show X ⟶ X from Tame.mk p h hh) n =
      Tame.mk p (h ^ n) (pow_mem_transporter hh n)
  | 0 => mk_congr p (pow_zero h).symm _ _
  | n + 1 => by
    simp only [iterComp]
    rw [iterComp_mk hh n]
    exact mk_congr p (pow_succ' h n).symm _ _

lemma liftA_iterComp {X : Obj p (SA : Subgroup A)} (f : X ⟶ X) :
    ∀ n, liftA SB (iterComp f n) = iterComp (liftA SB f) n
  | 0 => liftA_id X
  | n + 1 => by simp only [iterComp, liftA_comp, liftA_iterComp f n]

section Purity
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

lemma bA_one : bA hα (1 : A) (one_mem _) = 1 := by
  have : betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ = 1 := by
    rw [show (⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ :
      ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) = 1 from rfl, ← beta_apply]
    exact map_one _
  show ((betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ : _) : A × B).1 = 1
  rw [this]; rfl

lemma snd_centralizer {P Q : Obj p (SA : Subgroup A)} {g : A} (hg : g ∈ transporter P.val Q.val)
    {h : A × B} (hh : h ∈ transporter (α.fn.obj (prodObj SB P)).val (α.fn.obj (prodObj SB Q)).val)
    (e : α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg)) = Tame.mk p h hh) :
    h.2 ∈ centralizer ((SB : Subgroup B) : Set B) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨w, hw, rfl⟩ := bB_surj hα hf hy
  have h1 := map_mk_conj' hα (P := prodObj SB P) (Q := prodObj SB Q) (mem_transporter_prod hg) hh e
    (1, w) ⟨one_mem _, hw⟩
  have h2 : betaFun hα ⟨((g, 1) : A × B) * (1, w) * (g, 1)⁻¹, (prodObj SB Q).2.1
      (mem_transporter_prod hg (1, w) ⟨one_mem _, hw⟩)⟩ =
      betaFun hα ⟨(1, w), mem_prodSylow (one_mem _) hw⟩ := congrArg _ (Subtype.ext (by simp))
  rw [h2] at h1
  have e1 := betaFun_pair hα hf 1 (one_mem _) w hw
  rw [bA_one hα hf] at e1
  have h1' : h * ((betaFun hα ⟨(1, w), mem_prodSylow (one_mem _) hw⟩ : _) : A × B) * h⁻¹ =
      ((betaFun hα ⟨(1, w), mem_prodSylow (one_mem _) hw⟩ : _) : A × B) := h1
  rw [e1] at h1'
  have h4 := congrArg Prod.snd h1'
  simp only [Prod.snd_mul, Prod.snd_inv] at h4
  calc bB hα w hw * h.2 = (h.2 * bB hα w hw * h.2⁻¹) * h.2 := by rw [h4]
    _ = h.2 * bB hα w hw := by group

/-- `α([(g,1)])` is pure as soon as some representative has second coordinate in `O^p(C(S_B))`. -/
lemma pure_of_rep {P Q : Obj p (SA : Subgroup A)} {g : A} (hg : g ∈ transporter P.val Q.val)
    {h : A × B} (hh : h ∈ transporter (α.fn.obj (prodObj SB P)).val (α.fn.obj (prodObj SB Q)).val)
    (e : α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg)) = Tame.mk p h hh)
    (h2 : h.2 ∈ opCent p (SB : Subgroup B)) :
    Pure (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg))) := by
  rw [e]
  exact pure_of_snd hh (by rw [snd_obj hα hf]; exact h2)

/-- `p'`-elements of `Aut_{L(A)}(P)`. -/
lemma pure_pprime {P : Obj p (SA : Subgroup A)} {g : A} (hg : g ∈ transporter P.val P.val) {m : ℕ}
    (hm : ¬ p ∣ m) (hgm : g ^ m = 1) :
    Pure (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg))) := by
  obtain ⟨⟨h, hh⟩, e⟩ := Quotient.exists_rep (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg)))
  have e' : α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg)) = Tame.mk p h hh := e.symm
  have hc := snd_centralizer hα hf hg hh e'
  -- `h^m ∈ O^p(C(α(P × S_B)))`
  have hpow : iterComp (α.fn.map (liftA SB (show P ⟶ P from Tame.mk p g hg))) m = 𝟙 _ := by
    rw [← map_iterComp, ← liftA_iterComp, iterComp_mk]
    have : (Tame.mk p (g ^ m) (pow_mem_transporter hg m) : Mor p P.val P.val) =
        (𝟙 P : P ⟶ P) := mk_congr p hgm _ _
    erw [this, liftA_id, α.fn.map_id]
  rw [e', iterComp_mk] at hpow
  have h1 := opCent_snd ((mk_eq_mk p).1 hpow)
  simp only [Prod.snd_mul, Prod.snd_inv, Prod.pow_snd, Prod.snd_one, mul_one] at h1
  rw [snd_obj hα hf] at h1
  have h1' : h.2 ^ m ∈ opCent p (SB : Subgroup B) := by simpa using inv_mem h1
  obtain ⟨k, hk, z, hz, hkz⟩ := (centralizer_decomp SB (isCentric_self SB)).1 _ hc
  have hzS : z ∈ (SB : Subgroup B) := (mem_inf.1 hz).1
  have hkzc : Commute k z :=
    (mem_centralizer_iff.1 (opCent_le_centralizer p _ hk) z hzS).symm
  have hzm : z ^ m ∈ opCent p (SB : Subgroup B) := by
    have : z ^ m = (k ^ m)⁻¹ * h.2 ^ m := by
      rw [hkz, hkzc.mul_pow]; group
    rw [this]; exact mul_mem (inv_mem (pow_mem hk m)) h1'
  have hzm1 : z ^ m = 1 := eq_one_of_mem_opCent SB (isCentric_self SB) hzm (pow_mem hzS m)
  have hz1 : z = 1 := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 SB.isPGroup') ⟨z, hzS⟩
    rw [orderOf_mk] at hj
    have hdvd : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm1
    rw [hj] at hdvd
    cases j with
    | zero => simpa using hj
    | succ j =>
      exact absurd ((dvd_pow_self p (Nat.succ_ne_zero j)).trans hdvd) hm
  rw [hz1, mul_one] at hkz
  exact pure_of_rep hα hf hg hh e' (hkz ▸ hk)

end Purity

end AndersenOliverVentura.Tame
