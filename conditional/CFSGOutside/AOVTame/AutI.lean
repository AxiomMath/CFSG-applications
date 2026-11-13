import CFSGOutside.AOVTame.Centric
import CFSGOutside.AOVTame.OutTyp

/-!
# AOV tameness: automorphisms of `L^c_S(G)` (AOV Lemma 1.15, [O3, Proposition 6])

Every `α ∈ Aut_typ^I(L^c_S(G))` fixes `S`, induces an automorphism `β` of `S` with
`α([x]) = [β(x)]` on `Aut_L(S)`, satisfies `α(P) = β(P)`, and sends `[g] : P → Q` to some `[h]`
with `h β(x) h⁻¹ = β(g x g⁻¹)` for `x ∈ P`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)

lemma isCentric_self : IsCentric (T : Subgroup G) (T : Subgroup G) := by
  refine ⟨le_rfl, fun g hg => ?_⟩
  have hcard : Nat.card (conjSub g (T : Subgroup G)) = Nat.card (T : Subgroup G) :=
    Nat.card_congr (equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv.symm
  have he : conjSub g (T : Subgroup G) = T := Subgroup.eq_of_le_of_card_ge hg hcard.ge
  rw [he, inf_comm]

/-- The object `S` of `L^c_S(G)`. -/
def topObj : Obj p (T : Subgroup G) := ⟨T, isCentric_self T⟩

/-- A `p`-element of `R · O^p(C_G(R))`, with the first factor in `R`, has trivial second factor. -/
lemma eq_one_of_mul_mem_opCent {R : Subgroup G} (hR : IsCentric (T : Subgroup G) R) {x c : G}
    (hx : x ∈ R) (hc : c ∈ opCent p R) {k : ℕ} (hk : (x * c) ^ (p ^ k) = 1) : c = 1 := by
  have hxc : Commute x c :=
    (mem_centralizer_iff.1 (opCent_le_centralizer p R hc) x hx)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 (T.isPGroup'.to_le hR.1)) ⟨x, hx⟩
  rw [orderOf_mk] at hm
  have hx1 : x ^ (p ^ (k + m)) = 1 := by
    rw [pow_add, pow_mul', ← hm, pow_orderOf_eq_one, one_pow]
  have hc1 : c ^ (p ^ (k + m)) = 1 := by
    have : (x * c) ^ (p ^ (k + m)) = 1 := by
      rw [pow_add, pow_mul, hk, one_pow]
    rwa [hxc.mul_pow, hx1, one_mul] at this
  have hcop := (centralizer_decomp T hR).2
  have hd1 : orderOf c ∣ p ^ (k + m) := orderOf_dvd_of_pow_eq_one hc1
  have hd2 : orderOf c ∣ Nat.card (opCent p R) := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : opCent p R)
    rwa [orderOf_mk] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hd1
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj; exact hj
  · exact absurd ((dvd_pow_self p j.succ_ne_zero).trans (hj ▸ hd2)) hcop

lemma LAut.obj_inv_obj (α : LAut p (T : Subgroup G)) (P : Obj p (T : Subgroup G)) :
    α.fn.obj (α⁻¹.fn.obj P) = P := by
  have h : (α * α⁻¹).fn = 𝟭 _ := by rw [mul_inv_cancel]; rfl
  rw [LAut.fn_mul] at h
  exact congrArg (fun F => F.obj P) h

lemma LAut.obj_obj_inv (α : LAut p (T : Subgroup G)) (P : Obj p (T : Subgroup G)) :
    α⁻¹.fn.obj (α.fn.obj P) = P := by
  have h : (α⁻¹ * α).fn = 𝟭 _ := by rw [inv_mul_cancel]; rfl
  rw [LAut.fn_mul] at h
  exact congrArg (fun F => F.obj P) h

variable {T}

lemma autTypI_obj_top {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G)) :
    α.fn.obj (topObj T) = topObj T := by
  apply Obj.ext
  apply le_antisymm (α.fn.obj (topObj T)).2.1
  intro x hx
  have hP : (α⁻¹.fn.obj (topObj T)).val ≤ (topObj T).val := (α⁻¹.fn.obj (topObj T)).2.1
  obtain ⟨h', -⟩ := hα.2 _ _ hP
  rw [LAut.obj_inv_obj] at h'
  exact h' hx

lemma LAut.map_injective (α : LAut p (T : Subgroup G)) {P Q : Obj p (T : Subgroup G)}
    {f f' : P ⟶ Q} (h : α.fn.map f = α.fn.map f') : f = f' := by
  haveI : α.fn.Faithful := (Cat.equivOfIso α).faithful_functor
  exact α.fn.map_injective h

section
variable {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
include hα

lemma val_obj_top : (α.fn.obj (topObj T)).val = T := congrArg Obj.val (autTypI_obj_top hα)

lemma exists_beta {x : G} (hx : x ∈ (T : Subgroup G)) :
    ∃ (y : G) (hy : y ∈ (T : Subgroup G)),
      α.fn.map (show topObj T ⟶ topObj T from mk p x (mem_transporter_self hx)) =
        mk p y (mem_transporter_self ((val_obj_top hα).symm ▸ hy)) := by
  have hiso := hα.1 (topObj T)
  have hm : α.fn.map (show topObj T ⟶ topObj T from mk p x (mem_transporter_self hx)) ∈
      deltaSet p (T : Subgroup G) (α.fn.obj (topObj T)) :=
    hiso ▸ ⟨_, ⟨x, mem_transporter_self hx, hx, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyP, e⟩ := hm
  exact ⟨y, (val_obj_top hα) ▸ hyP, e⟩

lemma beta_unique {y y' : G} (hy : y ∈ (T : Subgroup G)) (hy' : y' ∈ (T : Subgroup G))
    (e : (mk p y (mem_transporter_self ((val_obj_top hα).symm ▸ hy)) :
      α.fn.obj (topObj T) ⟶ α.fn.obj (topObj T)) =
        mk p y' (mem_transporter_self ((val_obj_top hα).symm ▸ hy'))) : y = y' := by
  have h1 := (mk_eq_mk p).1 e
  have h2 := eq_one_of_mem_opCent T (α.fn.obj (topObj T)).2 h1 (mul_mem (inv_mem hy) hy')
  rw [← mul_inv_cancel_left y y', h2, mul_one]

/-- The automorphism `β` of `S` with `α([x]) = [β(x)]` on `Aut_L(S)`. -/
noncomputable def betaFun (x : (T : Subgroup G)) : (T : Subgroup G) :=
  ⟨(exists_beta hα x.2).choose, (exists_beta hα x.2).choose_spec.choose⟩

lemma map_mk_top (x : (T : Subgroup G)) :
    α.fn.map (show topObj T ⟶ topObj T from mk p x (mem_transporter_self x.2)) =
      mk p (betaFun hα x : G) (mem_transporter_self ((val_obj_top hα).symm ▸ (betaFun hα x).2)) :=
  (exists_beta hα x.2).choose_spec.choose_spec

lemma betaFun_mul (x y : (T : Subgroup G)) : betaFun hα (x * y) = betaFun hα x * betaFun hα y := by
  apply Subtype.ext
  apply beta_unique hα (betaFun hα (x * y)).2 (mul_mem (betaFun hα x).2 (betaFun hα y).2)
  rw [← map_mk_top hα]
  have e : (show topObj T ⟶ topObj T from mk p ((x * y : (T : Subgroup G)) : G)
      (mem_transporter_self (x * y).2)) =
      (show topObj T ⟶ topObj T from mk p (y : G) (mem_transporter_self y.2)) ≫
        (show topObj T ⟶ topObj T from mk p (x : G) (mem_transporter_self x.2)) := rfl
  rw [e, Functor.map_comp, map_mk_top hα, map_mk_top hα]
  rfl

lemma betaFun_injective : Function.Injective (betaFun hα) := by
  intro x y h
  have := map_mk_top hα x
  rw [h, ← map_mk_top hα y] at this
  have h2 := (mk_eq_mk p).1 (LAut.map_injective α this)
  exact Subtype.ext (by
    have h3 := eq_one_of_mem_opCent T (topObj T).2 h2 (mul_mem (inv_mem x.2) y.2)
    rw [← mul_inv_cancel_left (x : G) y, h3, mul_one])

/-- `β ∈ Aut(S)`. -/
noncomputable def beta : (T : Subgroup G) ≃* (T : Subgroup G) :=
  MulEquiv.ofBijective (MonoidHom.mk' (betaFun hα) (betaFun_mul hα))
    (Finite.injective_iff_bijective.1 (betaFun_injective hα))

lemma beta_apply (x : (T : Subgroup G)) : beta hα x = betaFun hα x := rfl

/-- `α([x]_P) = [β(x)]_{α(P)}` for `x ∈ P`. -/
lemma map_mk_delta (P : Obj p (T : Subgroup G)) {x : G} (hx : x ∈ P.val) :
    ∃ hb : (betaFun hα ⟨x, P.2.1 hx⟩ : G) ∈ (α.fn.obj P).val,
      α.fn.map (show P ⟶ P from mk p x (mem_transporter_self hx)) =
        mk p (betaFun hα ⟨x, P.2.1 hx⟩ : G) (mem_transporter_self hb) := by
  have hm : α.fn.map (show P ⟶ P from mk p x (mem_transporter_self hx)) ∈
      deltaSet p (T : Subgroup G) (α.fn.obj P) :=
    hα.1 P ▸ ⟨_, ⟨x, mem_transporter_self hx, hx, rfl⟩, rfl⟩
  obtain ⟨y, hyt, hyP, e⟩ := hm
  obtain ⟨hle, hι⟩ := hα.2 P (topObj T) P.2.1
  have key : (show P ⟶ P from mk p x (mem_transporter_self hx)) ≫ incl p (T : Subgroup G) P.2.1 =
      incl p (T : Subgroup G) P.2.1 ≫
        (show topObj T ⟶ topObj T from mk p ((⟨x, P.2.1 hx⟩ : (T : Subgroup G)) : G)
          (mem_transporter_self (⟨x, P.2.1 hx⟩ : (T : Subgroup G)).2)) :=
    mk_congr p (by simp) _ _
  have hm := map_mk_top hα ⟨x, P.2.1 hx⟩
  have key' : (mk p y hyt : α.fn.obj P ⟶ α.fn.obj P) ≫ incl p (T : Subgroup G) hle =
      incl p (T : Subgroup G) hle ≫ (mk p (betaFun hα ⟨x, P.2.1 hx⟩ : G)
        (mem_transporter_self ((val_obj_top hα).symm ▸ (betaFun hα ⟨x, P.2.1 hx⟩).2)) :
          α.fn.obj (topObj T) ⟶ α.fn.obj (topObj T)) := by
    rw [← e, ← hι, ← hm, ← Functor.map_comp, ← Functor.map_comp, key]
  have h1 := (mk_eq_mk p).1 key'
  have hyT : y ∈ (T : Subgroup G) := (α.fn.obj P).2.1 hyP
  have h2 := eq_one_of_mem_opCent T (α.fn.obj P).2 h1
    (by simpa using mul_mem (inv_mem hyT) (betaFun hα ⟨x, P.2.1 hx⟩).2)
  have hyb : y = betaFun hα ⟨x, P.2.1 hx⟩ := by
    have : (1 * y)⁻¹ * ((betaFun hα ⟨x, P.2.1 hx⟩ : G) * 1) = 1 := h2
    simpa [inv_mul_eq_one] using this
  subst hyb
  exact ⟨hyP, e⟩

end

/-- The image `β(P)` of `P ≤ S` under `β ∈ Aut(S)`, as a subgroup of `G`. -/
def bmap (β : (T : Subgroup G) ≃* (T : Subgroup G)) (P : Subgroup G) : Subgroup G :=
  ((P.subgroupOf T).map β.toMonoidHom).map (T : Subgroup G).subtype

lemma mem_bmap {β : (T : Subgroup G) ≃* (T : Subgroup G)} {P : Subgroup G} (x : (T : Subgroup G))
    (hx : (x : G) ∈ P) : ((β x : (T : Subgroup G)) : G) ∈ bmap β P :=
  ⟨β x, ⟨x, hx, rfl⟩, rfl⟩

lemma card_bmap (β : (T : Subgroup G) ≃* (T : Subgroup G)) {P : Subgroup G} (hP : P ≤ T) :
    Nat.card (bmap β P) = Nat.card P := by
  rw [bmap, Nat.card_congr (equivMapOfInjective _ _ (T : Subgroup G).subtype_injective).toEquiv.symm,
    Nat.card_congr (equivMapOfInjective _ _ β.injective).toEquiv.symm]
  exact Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv

lemma bmap_le_obj {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (P : Obj p (T : Subgroup G)) : bmap (beta hα) P.val ≤ (α.fn.obj P).val := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact (map_mk_delta hα P hx).1

lemma obj_val_eq {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (P : Obj p (T : Subgroup G)) : (α.fn.obj P).val = bmap (beta hα) P.val := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (bmap_le_obj hα P)
  have hα' : α⁻¹ ∈ autTypI p (T : Subgroup G) := inv_mem hα
  have h1 := bmap_le_obj hα' (α.fn.obj P)
  rw [LAut.obj_obj_inv] at h1
  have h2 := Subgroup.card_le_of_le h1
  rw [card_bmap _ (α.fn.obj P).2.1] at h2
  rw [card_bmap _ P.2.1]
  exact h2

lemma betaFun_mul_aut {α α' : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (hα' : α' ∈ autTypI p (T : Subgroup G)) (x : (T : Subgroup G)) :
    betaFun (mul_mem hα hα') x = betaFun hα (betaFun hα' x) := by
  obtain ⟨hb1, e1⟩ := map_mk_delta (mul_mem hα hα') (topObj T) (x := (x : G)) x.2
  obtain ⟨hb2, e2⟩ := map_mk_delta hα' (topObj T) (x := (x : G)) x.2
  obtain ⟨hb3, e3⟩ := map_mk_delta hα (α'.fn.obj (topObj T)) (x := (betaFun hα' ⟨x, x.2⟩ : G)) hb2
  have e : (α * α').fn.map (show topObj T ⟶ topObj T from mk p x (mem_transporter_self x.2)) =
      α.fn.map (α'.fn.map (show topObj T ⟶ topObj T from mk p x (mem_transporter_self x.2))) := rfl
  rw [e1, e2, e3] at e
  have h1 := (mk_eq_mk p).1 e
  have h2 := eq_one_of_mem_opCent T ((α * α').fn.obj (topObj T)).2 h1
    (mul_mem (inv_mem (betaFun _ _).2) (betaFun _ _).2)
  apply Subtype.ext
  rw [← mul_inv_cancel_left (betaFun (mul_mem hα hα') ⟨x, x.2⟩ : G)
    (betaFun hα ⟨_, hb2 |> fun h => (α'.fn.obj (topObj T)).2.1 h⟩ : G), h2, mul_one]

lemma betaFun_one_aut (x : (T : Subgroup G)) :
    betaFun (one_mem (autTypI p (T : Subgroup G))) x = x := by
  obtain ⟨hb, e⟩ := map_mk_delta (one_mem (autTypI p (T : Subgroup G))) (topObj T)
    (x := (x : G)) x.2
  have e' : (1 : LAut p (T : Subgroup G)).fn.map
      (show topObj T ⟶ topObj T from mk p x (mem_transporter_self x.2)) =
      mk p (x : G) (mem_transporter_self x.2) := rfl
  rw [e'] at e
  have h1 := (mk_eq_mk p).1 e
  have h2 := eq_one_of_mem_opCent T (topObj T).2 h1 (mul_mem (inv_mem x.2) (betaFun _ _).2)
  apply Subtype.ext
  rw [← mul_inv_cancel_left (x : G) (betaFun _ x : G), h2, mul_one]

lemma betaFun_congr {α α' : LAut p (T : Subgroup G)} (e : α = α')
    (hα : α ∈ autTypI p (T : Subgroup G)) (hα' : α' ∈ autTypI p (T : Subgroup G))
    (x : (T : Subgroup G)) : betaFun hα x = betaFun hα' x := by
  subst e; rfl

lemma betaFun_inv_aut {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (x : (T : Subgroup G)) : betaFun (inv_mem hα) (betaFun hα x) = x := by
  have h := betaFun_mul_aut (inv_mem hα) hα x
  have e : betaFun (mul_mem (inv_mem hα) hα) x = x := by
    rw [betaFun_congr (inv_mul_cancel α) _ (one_mem _), betaFun_one_aut]
  rw [← h, e]

/-- AOV Lemma 1.15 (`π ∘ α = c_β ∘ π`): `α([g]) = [h]` with `h β(x) h⁻¹ = β(gxg⁻¹)` on `P`. -/
lemma map_mk_conj {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    {P Q : Obj p (T : Subgroup G)} {g : G} (hg : g ∈ transporter P.val Q.val) :
    ∃ (h : G) (hh : h ∈ transporter (α.fn.obj P).val (α.fn.obj Q).val),
      α.fn.map (show P ⟶ Q from mk p g hg) = mk p h hh ∧
      ∀ (x : G) (hx : x ∈ P.val), h * betaFun hα ⟨x, P.2.1 hx⟩ * h⁻¹ =
        betaFun hα ⟨g * x * g⁻¹, Q.2.1 (hg x hx)⟩ := by
  obtain ⟨⟨h, hh⟩, e⟩ := Quotient.exists_rep (α.fn.map (show P ⟶ Q from mk p g hg))
  refine ⟨h, hh, e.symm, fun x hx => ?_⟩
  have hgx : g * x * g⁻¹ ∈ Q.val := hg x hx
  obtain ⟨hb1, e1⟩ := map_mk_delta hα P hx
  obtain ⟨hb2, e2⟩ := map_mk_delta hα Q hgx
  have key : (show P ⟶ P from mk p x (mem_transporter_self hx)) ≫ (show P ⟶ Q from mk p g hg) =
      (show P ⟶ Q from mk p g hg) ≫ (show Q ⟶ Q from mk p (g * x * g⁻¹) (mem_transporter_self hgx)) :=
    mk_congr p (by group) _ _
  have key' : (show α.fn.obj P ⟶ α.fn.obj P from mk p _ (mem_transporter_self hb1)) ≫
      (show α.fn.obj P ⟶ α.fn.obj Q from mk p h hh) =
      (show α.fn.obj P ⟶ α.fn.obj Q from mk p h hh) ≫
        (show α.fn.obj Q ⟶ α.fn.obj Q from mk p _ (mem_transporter_self hb2)) := by
    have e' : α.fn.map (show P ⟶ Q from mk p g hg) = mk p h hh := e.symm
    rw [← e1, ← e2, ← e', ← Functor.map_comp, ← Functor.map_comp, key]
  have h1 := (mk_eq_mk p).1 key'
  set b := (betaFun hα ⟨x, P.2.1 hx⟩ : G)
  set b' := (betaFun hα ⟨g * x * g⁻¹, Q.2.1 hgx⟩ : G)
  have hc : b⁻¹ * (h⁻¹ * b' * h) ∈ opCent p (α.fn.obj P).val := by
    have : (h * b)⁻¹ * (b' * h) = b⁻¹ * (h⁻¹ * b' * h) := by group
    rw [← this]; exact h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 T.isPGroup')
    (betaFun hα ⟨g * x * g⁻¹, Q.2.1 hgx⟩)
  rw [orderOf_mk] at hk
  have hpe : (b * (b⁻¹ * (h⁻¹ * b' * h))) ^ (p ^ k) = 1 := by
    rw [mul_inv_cancel_left]
    have h2 := map_pow (MulAut.conj h⁻¹) b' (p ^ k)
    simp only [MulAut.conj_apply, inv_inv] at h2
    rw [← h2, ← hk, pow_orderOf_eq_one]
    simp
  have hc1 := eq_one_of_mul_mem_opCent T (α.fn.obj P).2 hb1 hc hpe
  have : h⁻¹ * b' * h = b := by
    rw [← mul_inv_cancel_left b (h⁻¹ * b' * h), hc1, mul_one]
  rw [← this]; group

lemma betaFun_inv_aut' {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (x : (T : Subgroup G)) : betaFun hα (betaFun (inv_mem hα) x) = x := by
  have h := betaFun_inv_aut (inv_mem hα) x
  rwa [betaFun_congr (inv_inv α) (inv_mem (inv_mem hα)) hα] at h

/-- `map_mk_conj` for an arbitrary representative of `α([g])`. -/
lemma map_mk_conj' {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    {P Q : Obj p (T : Subgroup G)} {g : G} (hg : g ∈ transporter P.val Q.val) {h' : G}
    (hh' : h' ∈ transporter (α.fn.obj P).val (α.fn.obj Q).val)
    (e : α.fn.map (show P ⟶ Q from mk p g hg) = mk p h' hh') (x : G) (hx : x ∈ P.val) :
    h' * betaFun hα ⟨x, P.2.1 hx⟩ * h'⁻¹ = betaFun hα ⟨g * x * g⁻¹, Q.2.1 (hg x hx)⟩ := by
  obtain ⟨h, hh, e₀, hrel⟩ := map_mk_conj hα hg
  rw [e₀] at e
  have hc := opCent_le_centralizer p _ ((mk_eq_mk p).1 e)
  have hb := (map_mk_delta hα P hx).1
  have h1 := mem_centralizer_iff.1 hc _ hb
  rw [← hrel x hx]
  calc h' * (betaFun hα ⟨x, P.2.1 hx⟩ : G) * h'⁻¹
      = h * ((h⁻¹ * h') * betaFun hα ⟨x, P.2.1 hx⟩) * (h⁻¹ * h')⁻¹ * h⁻¹ := by group
    _ = h * (betaFun hα ⟨x, P.2.1 hx⟩ * (h⁻¹ * h')) * (h⁻¹ * h')⁻¹ * h⁻¹ := by rw [h1]
    _ = h * betaFun hα ⟨x, P.2.1 hx⟩ * h⁻¹ := by group

end AndersenOliverVentura.Tame
