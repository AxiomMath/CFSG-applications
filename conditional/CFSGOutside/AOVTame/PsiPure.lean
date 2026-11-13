import CFSGOutside.AOVTame.PhiHom
import CFSGOutside.AOVTame.SplitAux
import CFSGOutside.AOVTame.PPart

/-!
# AOV tameness: automorphisms of `L(A × B)` preserving both factors (purity)

Let `α ∈ Aut_typ^I(L(A × B))` whose induced `β ∈ Aut(S_A × S_B)` preserves `S_A × 1` and
`1 × S_B`. For `ψ = [g] : P → Q` in `L(A)`, `α([(g, 1)] : P × S_B → Q × S_B) = [(h, z)]` with
`z ∈ C_B(S_B)`; we show (AOV, proof of Theorem 3.6, claim (3.6b)) that in fact `z` can be taken
trivial ("`α([(g,1)])` is pure"). The paper uses Alperin's fusion theorem for linking systems; here
the linking system is `L^c_S(G)` and we argue directly by induction on `|S_A : P|`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

section Prod

lemma map_fst_prod (P : Subgroup A) (Q : Subgroup B) : (P.prod Q).map (MonoidHom.fst A B) = P := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx.1
  · intro ha; exact ⟨(a, 1), ⟨ha, one_mem _⟩, rfl⟩

lemma map_snd_prod (P : Subgroup A) (Q : Subgroup B) : (P.prod Q).map (MonoidHom.snd A B) = Q := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx.2
  · intro hb; exact ⟨(1, b), ⟨one_mem _, hb⟩, rfl⟩

variable (SB) in
/-- `P × S_B`, an object of `L(A × B)`. -/
def prodObj (P : Obj p (SA : Subgroup A)) :
    Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  ⟨P.val.prod SB, isCentric_prod P.2 (isCentric_self SB)⟩

@[simp] lemma prodObj_val (P : Obj p (SA : Subgroup A)) :
    (prodObj SB P).val = P.val.prod (SB : Subgroup B) := rfl

lemma mem_transporter_prod {P Q : Subgroup A} {R : Subgroup B} {g : A} (hg : g ∈ transporter P Q) :
    ((g, 1) : A × B) ∈ transporter (P.prod R) (Q.prod R) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨hg x hx, by simpa using hy⟩

variable (SB) in
/-- `[g] ↦ [(g, 1)]`, `Mor(P, Q) → Mor(P × S_B, Q × S_B)`. -/
def liftA {P Q : Obj p (SA : Subgroup A)} : (P ⟶ Q) → (prodObj SB P ⟶ prodObj SB Q) :=
  Quotient.lift (fun g : transporter P.val Q.val =>
      (Tame.mk p ((g : A), (1 : B)) (mem_transporter_prod g.2) : Mor p _ _))
    (by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ (e : g⁻¹ * g' ∈ opCent p P.val)
      apply (mk_eq_mk p).2
      have := opCent_pair (P := P.val.prod (SB : Subgroup B)) (a := g⁻¹ * g') (b := 1)
        (by rwa [map_fst_prod]) (one_mem _)
      simpa using this)

lemma liftA_mk {P Q : Obj p (SA : Subgroup A)} {g : A} (hg : g ∈ transporter P.val Q.val) :
    liftA SB (show P ⟶ Q from Tame.mk p g hg) = Tame.mk p (g, 1) (mem_transporter_prod hg) := rfl

lemma liftA_id (P : Obj p (SA : Subgroup A)) : liftA SB (𝟙 P) = 𝟙 (prodObj SB P) := rfl

lemma liftA_comp {P Q R : Obj p (SA : Subgroup A)} (f : P ⟶ Q) (g : Q ⟶ R) :
    liftA SB (f ≫ g) = liftA SB f ≫ liftA SB g := by
  obtain ⟨⟨a, ha⟩⟩ := f
  obtain ⟨⟨b, hb⟩⟩ := g
  show Tame.mk p ((b * a : A), (1 : B)) _ = Tame.mk p ((b, 1) * (a, 1) : A × B) _
  exact mk_congr p (by simp) _ _

lemma liftA_incl {P Q : Obj p (SA : Subgroup A)} (h : P.val ≤ Q.val) :
    liftA SB (incl p _ h) = incl p _ (prod_mono h le_rfl : (prodObj SB P).val ≤ (prodObj SB Q).val) :=
  rfl

end Prod

section Pure

variable {R R' R'' : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}

/-- A morphism `[(h, 1)]` with trivial second coordinate. -/
def Pure (m : R ⟶ R') : Prop :=
  ∃ (h : A) (hh : ((h, 1) : A × B) ∈ transporter R.val R'.val), m = Tame.mk p (h, 1) hh

lemma pure_of_snd {g : A × B} (hg : g ∈ transporter R.val R'.val)
    (h2 : g.2 ∈ opCent p (R.val.map (MonoidHom.snd A B))) :
    Pure (show R ⟶ R' from Tame.mk p g hg) := by
  have hc : g.2 ∈ centralizer ((R.val.map (MonoidHom.snd A B) : Subgroup B) : Set B) :=
    opCent_le_centralizer p _ h2
  have hmem : ((g.1, 1) : A × B) ∈ transporter R.val R'.val := by
    intro x hx
    have hx2 : x.2 ∈ R.val.map (MonoidHom.snd A B) := ⟨x, hx, rfl⟩
    have hcomm : g.2 * x.2 * g.2⁻¹ = x.2 := by
      rw [← mem_centralizer_iff.1 hc _ hx2]; group
    have := hg x hx
    convert this using 1
    ext
    · rfl
    · simp [hcomm]
  refine ⟨g.1, hmem, (mk_eq_mk p).2 ?_⟩
  have := opCent_pair (P := R.val) (a := 1) (b := g.2⁻¹) (one_mem _) (inv_mem h2)
  convert this using 1
  ext <;> simp

lemma snd_mem_opCent {g g' : A × B} {hg : g ∈ transporter R.val R'.val}
    {hg' : g' ∈ transporter R.val R'.val}
    (e : (Tame.mk p g hg : Mor p R.val R'.val) = Tame.mk p g' hg') :
    g.2⁻¹ * g'.2 ∈ opCent p (R.val.map (MonoidHom.snd A B)) := by
  have := opCent_snd ((mk_eq_mk p).1 e)
  simpa using this

lemma pure_comp {m : R ⟶ R'} {m' : R' ⟶ R''} (hm : Pure m) (hm' : Pure m') : Pure (m ≫ m') := by
  obtain ⟨h, hh, rfl⟩ := hm
  obtain ⟨k, hk, rfl⟩ := hm'
  exact ⟨k * h, by simpa using mul_mem_transporter hk hh,
    mk_congr p (by simp) _ _⟩

lemma pure_id : Pure (𝟙 R) := ⟨1, one_mem_transporter le_rfl, rfl⟩

lemma pure_incl (h : R.val ≤ R'.val) : Pure (incl p _ h : R ⟶ R') :=
  ⟨1, one_mem_transporter h, rfl⟩

lemma pure_cancel_right {m : R ⟶ R'} {m' : R' ⟶ R''} (hm' : Pure m') (h : Pure (m ≫ m')) :
    Pure m := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := Quotient.exists_rep m
  obtain ⟨k, hk, rfl⟩ := hm'
  obtain ⟨c, hc, e⟩ := h
  have e' : (Tame.mk p ((k, 1) * g) (mul_mem_transporter hk hg) : Mor p R.val R''.val) =
      Tame.mk p (c, 1) hc := e
  have := snd_mem_opCent e'
  simp only [Prod.snd_mul, mul_inv_rev, one_mul, mul_one, inv_one] at this
  exact pure_of_snd hg (by simpa using inv_mem this)

lemma pure_cancel_left {m : R ⟶ R'} {m' : R' ⟶ R''}
    (hR : R.val.map (MonoidHom.snd A B) = R'.val.map (MonoidHom.snd A B)) (hm : Pure m)
    (h : Pure (m ≫ m')) : Pure m' := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := Quotient.exists_rep m'
  obtain ⟨k, hk, rfl⟩ := hm
  obtain ⟨c, hc, e⟩ := h
  have e' : (Tame.mk p (g * (k, 1)) (mul_mem_transporter hg hk) : Mor p R.val R''.val) =
      Tame.mk p (c, 1) hc := e
  have := snd_mem_opCent e'
  simp only [Prod.snd_mul, mul_inv_rev, one_mul, mul_one, inv_one] at this
  exact pure_of_snd hg (by rw [← hR]; simpa using inv_mem this)

lemma pure_conj {m : R ⟶ R'} {m' : R' ⟶ R} (hmm : m ≫ m' = 𝟙 R) {k : R' ⟶ R'} (hk : Pure k)
    (hR : R.val.map (MonoidHom.snd A B) = R'.val.map (MonoidHom.snd A B)) :
    Pure (m ≫ k ≫ m') := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := Quotient.exists_rep m
  obtain ⟨⟨b, hb⟩, rfl⟩ := Quotient.exists_rep m'
  obtain ⟨c, hc, rfl⟩ := hk
  have e : (Tame.mk p (b * a) (mul_mem_transporter hb ha) : Mor p R.val R.val) =
      Tame.mk p 1 (one_mem_transporter le_rfl) := hmm
  have h1 := snd_mem_opCent e
  simp only [Prod.snd_mul, Prod.snd_one, mul_one] at h1
  have e2 : (show R ⟶ R' from Tame.mk p a ha) ≫ (show R' ⟶ R' from Tame.mk p (c, 1) hc) ≫
      (show R' ⟶ R from Tame.mk p b hb) = (show R ⟶ R from Tame.mk p (b * (c, 1) * a)
        (mul_mem_transporter (mul_mem_transporter hb hc) ha)) := rfl
  change Pure ((show R ⟶ R' from Tame.mk p a ha) ≫ (show R' ⟶ R' from Tame.mk p (c, 1) hc) ≫
      (show R' ⟶ R from Tame.mk p b hb))
  rw [e2]
  refine pure_of_snd _ ?_
  have : (b * (c, 1) * a).2 = (a.2⁻¹ * b.2⁻¹)⁻¹ := by simp [mul_assoc]
  rw [this]
  exact inv_mem (by simpa using h1)

end Pure

end AndersenOliverVentura.Tame
