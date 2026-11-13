import CFSGOutside.AndersenOliverVentura.Defs

/-!
# AOV tameness: the centric linking system of a finite group

For a finite group `G` and `S ≤ G`, the centric linking system `L^c_S(G)` (AOV §1.2, after
Definition 1.9): its objects are the `F_S(G)`-centric subgroups `P ≤ S`, and
`Mor(P,Q) = N_G(P,Q) / O^p(C_G(P))`, where `N_G(P,Q) = {g | gPg⁻¹ ≤ Q}` and `O^p(C_G(P))` acts by
right multiplication. Composition is induced by multiplication in `G`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G]

/-- The transporter `N_G(P,Q) = {g ∈ G | gPg⁻¹ ≤ Q}`. -/
def transporter (P Q : Subgroup G) : Set G := {g | ∀ x ∈ P, g * x * g⁻¹ ∈ Q}

lemma one_mem_transporter {P Q : Subgroup G} (h : P ≤ Q) : (1 : G) ∈ transporter P Q :=
  fun x hx => by simpa using h hx

lemma mul_mem_transporter {P Q R : Subgroup G} {g h : G} (hh : h ∈ transporter Q R)
    (hg : g ∈ transporter P Q) : h * g ∈ transporter P R := fun x hx => by
  have := hh _ (hg x hx)
  simpa [mul_assoc] using this

lemma mem_transporter_self {P : Subgroup G} {x : G} (hx : x ∈ P) : x ∈ transporter P P :=
  fun y hy => P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)

/-- The conjugate `gPg⁻¹`. -/
def conjSub (g : G) (P : Subgroup G) : Subgroup G := P.map (MulAut.conj g).toMonoidHom

lemma mem_conjSub {g : G} {P : Subgroup G} {y : G} :
    y ∈ conjSub g P ↔ g⁻¹ * y * g ∈ P := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa [mul_assoc] using hx
  · intro h; exact ⟨_, h, by simp [mul_assoc]⟩

/-- `P ≤ S` is `F_S(G)`-centric (AOV Definition 1.2): `C_S(P*) = Z(P*)` for every subgroup
`P* = gPg⁻¹ ≤ S` which is `F_S(G)`-conjugate to `P`. -/
def IsCentric (S P : Subgroup G) : Prop :=
  P ≤ S ∧ ∀ g : G, conjSub g P ≤ S →
    centralizer (conjSub g P : Set G) ⊓ S = conjSub g P ⊓ centralizer (conjSub g P : Set G)

lemma conjSub_conjSub (g h : G) (P : Subgroup G) : conjSub g (conjSub h P) = conjSub (g * h) P := by
  ext x; simp only [mem_conjSub, mul_inv_rev]; group

variable (p : ℕ)

/-- `O^p(C_G(P))`, as a subgroup of `G`. -/
def opCent (P : Subgroup G) : Subgroup G :=
  (FusionSystem.oP p (centralizer (P : Set G))).map (centralizer (P : Set G)).subtype

lemma opCent_le_centralizer (P : Subgroup G) : opCent p P ≤ centralizer (P : Set G) :=
  map_subtype_le _

/-- A homomorphism carries `O^p` into `O^p`. -/
lemma map_oP_le [hp : Fact p.Prime] {H K : Type*} [Group H] [Group K] (f : H →* K) :
    (FusionSystem.oP p H).map f ≤ FusionSystem.oP p K := by
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, FusionSystem.oP, mem_sInf]
  rintro N ⟨hN, k, hk⟩
  have hd : (N.comap f).index ∣ p ^ k := by
    rw [index_comap, ← hk]; exact relIndex_dvd_index_of_normal (H := N) (K := f.range)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hd
  exact (mem_sInf.1 hx) (N.comap f) ⟨hN.comap f, j, hj⟩

lemma conj_mem_opCent [Fact p.Prime] {P Q : Subgroup G} {g : G} (hg : g ∈ transporter P Q)
    {k : G} (hk : k ∈ opCent p Q) : g⁻¹ * k * g ∈ opCent p P := by
  let f : centralizer (Q : Set G) →* centralizer (P : Set G) :=
    { toFun := fun c => ⟨g⁻¹ * c * g, by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := mem_centralizer_iff.1 c.2 _ (hg x hx)
        calc x * (g⁻¹ * c * g) = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
          _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [h1]
          _ = g⁻¹ * c * g * x := by group⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [coe_mul]; group }
  obtain ⟨c, hc, rfl⟩ := hk
  have := map_oP_le p f ⟨c, hc, rfl⟩
  exact ⟨_, this, rfl⟩

/-- The objects of `L^c_S(G)` (for the prime `p`): the `F_S(G)`-centric subgroups of `S`. -/
@[ext] structure Obj (_p : ℕ) (S : Subgroup G) : Type u where
  /-- The underlying subgroup. -/
  val : Subgroup G
  /-- It is `F_S(G)`-centric. -/
  prop : IsCentric S val

/-- `N_G(P,Q)` modulo right multiplication by `O^p(C_G(P))`. -/
def morSetoid (P Q : Subgroup G) : Setoid (transporter P Q) where
  r g h := (g : G)⁻¹ * h ∈ opCent p P
  iseqv := ⟨fun g => by simp [one_mem], fun {g h} hgh => by
      have := inv_mem hgh; simpa using this,
    fun {a b c} hab hbc => by
      have := mul_mem hab hbc; simpa [mul_assoc] using this⟩

/-- `Mor_{L^c_S(G)}(P,Q) = N_G(P,Q)/O^p(C_G(P))`. -/
def Mor (P Q : Subgroup G) : Type u := Quotient (morSetoid p P Q)

/-- The class `[g]` of `g ∈ N_G(P,Q)`. -/
def mk {P Q : Subgroup G} (g : G) (hg : g ∈ transporter P Q) : Mor p P Q :=
  Quotient.mk _ ⟨g, hg⟩

lemma mk_eq_mk {P Q : Subgroup G} {g h : G} {hg : g ∈ transporter P Q}
    {hh : h ∈ transporter P Q} : mk p g hg = mk p h hh ↔ g⁻¹ * h ∈ opCent p P :=
  Quotient.eq

lemma mk_congr {P Q : Subgroup G} {g h : G} (e : g = h) (hg : g ∈ transporter P Q)
    (hh : h ∈ transporter P Q) : mk p g hg = mk p h hh := by
  subst e; rfl

lemma mk_heq_of_mem {P P' Q Q' : Subgroup G} (hP : P = P') (hQ : Q = Q') {g g' : G}
    (hg : g ∈ transporter P Q) (hg' : g' ∈ transporter P' Q') (e : g⁻¹ * g' ∈ opCent p P) :
    HEq (mk p g hg) (mk p g' hg') := by
  subst hP hQ
  exact heq_of_eq ((mk_eq_mk p).2 e)

/-- Composition `[h] ∘ [g] = [hg]`. -/
def comp [Fact p.Prime] {P Q R : Subgroup G} (ψ : Mor p Q R) (φ : Mor p P Q) : Mor p P R :=
  Quotient.liftOn₂ ψ φ (fun h g => mk p ((h : G) * g) (mul_mem_transporter h.2 g.2))
    (by
      rintro ⟨h, hh⟩ ⟨g, hg⟩ ⟨h', hh'⟩ ⟨g', hg'⟩ (e₁ : h⁻¹ * h' ∈ _) (e₂ : g⁻¹ * g' ∈ _)
      apply (mk_eq_mk p).2
      have h3 := conj_mem_opCent p hg e₁
      have : (h * g)⁻¹ * (h' * g') = (g⁻¹ * (h⁻¹ * h') * g) * (g⁻¹ * g') := by group
      rw [this]; exact mul_mem h3 e₂)

@[simp] lemma comp_mk [Fact p.Prime] {P Q R : Subgroup G} (h g : G) (hh : h ∈ transporter Q R)
    (hg : g ∈ transporter P Q) :
    comp p (mk p h hh) (mk p g hg) = mk p (h * g) (mul_mem_transporter hh hg) := rfl

variable (S : Subgroup G)

/-- The centric linking system `L^c_S(G)` as a category. -/
instance linkingCategory [Fact p.Prime] : Category (Obj p S) where
  Hom P Q := Mor p P.1 Q.1
  id P := mk p 1 (one_mem_transporter le_rfl)
  comp φ ψ := comp p ψ φ
  id_comp := by
    rintro P Q ⟨⟨g, hg⟩⟩
    show comp p (mk p g hg) (mk p 1 _) = mk p g hg
    rw [comp_mk]; simp only [mul_one]
  comp_id := by
    rintro P Q ⟨⟨g, hg⟩⟩
    show comp p (mk p 1 _) (mk p g hg) = mk p g hg
    rw [comp_mk]; simp only [one_mul]
  assoc := by
    rintro P Q R T ⟨⟨f, hf⟩⟩ ⟨⟨g, hg⟩⟩ ⟨⟨h, hh⟩⟩
    show comp p (mk p h hh) (comp p (mk p g hg) (mk p f hf)) =
      comp p (comp p (mk p h hh) (mk p g hg)) (mk p f hf)
    simp only [comp_mk, mul_assoc]

section Aut

variable [Fact p.Prime]

/-- The inclusion `ι_P^Q = [1]` for `P ≤ Q`. -/
def incl {P Q : Obj p S} (h : P.1 ≤ Q.1) : P ⟶ Q := mk p 1 (one_mem_transporter h)

/-- `δ_P(P) ⊆ Aut_L(P)`: the classes of the elements of `P`. -/
def deltaSet (P : Obj p S) : Set (P ⟶ P) :=
  {m | ∃ (x : G) (hx : x ∈ transporter P.1 P.1), x ∈ P.1 ∧ m = mk p x hx}

/-- A functor `L → L` is isotypical (AOV Definition 1.13(b)): `α(δ_P(P)) = δ_{α(P)}(α(P))`. -/
def IsIsotypical (F : Obj p S ⥤ Obj p S) : Prop :=
  ∀ P : Obj p S, F.map '' deltaSet p S P = deltaSet p S (F.obj P)

/-- A functor `L → L` sends inclusions to inclusions. -/
def PreservesIncl (F : Obj p S ⥤ Obj p S) : Prop :=
  ∀ (P Q : Obj p S) (h : P.1 ≤ Q.1), ∃ h' : (F.obj P).1 ≤ (F.obj Q).1, F.map (incl p S h) = incl p S h'

lemma IsIsotypical.comp {F F' : Obj p S ⥤ Obj p S} (hF : IsIsotypical p S F)
    (hF' : IsIsotypical p S F') : IsIsotypical p S (F ⋙ F') := fun P => by
  change (fun m => F'.map (F.map m)) '' _ = _
  rw [show (fun m : P ⟶ P => F'.map (F.map m)) = F'.map ∘ F.map from rfl, Set.image_comp, hF P,
    hF' (F.obj P)]
  rfl

lemma PreservesIncl.comp {F F' : Obj p S ⥤ Obj p S} (hF : PreservesIncl p S F)
    (hF' : PreservesIncl p S F') : PreservesIncl p S (F ⋙ F') := fun P Q h => by
  obtain ⟨h₁, e₁⟩ := hF P Q h
  obtain ⟨h₂, e₂⟩ := hF' _ _ h₁
  exact ⟨h₂, by change F'.map (F.map _) = _; rw [e₁, e₂]⟩

lemma isIsotypical_id : IsIsotypical p S (𝟭 (Obj p S)) := fun P => by simp

lemma preservesIncl_id : PreservesIncl p S (𝟭 (Obj p S)) := fun P Q h => ⟨h, rfl⟩

instance [Finite G] : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective

instance [Finite G] : Finite (Obj p S) :=
  Finite.of_injective (fun P : Obj p S => P.val) (fun _ _ h => Obj.ext h)

instance [Finite G] (P Q : Subgroup G) : Finite (Mor p P Q) := Quotient.finite _

instance [Finite G] (P Q : Obj p S) : Finite (P ⟶ Q) := inferInstanceAs (Finite (Mor p P.1 Q.1))

/-- The automorphism group of the category `L^c_S(G)`. -/
abbrev LAut := Aut (Cat.of (Obj p S))

/-- The underlying functor of an automorphism. -/
abbrev LAut.fn (α : LAut p S) : Obj p S ⥤ Obj p S := α.hom.toFunctor

lemma LAut.fn_mul (α β : LAut p S) : (α * β).fn = β.fn ⋙ α.fn := rfl

lemma LAut.fn_one : (1 : LAut p S).fn = 𝟭 _ := rfl

lemma LAut.ext_fn {α β : LAut p S} (h : α.fn = β.fn) : α = β := by
  apply Iso.ext; exact Cat.ext h

instance [Finite G] : Finite (LAut p S) := by
  let M := Σ PQ : Obj p S × Obj p S, PQ.1 ⟶ PQ.2
  let enc : LAut p S → (Obj p S → Obj p S) × (M → M) := fun α =>
    (α.fn.obj, fun m => ⟨(α.fn.obj m.1.1, α.fn.obj m.1.2), α.fn.map m.2⟩)
  refine Finite.of_injective enc ?_
  intro α β h
  simp only [enc, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  apply LAut.ext_fn
  apply Functor.hext (fun X => congrFun h1 X)
  intro X Y f
  have := congrFun h2 ⟨(X, Y), f⟩
  exact (Sigma.ext_iff.1 this).2

/-- The isotypical, inclusion-preserving automorphisms, as a submonoid. -/
def autTypIMonoid : Submonoid (LAut p S) where
  carrier := {α | IsIsotypical p S α.fn ∧ PreservesIncl p S α.fn}
  one_mem' := ⟨isIsotypical_id p S, preservesIncl_id p S⟩
  mul_mem' := fun {α β} hα hβ => by
    show IsIsotypical p S (α * β).fn ∧ PreservesIncl p S (α * β).fn
    rw [LAut.fn_mul]
    exact ⟨hβ.1.comp p S hα.1, hβ.2.comp p S hα.2⟩

/-- `Aut_typ^I(L)` (AOV Definition 1.13(d)): the isotypical automorphisms of `L^c_S(G)` which send
inclusions to inclusions. By AOV Lemma 1.14(a) every isotypical self-equivalence sending
inclusions to inclusions is an automorphism; that it is closed under inverses is proved here. -/
def autTypI [Finite G] : Subgroup (LAut p S) where
  toSubmonoid := autTypIMonoid p S
  inv_mem' := fun {α} hα => by
    have hinv : α⁻¹ = α ^ (orderOf α - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos α), pow_orderOf_eq_one]
    rw [hinv]; exact Submonoid.pow_mem _ hα _

end Aut

end AndersenOliverVentura.Tame
