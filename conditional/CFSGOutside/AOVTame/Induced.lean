import CFSGOutside.AOVTame.Centric
import CFSGOutside.AOVTame.MapEquiv
import CFSGOutside.AOVTame.Transport

/-!
# AOV tameness: linking systems under fusion-preserving homomorphisms

Let `f : H → K` be a homomorphism of finite groups carrying a Sylow `p`-subgroup `SH` of `H`
isomorphically onto a Sylow `p`-subgroup `SK` of `K`, such that every `K`-conjugation between
images of subgroups of `SH` is induced by an `H`-conjugation. Then `f` induces an isomorphism of
categories `L^c_{SH}(H) ≅ L^c_{SK}(K)`, `P ↦ f(P)`, `[h] ↦ [f(h)]`.

This covers `H → H/O_{p'}(H)` and the inclusion of a normal subgroup of index prime to `p` with
the same fusion system.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {H K : Type u} [Group H] [Group K] [Finite H] [Finite K] (p : ℕ) [Fact p.Prime]

/-- The hypotheses on `f : H → K`. -/
structure FusionHom (SH : Sylow p H) (SK : Sylow p K) (f : H →* K) : Prop where
  map_eq : (SH : Subgroup H).map f = SK
  inj : ∀ x ∈ (SH : Subgroup H), ∀ y ∈ (SH : Subgroup H), f x = f y → x = y
  fus : ∀ (P : Subgroup H), P ≤ SH → ∀ k : K, (∀ x ∈ P, k * f x * k⁻¹ ∈ (SK : Subgroup K)) →
    ∃ h : H, (∀ x ∈ P, h * x * h⁻¹ ∈ (SH : Subgroup H)) ∧ ∀ x ∈ P, f (h * x * h⁻¹) = k * f x * k⁻¹

variable {p} {SH : Sylow p H} {SK : Sylow p K} {f : H →* K}

namespace FusionHom

variable (hf : FusionHom p SH SK f)
include hf

lemma mem_map_iff {R : Subgroup H} (hR : R ≤ SH) {x : H} (hx : x ∈ (SH : Subgroup H)) :
    f x ∈ R.map f ↔ x ∈ R :=
  ⟨fun ⟨y, hy, e⟩ => (hf.inj y (hR hy) x hx e) ▸ hy, fun h => mem_map_of_mem _ h⟩

lemma map_conjSub {R : Subgroup H} (h : H) : (conjSub h R).map f = conjSub (f h) (R.map f) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, by simp⟩

/-- `f(C_{SH}(R) ...)`: centralizers of subgroups of `SH` correspond. -/
lemma map_centralizer_inf {R : Subgroup H} (hR : R ≤ SH) :
    (centralizer (R : Set H) ⊓ SH).map f = centralizer ((R.map f : Subgroup K) : Set K) ⊓ SK := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsC, hsS⟩ := mem_inf.1 hs
    refine mem_inf.2 ⟨?_, hf.map_eq ▸ mem_map_of_mem _ hsS⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hsC r hr]
  · intro hy
    obtain ⟨hyC, hyS⟩ := mem_inf.1 hy
    rw [← hf.map_eq] at hyS
    obtain ⟨s, hs, rfl⟩ := hyS
    refine ⟨s, mem_inf.2 ⟨?_, hs⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have h1 := mem_centralizer_iff.1 hyC (f r) (mem_map_of_mem _ hr)
    rw [← map_mul, ← map_mul] at h1
    exact hf.inj _ (mul_mem (hR hr) hs) _ (mul_mem hs (hR hr)) h1

lemma map_inf_centralizer {R : Subgroup H} (hR : R ≤ SH) :
    (R ⊓ centralizer (R : Set H)).map f = R.map f ⊓ centralizer ((R.map f : Subgroup K) : Set K) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsR, hsC⟩ := mem_inf.1 hs
    refine mem_inf.2 ⟨mem_map_of_mem _ hsR, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hsC r hr]
  · intro hy
    obtain ⟨⟨s, hs, rfl⟩, hyC⟩ := mem_inf.1 hy
    refine ⟨s, mem_inf.2 ⟨hs, ?_⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have h1 := mem_centralizer_iff.1 hyC (f r) (mem_map_of_mem _ hr)
    rw [← map_mul, ← map_mul] at h1
    exact hf.inj _ (mul_mem (hR hr) (hR hs)) _ (mul_mem (hR hs) (hR hr)) h1

lemma map_le_iff {R Q : Subgroup H} (hR : R ≤ SH) (hQ : Q ≤ SH) : R.map f ≤ Q.map f ↔ R ≤ Q :=
  ⟨fun h x hx => (hf.mem_map_iff hQ (hR hx)).1 (h (mem_map_of_mem _ hx)), map_mono⟩

lemma map_injOn {R Q : Subgroup H} (hR : R ≤ SH) (hQ : Q ≤ SH) (e : R.map f = Q.map f) : R = Q :=
  le_antisymm ((hf.map_le_iff hR hQ).1 e.le) ((hf.map_le_iff hQ hR).1 e.ge)

lemma conjSub_le_of {P : Subgroup H} {h : H} (hh : ∀ x ∈ P, h * x * h⁻¹ ∈ (SH : Subgroup H)) :
    conjSub h P ≤ SH := fun _ ⟨x, hx, e⟩ => e ▸ hh x hx

lemma conjSub_map_eq {P : Subgroup H} {h : H} {k : K}
    (he : ∀ x ∈ P, f (h * x * h⁻¹) = k * f x * k⁻¹) :
    conjSub k (P.map f) = (conjSub h P).map f := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, by simp [he x hx]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [he x hx]⟩

lemma isCentric_map_iff {P : Subgroup H} (hP : P ≤ SH) :
    IsCentric (SH : Subgroup H) P ↔ IsCentric (SK : Subgroup K) (P.map f) := by
  constructor
  · intro hc
    refine ⟨hf.map_eq ▸ map_mono hP, fun k hk => ?_⟩
    obtain ⟨h, hh, he⟩ := hf.fus P hP k (fun x hx => hk ⟨f x, mem_map_of_mem _ hx, rfl⟩)
    have hR := hf.conjSub_le_of hh
    rw [hf.conjSub_map_eq he, ← hf.map_centralizer_inf hR, ← hf.map_inf_centralizer hR,
      hc.2 h hR]
  · intro hc
    refine ⟨hP, fun h hh => ?_⟩
    have he : ∀ x ∈ P, f (h * x * h⁻¹) = f h * f x * (f h)⁻¹ := fun x _ => by simp
    have hR : conjSub h P ≤ SH := hh
    have h2 := hc.2 (f h) (by rw [hf.conjSub_map_eq he, ← hf.map_eq]; exact map_mono hR)
    rw [hf.conjSub_map_eq he, ← hf.map_centralizer_inf hR, ← hf.map_inf_centralizer hR] at h2
    exact hf.map_injOn inf_le_right (inf_le_left.trans hR) h2

lemma mem_transporter_map {P Q : Subgroup H} {h : H} (hh : h ∈ transporter P Q) :
    f h ∈ transporter (P.map f) (Q.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨h * x * h⁻¹, hh x hx, by simp⟩

lemma map_opCent_le (P : Subgroup H) : (opCent p P).map f ≤ opCent p (P.map f) := by
  let g : centralizer (P : Set H) →* centralizer ((P.map f : Subgroup K) : Set K) :=
    { toFun := fun c => ⟨f c, by
        rw [mem_centralizer_iff]
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul, mem_centralizer_iff.1 c.2 x hx]⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [coe_mul, map_mul] }
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨g c, map_oP_le p g ⟨c, hc, rfl⟩, rfl⟩

/-- Every morphism `[k] : f(P) → f(Q)` of `L^c_{SK}(K)` is `[f(h)]` for some `h ∈ N_H(P,Q)`. -/
lemma exists_lift_mor {P Q : Subgroup H} (hP : IsCentric (SH : Subgroup H) P) (hQ : Q ≤ SH)
    {k : K} (hk : k ∈ transporter (P.map f) (Q.map f)) :
    ∃ h ∈ transporter P Q, (f h)⁻¹ * k ∈ opCent p (P.map f) := by
  have hQS : Q.map f ≤ SK := hf.map_eq ▸ map_mono hQ
  obtain ⟨h, hh, he⟩ := hf.fus P hP.1 k (fun x hx => hQS (hk _ (mem_map_of_mem _ hx)))
  have hhQ : h ∈ transporter P Q := fun x hx =>
    (hf.mem_map_iff hQ (hh x hx)).1 (by rw [he x hx]; exact hk _ (mem_map_of_mem _ hx))
  have hc : (f h)⁻¹ * k ∈ centralizer ((P.map f : Subgroup K) : Set K) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := he x hx
    simp only [map_mul, map_inv] at this
    calc f x * ((f h)⁻¹ * k) = (f h)⁻¹ * (f h * f x * (f h)⁻¹) * k := by group
      _ = (f h)⁻¹ * (k * f x * k⁻¹) * k := by rw [this]
      _ = (f h)⁻¹ * k * f x := by group
  have hPc := (hf.isCentric_map_iff hP.1).1 hP
  obtain ⟨k', hk', z, hz, e⟩ := (centralizer_decomp SK hPc).1 _ hc
  rw [← hf.map_inf_centralizer hP.1] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨hz₀P, hz₀C⟩ := mem_inf.1 hz₀
  have hzc : f z₀ * k' = k' * f z₀ := by
    have := mem_centralizer_iff.1 (opCent_le_centralizer p (P.map f) hk') (f z₀) (mem_map_of_mem _ hz₀P)
    exact this
  refine ⟨h * z₀, fun x hx => ?_, ?_⟩
  · have h1 := mem_centralizer_iff.1 hz₀C x hx
    have : h * z₀ * x * (h * z₀)⁻¹ = h * x * h⁻¹ := by
      calc h * z₀ * x * (h * z₀)⁻¹ = h * (z₀ * x) * z₀⁻¹ * h⁻¹ := by group
        _ = h * (x * z₀) * z₀⁻¹ * h⁻¹ := by rw [h1]
        _ = h * x * h⁻¹ := by group
    rw [this]; exact hhQ x hx
  · have : (f (h * z₀))⁻¹ * k = k' := by
      calc (f (h * z₀))⁻¹ * k = (f z₀)⁻¹ * ((f h)⁻¹ * k) := by rw [map_mul]; group
        _ = (f z₀)⁻¹ * (k' * f z₀) := by rw [e]
        _ = (f z₀)⁻¹ * (f z₀ * k') := by rw [hzc]
        _ = k' := by group
    rw [this]; exact hk'

/-- `[f(h)] = [f(h')]` implies `[h] = [h']`. -/
lemma mem_opCent_of_map {P Q : Subgroup H} (hP : IsCentric (SH : Subgroup H) P) (hQ : Q ≤ SH)
    {h h' : H} (hh : h ∈ transporter P Q) (hh' : h' ∈ transporter P Q)
    (e : (f h)⁻¹ * f h' ∈ opCent p (P.map f)) : h⁻¹ * h' ∈ opCent p P := by
  have hfc := opCent_le_centralizer p (P.map f) e
  have hc : h⁻¹ * h' ∈ centralizer (P : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := mem_centralizer_iff.1 hfc (f x) (mem_map_of_mem _ hx)
    have h2 : f (h * x * h⁻¹) = f (h' * x * h'⁻¹) := by
      simp only [map_mul, map_inv]
      calc f h * f x * (f h)⁻¹ = f h * (f x * ((f h)⁻¹ * f h')) * (f h')⁻¹ := by group
        _ = f h * (((f h)⁻¹ * f h') * f x) * (f h')⁻¹ := by rw [h1]
        _ = f h' * f x * (f h')⁻¹ := by group
    have h3 := hf.inj _ (hQ (hh x hx)) _ (hQ (hh' x hx)) h2
    calc x * (h⁻¹ * h') = h⁻¹ * (h * x * h⁻¹) * h' := by group
      _ = h⁻¹ * (h' * x * h'⁻¹) * h' := by rw [h3]
      _ = h⁻¹ * h' * x := by group
  obtain ⟨k₀, hk₀, z₀, hz₀, ex⟩ := (centralizer_decomp SH hP).1 _ hc
  have hPc := (hf.isCentric_map_iff hP.1).1 hP
  have hfz : f z₀ = 1 := by
    apply eq_one_of_mem_opCent SK hPc
    · have hz' : z₀ = k₀⁻¹ * (h⁻¹ * h') := by rw [ex]; group
      have : f z₀ = (f k₀)⁻¹ * ((f h)⁻¹ * f h') := by
        rw [hz']; simp only [map_mul, map_inv]
      rw [this]
      exact mul_mem (inv_mem (hf.map_opCent_le P ⟨k₀, hk₀, rfl⟩)) e
    · exact hf.map_eq ▸ mem_map_of_mem _ (hP.1 (mem_inf.1 hz₀).1)
  have hz : z₀ = 1 := hf.inj _ (hP.1 (mem_inf.1 hz₀).1) _ (one_mem _) (by rw [hfz, map_one])
  rw [ex, hz, mul_one]; exact hk₀

omit hf in
lemma mk_heq' {A A' B B' : Subgroup K} (hA : A = A') (hB : B = B') {g g' : K}
    (hg : g ∈ transporter A B) (hg' : g' ∈ transporter A' B') (e : g⁻¹ * g' ∈ opCent p A) :
    HEq (Tame.mk p g hg) (Tame.mk p g' hg') := by
  subst hA hB
  exact heq_of_eq ((mk_eq_mk p).2 e)

/-- Lift a morphism `A → B` of `L^c_{SK}(K)` with `A = f(P)`, `B = f(Q)` to `P → Q`. -/
noncomputable def liftMor {A B : Subgroup K} {P Q : Subgroup H} (hA : A = P.map f) (hB : B = Q.map f)
    (hP : IsCentric (SH : Subgroup H) P) (hQ : Q ≤ SH) : Mor p A B → Mor p P Q :=
  Quotient.lift (fun k => Tame.mk p (hf.exists_lift_mor hP hQ (hA ▸ hB ▸ k.2 :
      (k : K) ∈ transporter (P.map f) (Q.map f))).choose
      (hf.exists_lift_mor hP hQ (hA ▸ hB ▸ k.2 : (k : K) ∈ transporter (P.map f) (Q.map f))).choose_spec.1)
    (by
      rintro ⟨k, hk⟩ ⟨k', hk'⟩ (e : k⁻¹ * k' ∈ opCent p A)
      have s1 := hf.exists_lift_mor hP hQ (hA ▸ hB ▸ hk : k ∈ transporter (P.map f) (Q.map f))
      have s2 := hf.exists_lift_mor hP hQ (hA ▸ hB ▸ hk' : k' ∈ transporter (P.map f) (Q.map f))
      apply (mk_eq_mk p).2
      apply hf.mem_opCent_of_map hP hQ s1.choose_spec.1 s2.choose_spec.1
      have e3 : k⁻¹ * k' ∈ opCent p (P.map f) := hA ▸ e
      have : (f s1.choose)⁻¹ * f s2.choose =
          ((f s1.choose)⁻¹ * k) * (k⁻¹ * k') * ((f s2.choose)⁻¹ * k')⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem s1.choose_spec.2 e3) (inv_mem s2.choose_spec.2))

lemma liftMor_mk {A B : Subgroup K} {P Q : Subgroup H} (hA : A = P.map f) (hB : B = Q.map f)
    (hP : IsCentric (SH : Subgroup H) P) (hQ : Q ≤ SH) {k : K} (hk : k ∈ transporter A B) {h : H}
    (hh : h ∈ transporter P Q) (e : (f h)⁻¹ * k ∈ opCent p (P.map f)) :
    hf.liftMor hA hB hP hQ (Tame.mk p k hk) = Tame.mk p h hh := by
  show Tame.mk p _ _ = Tame.mk p h hh
  have s1 := hf.exists_lift_mor hP hQ (hA ▸ hB ▸ hk : k ∈ transporter (P.map f) (Q.map f))
  apply (mk_eq_mk p).2
  apply hf.mem_opCent_of_map hP hQ s1.choose_spec.1 hh
  have : (f s1.choose)⁻¹ * f h = ((f s1.choose)⁻¹ * k) * ((f h)⁻¹ * k)⁻¹ := by group
  rw [this]
  exact mul_mem s1.choose_spec.2 (inv_mem e)

lemma map_comap_inf {Q : Subgroup K} (hQ : Q ≤ SK) : (Q.comap f ⊓ SH).map f = Q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (mem_inf.1 hx).1
  · intro hy
    have : y ∈ (SH : Subgroup H).map f := hf.map_eq ▸ hQ hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, mem_inf.2 ⟨hy, hx⟩, rfl⟩

lemma comap_map_inf {P : Subgroup H} (hP : P ≤ SH) : (P.map f).comap f ⊓ SH = P :=
  hf.map_injOn inf_le_right hP (hf.map_comap_inf (hf.map_eq ▸ map_mono hP))

lemma liftMor_exists {A B : Subgroup K} {P Q : Subgroup H} (hA : A = P.map f) (hB : B = Q.map f)
    (hP : IsCentric (SH : Subgroup H) P) (hQ : Q ≤ SH) {k : K} (hk : k ∈ transporter A B) :
    ∃ (h : H) (hh : h ∈ transporter P Q), (f h)⁻¹ * k ∈ opCent p (P.map f) ∧
      hf.liftMor hA hB hP hQ (Tame.mk p k hk) = Tame.mk p h hh := by
  obtain ⟨h, hh, e⟩ := hf.exists_lift_mor hP hQ (hA ▸ hB ▸ hk : k ∈ transporter (P.map f) (Q.map f))
  exact ⟨h, hh, e, hf.liftMor_mk hA hB hP hQ hk hh e⟩

/-- `[h] ↦ [f(h)]`. -/
def fwdMor {P Q : Subgroup H} : Mor p P Q → Mor p (P.map f) (Q.map f) :=
  Quotient.lift (fun h => Tame.mk p (f h) (hf.mem_transporter_map h.2)) (by
    rintro ⟨h, hh⟩ ⟨h', hh'⟩ (e : h⁻¹ * h' ∈ opCent p P)
    apply (mk_eq_mk p).2
    have := hf.map_opCent_le P (mem_map_of_mem _ e)
    simpa using this)

@[simp] lemma fwdMor_mk {P Q : Subgroup H} (h : H) (hh : h ∈ transporter P Q) :
    hf.fwdMor (Tame.mk p h hh) = Tame.mk p (f h) (hf.mem_transporter_map hh) := rfl

/-- The functor `L^c_{SH}(H) → L^c_{SK}(K)`. -/
def fwd : Obj p (SH : Subgroup H) ⥤ Obj p (SK : Subgroup K) where
  obj P := ⟨P.val.map f, (hf.isCentric_map_iff P.2.1).1 P.2⟩
  map φ := hf.fwdMor φ
  map_id P := by
    show hf.fwdMor (Tame.mk p 1 _) = Tame.mk p 1 _
    rw [fwdMor_mk]; exact mk_congr p (map_one f) _ _
  map_comp := by
    rintro P Q R ⟨⟨g, hg⟩⟩ ⟨⟨h, hh⟩⟩
    show hf.fwdMor (comp p (Tame.mk p h hh) (Tame.mk p g hg)) =
      comp p (hf.fwdMor (Tame.mk p h hh)) (hf.fwdMor (Tame.mk p g hg))
    rw [comp_mk, fwdMor_mk, fwdMor_mk, fwdMor_mk, comp_mk]
    exact mk_congr p (map_mul f h g) _ _

/-- The inverse functor `L^c_{SK}(K) → L^c_{SH}(H)`. -/
noncomputable def bwd : Obj p (SK : Subgroup K) ⥤ Obj p (SH : Subgroup H) where
  obj Q := ⟨Q.val.comap f ⊓ SH, (hf.isCentric_map_iff inf_le_right).2
    ((hf.map_comap_inf Q.2.1).symm ▸ Q.2)⟩
  map {Q₁ Q₂} φ := hf.liftMor (hf.map_comap_inf Q₁.2.1).symm (hf.map_comap_inf Q₂.2.1).symm
    ((hf.isCentric_map_iff inf_le_right).2 ((hf.map_comap_inf Q₁.2.1).symm ▸ Q₁.2)) inf_le_right φ
  map_id Q := by
    show hf.liftMor _ _ _ _ (Tame.mk p 1 _) = Tame.mk p 1 _
    apply hf.liftMor_mk
    simp [one_mem]
  map_comp := by
    rintro Q₁ Q₂ Q₃ ⟨⟨k₁, hk₁⟩⟩ ⟨⟨k₂, hk₂⟩⟩
    have e₁ := (hf.map_comap_inf Q₁.2.1).symm
    have e₂ := (hf.map_comap_inf Q₂.2.1).symm
    have e₃ := (hf.map_comap_inf Q₃.2.1).symm
    have c₁ := (hf.isCentric_map_iff inf_le_right).2 (e₁ ▸ Q₁.2)
    have c₂ := (hf.isCentric_map_iff inf_le_right).2 (e₂ ▸ Q₂.2)
    obtain ⟨h₁, hh₁, f₁, E₁⟩ := hf.liftMor_exists e₁ e₂ c₁ inf_le_right hk₁
    obtain ⟨h₂, hh₂, f₂, E₂⟩ := hf.liftMor_exists e₂ e₃ c₂ inf_le_right hk₂
    show hf.liftMor e₁ e₃ c₁ inf_le_right (comp p (Tame.mk p k₂ hk₂) (Tame.mk p k₁ hk₁)) =
      comp p (hf.liftMor e₂ e₃ c₂ inf_le_right (Tame.mk p k₂ hk₂))
        (hf.liftMor e₁ e₂ c₁ inf_le_right (Tame.mk p k₁ hk₁))
    rw [E₁, E₂, comp_mk, comp_mk]
    apply hf.liftMor_mk
    have hk₁' : k₁ ∈ transporter ((Q₁.val.comap f ⊓ SH).map f) ((Q₂.val.comap f ⊓ SH).map f) :=
      e₁ ▸ e₂ ▸ hk₁
    have h3 := conj_mem_opCent p hk₁' f₂
    have : (f (h₂ * h₁))⁻¹ * (k₂ * k₁) = ((f h₁)⁻¹ * k₁) * (k₁⁻¹ * ((f h₂)⁻¹ * k₂) * k₁) := by
      rw [map_mul]; group
    rw [this]
    exact mul_mem f₁ h3

lemma fwd_bwd : hf.fwd ⋙ hf.bwd = 𝟭 _ := by
  apply Functor.hext (fun P => Obj.ext (hf.comap_map_inf P.2.1))
  rintro P Q ⟨⟨h, hh⟩⟩
  have e₁ := (hf.map_comap_inf ((hf.fwd.obj P).2.1)).symm
  have e₂ := (hf.map_comap_inf ((hf.fwd.obj Q).2.1)).symm
  have c₁ := (hf.isCentric_map_iff inf_le_right).2 (e₁ ▸ (hf.fwd.obj P).2)
  have hh' : h ∈ transporter (((P.val.map f).comap f) ⊓ SH) (((Q.val.map f).comap f) ⊓ SH) := by
    rw [hf.comap_map_inf P.2.1, hf.comap_map_inf Q.2.1]; exact hh
  change HEq (hf.liftMor e₁ e₂ c₁ inf_le_right (Tame.mk p (f h) (hf.mem_transporter_map hh)))
    (Tame.mk p h hh)
  refine HEq.trans (heq_of_eq (hf.liftMor_mk e₁ e₂ c₁ inf_le_right (hf.mem_transporter_map hh) hh'
    (by simp [one_mem]))) (mk_heq p (hf.comap_map_inf P.2.1) (hf.comap_map_inf Q.2.1) rfl _ _)

lemma bwd_fwd : hf.bwd ⋙ hf.fwd = 𝟭 _ := by
  apply Functor.hext (fun Q => Obj.ext (hf.map_comap_inf Q.2.1))
  rintro Q₁ Q₂ ⟨⟨k, hk⟩⟩
  have e₁ := (hf.map_comap_inf Q₁.2.1).symm
  have e₂ := (hf.map_comap_inf Q₂.2.1).symm
  have c₁ := (hf.isCentric_map_iff inf_le_right).2 (e₁ ▸ Q₁.2)
  obtain ⟨h, hh, e, E⟩ := hf.liftMor_exists e₁ e₂ c₁ inf_le_right hk
  change HEq (hf.fwdMor (hf.liftMor e₁ e₂ c₁ inf_le_right (Tame.mk p k hk))) (Tame.mk p k hk)
  rw [E, fwdMor_mk]
  exact mk_heq' e₁.symm e₂.symm _ _ e

/-- The isomorphism `L^c_{SH}(H) ≅ L^c_{SK}(K)` induced by `f`. -/
noncomputable def iso : Cat.of (Obj p (SH : Subgroup H)) ≅ Cat.of (Obj p (SK : Subgroup K)) where
  hom := hf.fwd.toCatHom
  inv := hf.bwd.toCatHom
  hom_inv_id := Cat.ext hf.fwd_bwd
  inv_hom_id := Cat.ext hf.bwd_fwd

lemma typIso : TypIso hf.iso := by
  refine ⟨fun P => ?_, fun Q => ?_⟩
  · ext m
    constructor
    · rintro ⟨_, ⟨x, hx, hxP, rfl⟩, rfl⟩
      exact ⟨f x, hf.mem_transporter_map hx, mem_map_of_mem _ hxP, rfl⟩
    · rintro ⟨y, hy, ⟨x, hxP, rfl⟩, rfl⟩
      exact ⟨Tame.mk p x (mem_transporter_self hxP), ⟨x, _, hxP, rfl⟩, rfl⟩
  · have e₁ := (hf.map_comap_inf Q.2.1).symm
    have c₁ := (hf.isCentric_map_iff inf_le_right).2 (e₁ ▸ Q.2)
    ext m
    constructor
    · rintro ⟨_, ⟨k, hk, hkQ, rfl⟩, rfl⟩
      rw [e₁] at hkQ
      obtain ⟨x, hx, rfl⟩ := hkQ
      refine ⟨x, mem_transporter_self hx, hx, ?_⟩
      exact hf.liftMor_mk e₁ e₁ c₁ inf_le_right hk _ (by simp [one_mem])
    · rintro ⟨x, hx, hxP, rfl⟩
      have hfx : f x ∈ Q.val := by rw [e₁]; exact mem_map_of_mem _ hxP
      refine ⟨Tame.mk p (f x) (mem_transporter_self hfx), ⟨f x, _, hfx, rfl⟩, ?_⟩
      exact hf.liftMor_mk e₁ e₁ c₁ inf_le_right _ _ (by simp [one_mem])

end FusionHom

end AndersenOliverVentura.Tame
