import CFSGOutside.AOVTame.AutI

/-!
# AOV tameness: linking systems of a direct product `A × B`

Projections of centric subgroups of `S_A × S_B` are centric, `C(P) = C(P₁) × C(P₂)`, and
`O^p(C(P))` is compatible with the projections.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]

variable (SA : Sylow p A) (SB : Sylow p B)

/-- The Sylow subgroup `S_A × S_B` of `A × B`. -/
noncomputable def prodSylow : Sylow p (A × B) :=
  IsPGroup.toSylow (P := (SA : Subgroup A).prod SB) (by
      rintro ⟨⟨a, b⟩, ha, hb⟩
      obtain ⟨i, hi⟩ := SA.isPGroup' ⟨a, ha⟩
      obtain ⟨j, hj⟩ := SB.isPGroup' ⟨b, hb⟩
      refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
      · have := congrArg Subtype.val hi
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
        simp only [Prod.pow_fst, Prod.fst_one, pow_add, pow_mul, this, one_pow]
      · have := congrArg Subtype.val hj
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
        simp only [Prod.pow_snd, Prod.snd_one, pow_add, mul_comm (p ^ i), pow_mul, this, one_pow])
    (by
      rw [index_prod]
      exact (Fact.out : p.Prime).not_dvd_mul SA.not_dvd_index SB.not_dvd_index)

@[simp] lemma coe_prodSylow : (prodSylow SA SB : Subgroup (A × B)) = (SA : Subgroup A).prod SB := rfl

variable {SA SB}

lemma mem_centralizer_prod {P : Subgroup (A × B)} {c : A × B} :
    c ∈ centralizer (P : Set (A × B)) ↔
      c.1 ∈ centralizer ((P.map (MonoidHom.fst A B) : Subgroup A) : Set A) ∧
        c.2 ∈ centralizer ((P.map (MonoidHom.snd A B) : Subgroup B) : Set B) := by
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact congrArg Prod.fst (h x hx)
    · rintro _ ⟨x, hx, rfl⟩; exact congrArg Prod.snd (h x hx)
  · rintro ⟨h1, h2⟩ x hx
    exact Prod.ext (h1 _ ⟨x, hx, rfl⟩) (h2 _ ⟨x, hx, rfl⟩)

lemma map_fst_le {P : Subgroup (A × B)} (h : P ≤ (SA : Subgroup A).prod SB) :
    P.map (MonoidHom.fst A B) ≤ SA := by rintro _ ⟨x, hx, rfl⟩; exact (h hx).1

lemma map_snd_le {P : Subgroup (A × B)} (h : P ≤ (SA : Subgroup A).prod SB) :
    P.map (MonoidHom.snd A B) ≤ SB := by rintro _ ⟨x, hx, rfl⟩; exact (h hx).2

lemma conjSub_fst {P : Subgroup (A × B)} (g : A × B) :
    (conjSub g P).map (MonoidHom.fst A B) = conjSub g.1 (P.map (MonoidHom.fst A B)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, rfl⟩

lemma conjSub_snd {P : Subgroup (A × B)} (g : A × B) :
    (conjSub g P).map (MonoidHom.snd A B) = conjSub g.2 (P.map (MonoidHom.snd A B)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, rfl⟩

/-- The first projection of a centric subgroup is centric. -/
lemma isCentric_fst {P : Subgroup (A × B)} (hP : IsCentric ((SA : Subgroup A).prod SB) P) :
    IsCentric (SA : Subgroup A) (P.map (MonoidHom.fst A B)) := by
  refine ⟨map_fst_le hP.1, fun g hg => le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨hyC, hyS⟩ := mem_inf.1 hy
    have hle : conjSub ((g, 1) : A × B) P ≤ (SA : Subgroup A).prod SB := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · exact hg ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
      · simpa using (hP.1 hx).2
    have h1 := hP.2 (g, 1) hle
    have hmem : ((y, 1) : A × B) ∈ centralizer (conjSub ((g, 1) : A × B) P : Set (A × B)) ⊓
        (SA : Subgroup A).prod SB := by
      refine mem_inf.2 ⟨mem_centralizer_prod.2 ⟨?_, ?_⟩, ⟨hyS, one_mem _⟩⟩
      · rw [conjSub_fst]; exact hyC
      · simp
    rw [h1] at hmem
    have := (mem_inf.1 hmem).1
    have h2 : y ∈ (conjSub ((g, 1) : A × B) P).map (MonoidHom.fst A B) := ⟨(y, 1), this, rfl⟩
    rw [conjSub_fst] at h2
    exact mem_inf.2 ⟨h2, hyC⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
    exact mem_inf.2 ⟨hy2, hg hy1⟩

/-- The second projection of a centric subgroup is centric. -/
lemma isCentric_snd {P : Subgroup (A × B)} (hP : IsCentric ((SA : Subgroup A).prod SB) P) :
    IsCentric (SB : Subgroup B) (P.map (MonoidHom.snd A B)) := by
  refine ⟨map_snd_le hP.1, fun g hg => le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨hyC, hyS⟩ := mem_inf.1 hy
    have hle : conjSub ((1, g) : A × B) P ≤ (SA : Subgroup A).prod SB := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using (hP.1 hx).1
      · exact hg ⟨x.2, ⟨x, hx, rfl⟩, rfl⟩
    have h1 := hP.2 (1, g) hle
    have hmem : ((1, y) : A × B) ∈ centralizer (conjSub ((1, g) : A × B) P : Set (A × B)) ⊓
        (SA : Subgroup A).prod SB := by
      refine mem_inf.2 ⟨mem_centralizer_prod.2 ⟨?_, ?_⟩, ⟨one_mem _, hyS⟩⟩
      · simp
      · rw [conjSub_snd]; exact hyC
    rw [h1] at hmem
    have := (mem_inf.1 hmem).1
    have h2 : y ∈ (conjSub ((1, g) : A × B) P).map (MonoidHom.snd A B) := ⟨(1, y), this, rfl⟩
    rw [conjSub_snd] at h2
    exact mem_inf.2 ⟨h2, hyC⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
    exact mem_inf.2 ⟨hy2, hg hy1⟩

lemma opCent_fst {P : Subgroup (A × B)} {c : A × B} (hc : c ∈ opCent p P) :
    c.1 ∈ opCent p (P.map (MonoidHom.fst A B)) := by
  let f : centralizer (P : Set (A × B)) →*
      centralizer ((P.map (MonoidHom.fst A B) : Subgroup A) : Set A) :=
    { toFun := fun c => ⟨c.1.1, (mem_centralizer_prod.1 c.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨c', hc', rfl⟩ := hc
  exact ⟨f c', map_oP_le p f ⟨c', hc', rfl⟩, rfl⟩

lemma opCent_snd {P : Subgroup (A × B)} {c : A × B} (hc : c ∈ opCent p P) :
    c.2 ∈ opCent p (P.map (MonoidHom.snd A B)) := by
  let f : centralizer (P : Set (A × B)) →*
      centralizer ((P.map (MonoidHom.snd A B) : Subgroup B) : Set B) :=
    { toFun := fun c => ⟨c.1.2, (mem_centralizer_prod.1 c.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨c', hc', rfl⟩ := hc
  exact ⟨f c', map_oP_le p f ⟨c', hc', rfl⟩, rfl⟩

lemma opCent_pair {P : Subgroup (A × B)} {a : A} {b : B}
    (ha : a ∈ opCent p (P.map (MonoidHom.fst A B))) (hb : b ∈ opCent p (P.map (MonoidHom.snd A B))) :
    ((a, b) : A × B) ∈ opCent p P := by
  let f₁ : centralizer ((P.map (MonoidHom.fst A B) : Subgroup A) : Set A) →*
      centralizer (P : Set (A × B)) :=
    { toFun := fun c => ⟨((c : A), 1), mem_centralizer_prod.2 ⟨c.2, one_mem _⟩⟩
      map_one' := rfl
      map_mul' := fun x y => by ext <;> simp <;> rfl }
  let f₂ : centralizer ((P.map (MonoidHom.snd A B) : Subgroup B) : Set B) →*
      centralizer (P : Set (A × B)) :=
    { toFun := fun c => ⟨(1, (c : B)), mem_centralizer_prod.2 ⟨one_mem _, c.2⟩⟩
      map_one' := rfl
      map_mul' := fun x y => by ext <;> simp <;> rfl }
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have h1 : ((a' : A), (1 : B)) ∈ opCent p P := ⟨f₁ a', map_oP_le p f₁ ⟨a', ha', rfl⟩, rfl⟩
  have h2 : ((1 : A), (b' : B)) ∈ opCent p P := ⟨f₂ b', map_oP_le p f₂ ⟨b', hb', rfl⟩, rfl⟩
  have := mul_mem h1 h2
  simp only [Prod.mk_mul_mk, mul_one, one_mul] at this
  exact this

lemma mem_transporter_fst {P Q : Subgroup (A × B)} {g : A × B} (hg : g ∈ transporter P Q) :
    g.1 ∈ transporter (P.map (MonoidHom.fst A B)) (Q.map (MonoidHom.fst A B)) := by
  rintro _ ⟨x, hx, rfl⟩; exact ⟨g * x * g⁻¹, hg x hx, rfl⟩

lemma mem_transporter_snd {P Q : Subgroup (A × B)} {g : A × B} (hg : g ∈ transporter P Q) :
    g.2 ∈ transporter (P.map (MonoidHom.snd A B)) (Q.map (MonoidHom.snd A B)) := by
  rintro _ ⟨x, hx, rfl⟩; exact ⟨g * x * g⁻¹, hg x hx, rfl⟩

end AndersenOliverVentura.Tame
