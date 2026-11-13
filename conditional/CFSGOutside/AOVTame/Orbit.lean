import CFSGOutside.AOVTame.HigherLim
import CFSGOutside.AOVTame.Linking

/-!
# The centric orbit category of `F_S(G)` and the functors `Z^K_F / Z^H_F`

For `F = F_S(G)`, the centric orbit category `O(F^c)` (AOV Definition 2.9) has as objects the
`F`-centric subgroups `P ≤ S`, and `Mor(P, Q) = Inn(Q) \ Hom_F(P, Q)`. Since
`Hom_F(P, Q) = N_G(P, Q) / C_G(P)`, this is the double coset space `Q \ N_G(P, Q) / C_G(P)`,
which is how it is encoded here.

For `H ≤ K` normal in `G`, `Z^K_F / Z^H_F : O(F^c)ᵒᵖ → Ab` sends `P` to
`(Z(P) ∩ K) / (Z(P) ∩ H)`, and `[φ] : P → Q` to the map induced by `φ⁻¹|_{Z(Q)}`; for `φ = c_g`
this is `z ↦ g⁻¹ z g`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {G : Type} [Group G] (p : ℕ) (S : Subgroup G)

/-- Objects of the centric orbit category: the centric subgroups of `S`. -/
@[ext] structure OObj (_p : ℕ) (S : Subgroup G) where
  val : Subgroup G
  prop : IsCentric S val

variable {p S}

/-- `g ~ q g c` for `q ∈ Q`, `c ∈ C_G(P)`. -/
def orbSetoid (P Q : Subgroup G) : Setoid (transporter P Q) where
  r g g' := ∃ q ∈ Q, ∃ c ∈ centralizer (P : Set G), (g' : G) = q * g * c
  iseqv := by
    refine ⟨fun g => ⟨1, one_mem _, 1, one_mem _, by simp⟩, ?_, ?_⟩
    · rintro g g' ⟨q, hq, c, hc, e⟩
      exact ⟨q⁻¹, inv_mem hq, c⁻¹, inv_mem hc, by rw [e]; group⟩
    · rintro g g' g'' ⟨q, hq, c, hc, e⟩ ⟨q', hq', c', hc', e'⟩
      exact ⟨q' * q, mul_mem hq' hq, c * c', mul_mem hc hc', by rw [e', e]; group⟩

/-- `Mor_{O(F^c)}(P, Q) = Q \ N_G(P, Q) / C_G(P)`. -/
def OMor (P Q : Subgroup G) : Type := Quotient (orbSetoid P Q)

/-- The class of `g ∈ N_G(P, Q)`. -/
def omk {P Q : Subgroup G} (g : G) (hg : g ∈ transporter P Q) : OMor P Q :=
  Quotient.mk (orbSetoid P Q) ⟨g, hg⟩

lemma conj_mem_centralizer {P Q : Subgroup G} {g : G} (hg : g ∈ transporter P Q) {d : G}
    (hd : d ∈ centralizer (Q : Set G)) : g⁻¹ * d * g ∈ centralizer (P : Set G) := by
  rw [mem_centralizer_iff] at hd ⊢
  intro x hx
  have := hd _ (hg x hx)
  calc x * (g⁻¹ * d * g) = g⁻¹ * ((g * x * g⁻¹) * d) * g := by group
    _ = g⁻¹ * (d * (g * x * g⁻¹)) * g := by rw [this]
    _ = g⁻¹ * d * g * x := by group

/-- Composition `[h] ∘ [g] = [hg]`. -/
def ocomp {P Q R : Subgroup G} : OMor Q R → OMor P Q → OMor P R :=
  Quotient.lift₂ (fun h g => omk ((h : G) * g) (mul_mem_transporter h.2 g.2)) (by
    rintro ⟨h, hh⟩ ⟨g, hg⟩ ⟨h', hh'⟩ ⟨g', hg'⟩ ⟨r, hr, d, hd, e₁⟩ ⟨q, hq, c, hc, e₂⟩
    apply Quotient.sound
    refine ⟨r * (h * q * h⁻¹), mul_mem hr (by simpa [mul_assoc] using hh q hq),
      g⁻¹ * d * g * c, mul_mem (conj_mem_centralizer hg hd) hc, ?_⟩
    change h' = r * h * d at e₁
    change g' = q * g * c at e₂
    change h' * g' = r * (h * q * h⁻¹) * (h * g) * (g⁻¹ * d * g * c)
    rw [e₁, e₂]
    have hdq : d * q = q * d := (mem_centralizer_iff.1 hd q hq).symm
    calc r * h * d * (q * g * c) = r * h * (d * q) * g * c := by group
      _ = r * h * (q * d) * g * c := by rw [hdq]
      _ = r * (h * q * h⁻¹) * (h * g) * (g⁻¹ * d * g * c) := by group)

lemma ocomp_id {P Q : Subgroup G} (f : OMor P Q) :
    ocomp f (omk 1 (one_mem_transporter le_rfl)) = f := by
  induction f using Quotient.inductionOn with
  | h g => exact Quotient.sound ⟨1, one_mem _, 1, one_mem _, by simp⟩

lemma id_ocomp {P Q : Subgroup G} (f : OMor P Q) :
    ocomp (omk 1 (one_mem_transporter le_rfl)) f = f := by
  induction f using Quotient.inductionOn with
  | h g => exact Quotient.sound ⟨1, one_mem _, 1, one_mem _, by simp⟩

lemma ocomp_assoc {P Q R T : Subgroup G} (f : OMor P Q) (g : OMor Q R) (h : OMor R T) :
    ocomp h (ocomp g f) = ocomp (ocomp h g) f := by
  induction f using Quotient.inductionOn with
  | h a =>
  induction g using Quotient.inductionOn with
  | h b =>
  induction h using Quotient.inductionOn with
  | h c => exact Quotient.sound ⟨1, one_mem _, 1, one_mem _, by simp [mul_assoc]⟩

instance orbitCategory : Category (OObj p S) where
  Hom P Q := OMor P.val Q.val
  id P := omk 1 (one_mem_transporter le_rfl)
  comp f g := ocomp g f
  id_comp f := ocomp_id f
  comp_id f := id_ocomp f
  assoc f g h := ocomp_assoc f g h

section Z
variable (K H : Subgroup G)

/-- `Z(P) ∩ K`. -/
def zK (P : Subgroup G) (K : Subgroup G) : Subgroup G := (P ⊓ centralizer (P : Set G)) ⊓ K

instance (P : Subgroup G) : CommGroup (zK P K) :=
  { (inferInstance : Group (zK P K)) with
    mul_comm := fun a b => Subtype.ext
      (mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 b.2).1).2 _ (mem_inf.1 (mem_inf.1 a.2).1).1) }

/-- `Z(P) ∩ H` inside `Z(P) ∩ K`. -/
def zHK (P : Subgroup G) : Subgroup (zK P K) := (zK P H).subgroupOf (zK P K)

instance (P : Subgroup G) : (zHK K H P).Normal := normal_of_comm _

/-- `(Z(P) ∩ K) / (Z(P) ∩ H)`, as an abelian group. -/
abbrev zQ (P : Subgroup G) : Type := Additive (zK P K ⧸ zHK K H P)

variable [K.Normal] [H.Normal]

lemma conj_mem_zK {P Q : Subgroup G} (hP : IsCentric S P) (hQ : Q ≤ S) {g : G}
    (hg : g ∈ transporter P Q) {L : Subgroup G} [L.Normal] {z : G} (hz : z ∈ zK Q L) :
    g⁻¹ * z * g ∈ zK P L := by
  obtain ⟨⟨hzQ, hzC⟩, hzL⟩ := hz
  have hle : conjSub g P ≤ S := fun y hy => hQ (by
    obtain ⟨x, hx, rfl⟩ := hy; exact hg x hx)
  have h1 : z ∈ centralizer (conjSub g P : Set G) ⊓ S := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_, hQ hzQ⟩
    rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_iff.1 hzC _ (hg x hx)
  rw [hP.2 g hle] at h1
  obtain ⟨h2, h3⟩ := mem_inf.1 h1
  refine ⟨⟨mem_conjSub.1 h2, ?_⟩, ?_⟩
  · refine mem_centralizer_iff.2 fun x hx => ?_
    have := mem_centralizer_iff.1 h3 (g * x * g⁻¹)
      (show g * x * g⁻¹ ∈ conjSub g P from mem_conjSub.2 (by simpa [mul_assoc] using hx))
    calc x * (g⁻¹ * z * g) = g⁻¹ * ((g * x * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * z * g * x := by group
  · simpa using (inferInstance : L.Normal).conj_mem z hzL g⁻¹

/-- Conjugation `z ↦ g⁻¹ z g`, `Z(Q) ∩ L → Z(P) ∩ L`. -/
def conjZ {P Q : Subgroup G} (hP : IsCentric S P) (hQ : Q ≤ S) {g : G} (hg : g ∈ transporter P Q)
    (L : Subgroup G) [L.Normal] : zK Q L →* zK P L where
  toFun z := ⟨g⁻¹ * z * g, conj_mem_zK hP hQ hg z.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp; group

/-- The induced map `(Z(Q) ∩ K)/(Z(Q) ∩ H) → (Z(P) ∩ K)/(Z(P) ∩ H)`. -/
def conjZQ {P Q : Subgroup G} (hP : IsCentric S P) (hQ : Q ≤ S) {g : G}
    (hg : g ∈ transporter P Q) : zK Q K ⧸ zHK K H Q →* zK P K ⧸ zHK K H P :=
  QuotientGroup.map _ _ (conjZ hP hQ hg K) (by
    intro z hz
    exact conj_mem_zK hP hQ hg (L := H) hz)

lemma conjZQ_congr {P Q : Subgroup G} (hP : IsCentric S P) (hQ : IsCentric S Q) {g g' : G}
    (hg : g ∈ transporter P Q) (hg' : g' ∈ transporter P Q)
    (e : ∃ q ∈ Q, ∃ c ∈ centralizer (P : Set G), g' = q * g * c) :
    conjZQ K H hP hQ.1 hg = conjZQ K H hP hQ.1 hg' := by
  obtain ⟨q, hq, c, hc, rfl⟩ := e
  ext z
  change (QuotientGroup.mk (conjZ hP hQ.1 hg K z) : zK P K ⧸ zHK K H P) =
    QuotientGroup.mk (conjZ hP hQ.1 hg' K z)
  congr 1
  apply Subtype.ext
  change g⁻¹ * z * g = (q * g * c)⁻¹ * z * (q * g * c)
  have hzq : (z : G) * q = q * z := (mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 z.2).1).2 q hq).symm
  have hw := conj_mem_zK hP hQ.1 hg (L := K) z.2
  have hcw : c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c :=
    (mem_centralizer_iff.1 hc _ (mem_inf.1 (mem_inf.1 hw).1).1).symm
  calc g⁻¹ * z * g = c⁻¹ * (c * (g⁻¹ * z * g)) := by group
    _ = c⁻¹ * ((g⁻¹ * z * g) * c) := by rw [hcw]
    _ = c⁻¹ * g⁻¹ * (q⁻¹ * (q * z)) * g * c := by group
    _ = c⁻¹ * g⁻¹ * (q⁻¹ * (z * q)) * g * c := by rw [hzq]
    _ = (q * g * c)⁻¹ * z * (q * g * c) := by group

/-- The map of `Z^K/Z^H` on a morphism of the orbit category. -/
def zMap {P Q : OObj p S} (f : P ⟶ Q) :
    AddCommGrpCat.of (zQ K H Q.val) ⟶ AddCommGrpCat.of (zQ K H P.val) :=
  Quotient.lift (fun g : transporter P.val Q.val =>
      AddCommGrpCat.ofHom (MonoidHom.toAdditive (conjZQ K H P.2 Q.2.1 g.2)))
    (by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
      simp only
      rw [conjZQ_congr K H P.2 Q.2 hg hg' e]) f

lemma zMap_mk {P Q : OObj p S} {g : G} (hg : g ∈ transporter P.val Q.val) :
    zMap K H (show P ⟶ Q from omk g hg) =
      AddCommGrpCat.ofHom (MonoidHom.toAdditive (conjZQ K H P.2 Q.2.1 hg)) := rfl

lemma conjZQ_one {P : Subgroup G} (hP : IsCentric S P) :
    conjZQ K H hP hP.1 (one_mem_transporter le_rfl) = MonoidHom.id _ := by
  ext z
  change (QuotientGroup.mk (conjZ hP hP.1 _ K z) : zK P K ⧸ zHK K H P) = QuotientGroup.mk z
  congr 1
  apply Subtype.ext
  change 1⁻¹ * (z : G) * 1 = z
  group

lemma conjZQ_comp {P Q R : Subgroup G} (hP : IsCentric S P) (hQ : IsCentric S Q) (hR : R ≤ S)
    {g h : G} (hg : g ∈ transporter P Q) (hh : h ∈ transporter Q R) :
    conjZQ K H hP hR (mul_mem_transporter hh hg) =
      (conjZQ K H hP hQ.1 hg).comp (conjZQ K H hQ hR hh) := by
  ext z
  change (QuotientGroup.mk (conjZ hP hR _ K z) : zK P K ⧸ zHK K H P) =
    QuotientGroup.mk (conjZ hP hQ.1 hg K (conjZ hQ hR hh K z))
  congr 1
  apply Subtype.ext
  change (h * g)⁻¹ * (z : G) * (h * g) = g⁻¹ * (h⁻¹ * z * h) * g
  group

variable {K H} in
/-- The functor `Z^K_F / Z^H_F : O(F^c)ᵒᵖ → Ab`. -/
def zFunctor (K H : Subgroup G) [K.Normal] [H.Normal] : (OObj p S)ᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj P := AddCommGrpCat.of (zQ K H P.unop.val)
  map f := zMap K H f.unop
  map_id P := by
    change zMap K H (omk 1 _) = _
    rw [zMap_mk, conjZQ_one]
    rfl
  map_comp {P Q R} f g := by
    induction f using Opposite.rec with | op f =>
    induction g using Opposite.rec with | op g =>
    induction f using Quotient.inductionOn with | h a =>
    induction g using Quotient.inductionOn with | h b =>
    change zMap K H (omk ((a : G) * b) (mul_mem_transporter a.2 b.2)) =
      zMap K H (omk (a : G) a.2) ≫ zMap K H (omk (b : G) b.2)
    rw [zMap_mk, zMap_mk, zMap_mk, conjZQ_comp K H R.unop.2 Q.unop.2 P.unop.2.1 b.2 a.2]
    rfl

end Z

end AndersenOliverVentura.Tame
