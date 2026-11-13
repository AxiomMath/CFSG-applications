import CFSGOutside.Baddeley.Definitions
import CFSGOutside.Corpus.GlaubermanZStar

/-!
# The centralizer of the regular minimal normal subgroup is smaller than it

For a special pair `(Γ, G)` with regular nonabelian minimal normal subgroup `M`, Baddeley uses
`|C_G(M)| < |M|` (proof of Lemma 6.2, p. 232, "by the results of the previous section"). The paper derives it from
Lemma 5.1, which rests on Praeger's analysis of quasiprimitive groups ([13, 5.2 and 5.3(a)]) and so on the
classification. We prove it from Glauberman's Z*-theorem instead.

`C = C_G(M)` is semiregular, so `|C| ≤ |M|`. If `|C| = |M|` then `C` is regular, and for each `m ∈ M` some element
of the vertex stabilizer `G_v` induces conjugation by `m` on `M`. Identify the vertices with `M` through
`m ↦ m • v` and let `Y ⊆ M` correspond to the neighbours of `v`. The stabilizer `G_v` acts on `Y` by conjugation,
and 2-arc transitivity makes it transitive on the neighbours other than a fixed one. So an element `y ∈ Y`
commutes with no other element of `Y`: otherwise it would commute with all of `Y`, which generates `M` since `Γ`
is connected, and `Z(M) = 1`. As `y⁻¹ ∈ Y`, `y` is an involution, and since every `G`-conjugate of `y` lies in `Y`,
`y` is isolated in `G`. By Z*, an odd-order normal subgroup `N` of `G` contains every `[g, y]`; then `N ∩ M`
is normal and has odd order, so it is trivial, and `y` is central in `M`, a contradiction.
-/

namespace CFSGOutside.Baddeley

open Subgroup

section GroupLemmas

variable {X : Type*} [Group X]

theorem normal_of_top_le {N : Subgroup X} (h : ⊤ ≤ normalizer (N : Set X)) : N.Normal :=
  ⟨fun n hn g => (mem_normalizer_iff.1 (h (mem_top g)) n).1 hn⟩

theorem top_le_normalizer {N : Subgroup X} (hN : N.Normal) : ⊤ ≤ normalizer (N : Set X) := by
  haveI := hN
  exact (normalizer_eq_top N).ge

/-- A nonabelian minimal normal subgroup has trivial centre. -/
theorem inf_centralizer_eq_bot {M : Subgroup X} (hM : IsMinimalNormalIn M ⊤) (hna : IsNonabelian M) :
    M ⊓ centralizer (M : Set X) = ⊥ := by
  haveI := normal_of_top_le hM.2.1
  rcases hM.2.2.2 _ inf_le_left
      (top_le_normalizer (inferInstance : (M ⊓ centralizer (M : Set X)).Normal)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    have hb' : b ∈ M ⊓ centralizer (M : Set X) := by rw [h]; exact hb
    exact hab (mem_centralizer_iff.1 hb'.2 a ha)

end GroupLemmas

section Action

variable {X V : Type*} [Group X] [MulAction X V] {M : Subgroup X}

theorem eq_of_smul_eq (hreg : IsRegular V M) {a b : X} (ha : a ∈ M) (hb : b ∈ M) {v : V}
    (h : a • v = b • v) : a = b := by
  have h1 : (b⁻¹ * a) • v = v := by rw [mul_smul, h, inv_smul_smul]
  exact (inv_mul_eq_one.1 (hreg.2 _ (mul_mem (inv_mem hb) ha) v h1)).symm

variable [FaithfulSMul X V]

/-- The centralizer of a transitive subgroup is semiregular. -/
theorem centralizer_free (hreg : IsRegular V M) {c : X} (hc : c ∈ centralizer (M : Set X)) {v : V}
    (hv : c • v = v) : c = 1 := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro w
  obtain ⟨m, hm, rfl⟩ := hreg.1 v w
  have hcm : m * c = c * m := mem_centralizer_iff.1 hc m hm
  rw [one_smul, ← mul_smul, ← hcm, mul_smul, hv]

theorem centralizer_smul_injective (hreg : IsRegular V M) (v : V) :
    Function.Injective fun c : centralizer (M : Set X) => (c : X) • v := by
  intro a b h
  have h' : ((b : X)⁻¹ * a) • v = v := by
    rw [mul_smul]
    rw [show (a : X) • v = (b : X) • v from h, inv_smul_smul]
  exact Subtype.ext (inv_mul_eq_one.1 (centralizer_free hreg (mul_mem (inv_mem b.2) a.2) h')).symm

end Action

section Main

variable {X V : Type} [Group X] [Finite X] [MulAction X V] [FaithfulSMul X V] [Finite V]
  {Γ : SimpleGraph V} {M : Subgroup X}

theorem card_eq_card_of_isRegular (hreg : IsRegular V M) (v : V) : Nat.card M = Nat.card V := by
  refine Nat.card_eq_of_bijective (fun m : M => (m : X) • v) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (eq_of_smul_eq hreg a.2 b.2 h)
  · intro w
    obtain ⟨m, hm, h⟩ := hreg.1 v w
    exact ⟨⟨m, hm⟩, h⟩

/-- **`|C_G(M)| < |M|`** for a special pair, here with `G = X` acting faithfully on the vertices. -/
theorem card_centralizer_lt [CFSGOutside.Corpus.GlaubermanZStar]
    (hAut : IsAutGroup Γ (⊤ : Subgroup X)) (hconn : Γ.Connected)
    (h2 : IsTwoArcTransitive Γ (⊤ : Subgroup X)) (hM : IsMinimalNormalIn M ⊤)
    (hMna : IsNonabelian M) (hreg : IsRegular V M) :
    Nat.card (centralizer (M : Set X)) < Nat.card M := by
  obtain ⟨v₀⟩ := hconn.nonempty
  have hMV := card_eq_card_of_isRegular hreg v₀
  have hCV : Nat.card (centralizer (M : Set X)) ≤ Nat.card V :=
    Nat.card_le_card_of_injective _ (centralizer_smul_injective hreg v₀)
  refine lt_of_le_of_ne (by omega) fun hCM => ?_
  have hadj : ∀ g : X, ∀ u v : V, Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v := fun g => hAut g trivial
  have hMn : M.Normal := normal_of_top_le hM.2.1
  have hZ := inf_centralizer_eq_bot hM hMna
  -- `C_G(M)` is regular.
  have hCsurj : ∀ w : V, ∃ c ∈ centralizer (M : Set X), c • v₀ = w := by
    have hbij := (centralizer_smul_injective hreg v₀).bijective_of_nat_card_le (by omega)
    intro w
    obtain ⟨c, hc⟩ := hbij.2 w
    exact ⟨c, c.2, hc⟩
  -- The vertex stabilizer contains a copy of `Inn(M)`.
  have hdiag : ∀ m ∈ M, ∃ g : X, g • v₀ = v₀ ∧ ∀ x ∈ M, g * x * g⁻¹ = m * x * m⁻¹ := by
    intro m _
    obtain ⟨c, hc, hcv⟩ := hCsurj (m⁻¹ • v₀)
    refine ⟨m * c, by rw [mul_smul, hcv, smul_inv_smul], fun x hx => ?_⟩
    have hcx : x * c = c * x := mem_centralizer_iff.1 hc x hx
    calc m * c * x * (m * c)⁻¹ = m * (c * x) * c⁻¹ * m⁻¹ := by group
      _ = m * (x * c) * c⁻¹ * m⁻¹ := by rw [hcx]
      _ = m * x * m⁻¹ := by group
  -- The neighbours of `v₀`, as elements of `M`.
  set Ys : Set X := {x | x ∈ M ∧ Γ.Adj v₀ (x • v₀)} with hYs
  have hfix : ∀ g : X, g • v₀ = v₀ → ∀ x : X, (g * x * g⁻¹) • v₀ = g • x • v₀ := by
    intro g hg x
    rw [mul_smul, mul_smul, show g⁻¹ • v₀ = v₀ by rw [inv_smul_eq_iff, hg]]
  have hstab : ∀ g : X, g • v₀ = v₀ → ∀ x ∈ Ys, g * x * g⁻¹ ∈ Ys := by
    rintro g hg x ⟨hxM, hx⟩
    refine ⟨hMn.conj_mem x hxM g, ?_⟩
    rw [hfix g hg x]
    have := (hadj g v₀ (x • v₀)).2 hx
    rwa [hg] at this
  have hconjY : ∀ a : X, ∀ x ∈ Ys, a * x * a⁻¹ ∈ Ys := by
    intro a x hx
    obtain ⟨m, hm, hmv⟩ := hreg.1 v₀ (a • v₀)
    obtain ⟨g, hgv, hg⟩ := hdiag m hm
    have hs : (m⁻¹ * a) • v₀ = v₀ := by rw [mul_smul, ← hmv, inv_smul_smul]
    have h1 := hstab _ hs x hx
    have h2' := hstab g hgv _ h1
    rw [hg _ h1.1] at h2'
    convert h2' using 1
    group
  have hy1 : ∀ y ∈ Ys, y ≠ 1 := by
    rintro y ⟨-, hy⟩ rfl
    rw [one_smul] at hy
    exact hy.ne rfl
  -- Two commuting distinct neighbours force a neighbour to commute with all neighbours.
  have hkey : ∀ y ∈ Ys, ∀ z ∈ Ys, y * z = z * y → z ≠ y → ∀ w ∈ Ys, y * w = w * y := by
    rintro y ⟨hyM, hy⟩ z ⟨hzM, hz⟩ hyz hzy w ⟨hwM, hw⟩
    by_cases hwy : w = y
    · rw [hwy]
    have hne : ∀ {u : X}, u ∈ M → u ≠ y → u • v₀ ≠ y • v₀ := fun hu huy h =>
      huy (eq_of_smul_eq hreg hu hyM h)
    obtain ⟨g, -, hg0, hg1, hg2⟩ := h2 (z • v₀) v₀ (y • v₀) (w • v₀) v₀ (y • v₀) hz.symm hy
      (hne hzM hzy) hw.symm hy (hne hwM hwy)
    have hgz : g * z * g⁻¹ = w :=
      eq_of_smul_eq hreg (hMn.conj_mem z hzM g) hwM (by rw [hfix g hg1, hg0])
    have hgy : g * y * g⁻¹ = y :=
      eq_of_smul_eq hreg (hMn.conj_mem y hyM g) hyM (by rw [hfix g hg1, hg2])
    calc y * w = g * y * g⁻¹ * (g * z * g⁻¹) := by rw [hgy, hgz]
      _ = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hyz]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group
      _ = w * y := by rw [hgy, hgz]
  -- The neighbours generate `M`, since `Γ` is connected.
  have hYM : closure Ys ≤ M := (closure_le M).2 fun x hx => hx.1
  have hgen : M ≤ closure Ys := by
    have hstep : ∀ u w : V, (∃ m ∈ closure Ys, m • v₀ = u) → Γ.Adj u w →
        ∃ m ∈ closure Ys, m • v₀ = w := by
      rintro u w ⟨m, hm, rfl⟩ huw
      obtain ⟨y, hyM, hyv⟩ := hreg.1 v₀ (m⁻¹ • w)
      refine ⟨m * y, mul_mem hm (subset_closure ⟨hyM, ?_⟩), by rw [mul_smul, hyv, smul_inv_smul]⟩
      rw [hyv]
      have := (hadj m⁻¹ (m • v₀) w).2 huw
      rwa [inv_smul_smul] at this
    have hwalk : ∀ (u w : V) (_ : Γ.Walk u w), (∃ m ∈ closure Ys, m • v₀ = u) →
        ∃ m ∈ closure Ys, m • v₀ = w := by
      intro u w p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun hu => ih (hstep _ _ hu h)
    intro m hm
    obtain ⟨p⟩ := hconn.preconnected v₀ (m • v₀)
    obtain ⟨m', hm', hmv⟩ := hwalk _ _ p ⟨1, one_mem _, one_smul _ _⟩
    rw [← eq_of_smul_eq hreg (hYM hm') hm hmv]
    exact hm'
  -- So a neighbour commutes with no other neighbour.
  have hiso : ∀ y ∈ Ys, ∀ z ∈ Ys, y * z = z * y → z = y := by
    intro y hy z hz hyz
    by_contra hzy
    have hall := hkey y hy z hz hyz hzy
    have hyc : y ∈ centralizer (M : Set X) := by
      have h1 : y ∈ centralizer Ys := mem_centralizer_iff.2 fun w hw => (hall w hw).symm
      rw [← centralizer_closure] at h1
      exact centralizer_le (fun x hx => hgen hx) h1
    have h3 : y ∈ M ⊓ centralizer (M : Set X) := ⟨hy.1, hyc⟩
    rw [hZ, mem_bot] at h3
    exact hy1 y hy h3
  -- A neighbour exists.
  obtain ⟨a, haM, b, hbM, hab⟩ := hMna
  have hnt : ∃ w : V, w ≠ v₀ := by
    by_contra h
    push Not at h
    apply hab
    rw [hreg.2 a haM v₀ (h _), hreg.2 b hbM v₀ (h _)]
  obtain ⟨w, hw⟩ := hnt
  obtain ⟨p⟩ := hconn.preconnected v₀ w
  obtain ⟨u, hu⟩ : ∃ u, Γ.Adj v₀ u := by
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, h⟩
  obtain ⟨y, hyM, rfl⟩ := hreg.1 v₀ u
  have hyY : y ∈ Ys := ⟨hyM, hu⟩
  -- It is an involution, isolated in `X`.
  have hyinv : y⁻¹ ∈ Ys := by
    refine ⟨inv_mem hyM, ?_⟩
    have := (hadj y⁻¹ v₀ (y • v₀)).2 hu
    rw [inv_smul_smul] at this
    exact this.symm
  have hyy : y⁻¹ = y := hiso y hyY y⁻¹ hyinv (by group)
  have hy2 : y * y = 1 := by
    have := mul_inv_cancel y
    rwa [hyy] at this
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSGOutside.Corpus.GlaubermanZStar.glauberman_zStar X y (hy1 y hyY) hy2
    (fun g hg => hiso y hyY _ (hconjY g y hyY) hg.symm)
  -- `N ∩ M` is normal of odd order, hence trivial.
  have hNM : N ⊓ M = ⊥ := by
    haveI := hNn
    rcases hM.2.2.2 (N ⊓ M) inf_le_right (top_le_normalizer inferInstance) with h | h
    · exact h
    · exfalso
      have hle : M ≤ N := by rw [← h]; exact inf_le_left
      have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) (hy1 y hyY)
      have h2M : 2 ∣ Nat.card M := by
        have := Subgroup.orderOf_dvd_natCard M hyM
        rwa [hord] at this
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 (h2M.trans (card_dvd_of_le hle)))
  have hyc : y ∈ centralizer (M : Set X) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hmem : a * y * a⁻¹ * y⁻¹ ∈ N ⊓ M :=
      mem_inf.2 ⟨hN a, M.mul_mem (hMn.conj_mem y hyM a) (M.inv_mem hyM)⟩
    rw [hNM, mem_bot] at hmem
    have h1 : a * y * a⁻¹ = y := mul_inv_eq_one.1 hmem
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h1]
  have h3 : y ∈ M ⊓ centralizer (M : Set X) := ⟨hyM, hyc⟩
  rw [hZ, mem_bot] at h3
  exact hy1 y hyY h3

end Main

end CFSGOutside.Baddeley
