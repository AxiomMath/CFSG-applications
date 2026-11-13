import CFSGOutside.KhukhroShumyatskyFixedPointLength.Definitions
import CFSGOutside.Common.UpperNonsolubleSeries

/-!
# Khukhro–Shumyatsky, fixed points: coprime action

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. Coprime action is not in the corpus, so the little that is needed is proved here: a
`φ`-invariant coset of a `φ`-invariant subgroup of order prime to the order of `φ` contains a fixed point
(`exists_fixed_mul`), whence `G = C_G(φ)[G, φ]`, and the automorphisms induced on quotients and restricted to
invariant subgroups.
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section Coprime

variable {G : Type*} [Group G] [Finite G]


lemma commSub_normal (φ : MulAut G) : (commSub φ).Normal := by
  refine ⟨fun x hx h => ?_⟩
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    have e : h * (g⁻¹ * φ g) * h⁻¹ =
        ((g * h⁻¹)⁻¹ * φ (g * h⁻¹)) * (h⁻¹⁻¹ * φ h⁻¹)⁻¹ := by
      simp [map_mul, map_inv, mul_assoc]
    rw [e]
    exact mul_mem (inv_mul_mem_commSub φ _) (inv_mem (inv_mul_mem_commSub φ _))
  | one => simp
  | mul a b _ _ ha hb =>
    have : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

/-- A subgroup is `φ`-invariant. -/
def IsInv (φ : MulAut G) (H : Subgroup G) : Prop := H.map φ.toMonoidHom = H

lemma IsInv.mem {φ : MulAut G} {H : Subgroup G} (h : IsInv φ H) {x : G} (hx : x ∈ H) :
    φ x ∈ H := by
  rw [← h]; exact ⟨x, hx, rfl⟩

lemma isInv_of_forall {φ : MulAut G} {H : Subgroup G} (h : ∀ x ∈ H, φ x ∈ H) : IsInv φ H := by
  have hle : H.map φ.toMonoidHom ≤ H := by rintro _ ⟨x, hx, rfl⟩; exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective φ.injective]

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Coprime action, the basic counting step.**  If `φ^p = 1`, `p ∤ |G|`, `N` is `φ`-invariant
and the coset `yN` is `φ`-invariant, then `yN` contains a fixed point of `φ`. -/
lemma exists_fixed_mul {φ : MulAut G} (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)
    {N : Subgroup G} (hN : ∀ n ∈ N, φ n ∈ N) {y : G} (hy : y⁻¹ * φ y ∈ N) :
    ∃ n ∈ N, φ (y * n) = y * n := by
  classical
  haveI := Fintype.ofFinite N
  let f : Function.End N := fun n => ⟨y⁻¹ * φ (y * n), by
    rw [map_mul, ← mul_assoc]; exact mul_mem hy (hN _ n.2)⟩
  have hfk : ∀ k : ℕ, ∀ n : N, ((f ^ k) n : G) = y⁻¹ * (φ ^ k) (y * n) := by
    intro k
    induction k with
    | zero => intro n; change (n : G) = _; simp
    | succ k ih =>
      intro n
      have : (f ^ (k + 1)) n = f ((f ^ k) n) := by rw [pow_succ']; rfl
      rw [this]
      change y⁻¹ * φ (y * ((f ^ k) n : G)) = _
      rw [ih, mul_inv_cancel_left, pow_succ', MulAut.mul_apply]
  have hf : f ^ p ^ 1 = 1 := by
    funext n
    apply Subtype.ext
    change ((f ^ p ^ 1) n : G) = (n : G)
    rw [pow_one, hfk, hφ]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  by_contra hno
  push Not at hno
  have hempty : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨n, hn⟩ => hno n n.2 ?_⟩
    have h1 : f n = n := hn
    have h2 : y⁻¹ * φ (y * n) = n := congrArg Subtype.val h1
    exact (inv_mul_eq_iff_eq_mul).1 h2
  rw [hempty, ← Nat.card_eq_fintype_card] at hmod
  have hdvd : p ∣ Nat.card N := (Nat.modEq_zero_iff_dvd).1 hmod
  exact hpG (hdvd.trans (Subgroup.card_subgroup_dvd_card N))

variable {φ : MulAut G} (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)
include hφ hpG

/-- `G = C_G(φ) [G, φ]`. -/
lemma exists_fixed_mul_commSub (g : G) :
    ∃ c ∈ fixedSub φ, ∃ n ∈ commSub φ, g = c * n := by
  have hN : ∀ n ∈ commSub φ, φ n ∈ commSub φ := by
    intro n hn
    induction hn using closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [map_mul, map_inv]; exact inv_mul_mem_commSub φ _
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul hφ hpG hN (inv_mul_mem_commSub φ g)
  exact ⟨g * n, hfix, n⁻¹, inv_mem hn, by group⟩

end Coprime

section Induced

variable {G : Type*} [Group G]

/-- The automorphism of `G/N` induced by `φ`, for `φ`-invariant normal `N`. -/
noncomputable def quotAut (φ : MulAut G) (N : Subgroup G) [N.Normal] (h : IsInv φ N) :
    MulAut (G ⧸ N) :=
  QuotientGroup.congr N N φ h

lemma quotAut_mk (φ : MulAut G) (N : Subgroup G) [N.Normal] (h : IsInv φ N) (x : G) :
    quotAut φ N h (x : G ⧸ N) = (φ x : G ⧸ N) := rfl

lemma quotAut_pow (φ : MulAut G) (N : Subgroup G) [N.Normal] (h : IsInv φ N) (k : ℕ)
    (x : G) : (quotAut φ N h ^ k) (x : G ⧸ N) = ((φ ^ k) x : G ⧸ N) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, quotAut_mk, pow_succ', MulAut.mul_apply]

lemma quotAut_pow_eq_one {p : ℕ} {φ : MulAut G} (hφ : φ ^ p = 1) (N : Subgroup G) [N.Normal]
    (h : IsInv φ N) : quotAut φ N h ^ p = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotAut_pow, hφ]; rfl

/-- The restriction of `φ` to an invariant subgroup. -/
noncomputable def restrictAut (φ : MulAut G) (H : Subgroup G) (h : IsInv φ H) : MulAut H :=
  (φ.subgroupMap H).trans (MulEquiv.subgroupCongr h)

lemma restrictAut_apply (φ : MulAut G) (H : Subgroup G) (h : IsInv φ H) (x : H) :
    (restrictAut φ H h x : G) = φ x := rfl

lemma restrictAut_pow_apply (φ : MulAut G) (H : Subgroup G) (h : IsInv φ H) (k : ℕ) (x : H) :
    ((restrictAut φ H h ^ k) x : G) = (φ ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, restrictAut_apply, ih, pow_succ', MulAut.mul_apply]

lemma restrictAut_pow_eq_one {p : ℕ} {φ : MulAut G} (hφ : φ ^ p = 1) (H : Subgroup G)
    (h : IsInv φ H) : restrictAut φ H h ^ p = 1 := by
  ext x
  rw [restrictAut_pow_apply, hφ]; rfl

end Induced

end CFSGOutside.KhukhroShumyatskyFixedPointLength
