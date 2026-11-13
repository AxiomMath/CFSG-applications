import CFSGOutside.KhukhroShumyatskyFactorizedLength.GeneralizedFittingHeight
import CFSGOutside.Corpus.BurnsidePQ

/-!
# Factorizations `G = AB` with coprime orders

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780.

Let `Y` be a finite group with `F(Y) = 1` and `Y = AB` with `gcd(|A|, |B|) = 1`. Every component `S` of `Y`
factorizes as `S = (S ∩ A)(S ∩ B)` with `|S| = |S ∩ A||S ∩ B|` (`component_decomp`, `card_component`, from
Lemma 2.3 `mem_of_mul_mem`). Let `K_A` (`kernelOf (compsA A)`) be the kernel of the action of `Y` on the
components `S` for which `S ∩ A` is not of prime-power order. It is normal, because the order of `S ∩ A` is
invariant under conjugation (`card_map_conj_inf`).

* `generalizedFitting_le_kernelOf` is **Lemma 3.3**: `F*(A) ≤ K_A`. It is proved directly, avoiding the paper's
  Lemma 2.2: `O_p(A)` normalizes `S` by a commutator and element-order argument in two distinct commuting
  components, and every component of `A` either lies in `E(Y)` or centralizes `E(Y) ∩ A ⊇ S ∩ A ≠ 1`.
* `kernelOf_compsA_inf` is `K_A ∩ K_B = K`, the kernel of the action on all components, by Burnside's
  `p^a q^b` theorem (the class `CFSGOutside.Corpus.BurnsidePQ`).
-/

namespace CFSGOutside.KhukhroShumyatskyFactorizedLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores CFSGOutside.NonsolubleLength
open scoped commutatorElement

section Elementary

variable {Y : Type*} [Group Y] [Finite Y]

lemma IsFactorization.symm {A B : Subgroup Y} (h : IsFactorization A B) : IsFactorization B A := by
  intro g
  obtain ⟨a, ha, b, hb, hab⟩ := h g⁻¹
  exact ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, by rw [← mul_inv_rev, ← hab, inv_inv]⟩

lemma coprime_orderOf {A B : Subgroup Y} (hcop : (Nat.card A).Coprime (Nat.card B)) {a b : Y}
    (ha : a ∈ A) (hb : b ∈ B) : (orderOf a).Coprime (orderOf b) :=
  Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard A ha)
    (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard B hb) hcop)

lemma inf_eq_bot_of_coprime {A B : Subgroup Y} (hcop : (Nat.card A).Coprime (Nat.card B)) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have := coprime_orderOf hcop hx.1 hx.2
  rw [Nat.coprime_self, orderOf_eq_one_iff] at this
  rw [mem_bot]; exact this

/-- **Lemma 2.3**: if `a, b` have coprime orders, normalize `N`, and `ab ∈ N`, then `a, b ∈ N`. -/
lemma mem_of_mul_mem {N : Subgroup Y} {a b : Y} (ha : a ∈ normalizer (N : Set Y))
    (hb : b ∈ normalizer (N : Set Y)) (hcop : (orderOf a).Coprime (orderOf b))
    (h : a * b ∈ N) : a ∈ N ∧ b ∈ N := by
  have key : ∀ k : ℕ, a ^ k * b ^ k ∈ N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbk : (b ^ k)⁻¹ ∈ normalizer (N : Set Y) := inv_mem (pow_mem hb k)
      have h1 : (b ^ k)⁻¹ * (a * b) * ((b ^ k)⁻¹)⁻¹ ∈ N :=
        (mem_normalizer_iff.1 hbk _).1 h
      have : a ^ (k + 1) * b ^ (k + 1) = (a ^ k * b ^ k) * ((b ^ k)⁻¹ * (a * b) * ((b ^ k)⁻¹)⁻¹) := by
        rw [inv_inv, pow_succ, pow_succ']
        group
      rw [this]
      exact mul_mem ih h1
  have haN : a ∈ N := by
    have h1 := key (orderOf b)
    rw [pow_orderOf_eq_one, mul_one] at h1
    exact mem_of_pow_mem_of_coprime hcop (by rw [pow_orderOf_eq_one]; exact one_mem _) h1
  refine ⟨haN, ?_⟩
  have := mul_mem (inv_mem haN) h
  rwa [inv_mul_cancel_left] at this

lemma mem_normalizer_of_normal {N : Subgroup Y} [hN : N.Normal] (g : Y) :
    g ∈ normalizer (N : Set Y) :=
  mem_normalizer_iff.2 fun h => ⟨fun hh => hN.conj_mem h hh g, fun hh => by
    simpa [mul_assoc] using hN.conj_mem _ hh g⁻¹⟩

end Elementary

section Components

variable {Y : Type} [Group Y] [Finite Y] (hF : fittingSubgroup Y = ⊥)
  {A B : Subgroup Y} (hAB : IsFactorization A B) (hcop : (Nat.card A).Coprime (Nat.card B))

/-- `S` has prime-power order (a `p`-group for some prime `p`). -/
def IsPPow (S : Subgroup Y) : Prop := ∃ p k : ℕ, p.Prime ∧ Nat.card S = p ^ k

include hAB hcop

/-- Every element of a component factorizes inside the component. -/
lemma component_decomp {S : Subgroup Y} (hS : IsComponent S) {s : Y} (hs : s ∈ S) :
    ∃ a ∈ S ⊓ A, ∃ b ∈ S ⊓ B, s = a * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hAB s
  have hc := coprime_orderOf hcop ha hb
  have hV := mem_of_mul_mem (N := layer Y) (mem_normalizer_of_normal a)
    (mem_normalizer_of_normal b) hc (component_le_layer hS hs)
  have hS' := mem_of_mul_mem (N := S) (layer_le_normalizer hS hV.1) (layer_le_normalizer hS hV.2)
    hc hs
  exact ⟨a, ⟨hS'.1, ha⟩, b, ⟨hS'.2, hb⟩, rfl⟩

lemma card_component {S : Subgroup Y} (hS : IsComponent S) :
    Nat.card (S ⊓ A : Subgroup Y) * Nat.card (S ⊓ B : Subgroup Y) = Nat.card S := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨(p.1 : Y) * p.2, S.mul_mem (mem_inf.1 p.1.2).1 (mem_inf.1 p.2.2).1⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have hx : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem (mem_inf.1 ha').2) (mem_inf.1 ha).2, by
      have : a'⁻¹ * a = b' * b⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      rw [this]; exact B.mul_mem (mem_inf.1 hb').2 (B.inv_mem (mem_inf.1 hb).2)⟩
    rw [inf_eq_bot_of_coprime hcop, mem_bot, inv_mul_eq_one] at hx
    subst hx
    have : b = b' := mul_left_cancel h1
    subst this
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := component_decomp hAB hcop hS hs
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

omit hAB hcop in
lemma card_map_conj_inf_of_mem {S A : Subgroup Y} {c : Y} (hc : c ∈ A) :
    Nat.card (S.map (MulAut.conj c).toMonoidHom ⊓ A : Subgroup Y) = Nat.card (S ⊓ A : Subgroup Y) := by
  have hA : A.map (MulAut.conj c).toMonoidHom = A := map_conj_eq_of_mem_normalizer (le_normalizer hc)
  rw [show S.map (MulAut.conj c).toMonoidHom ⊓ A = (S ⊓ A).map (MulAut.conj c).toMonoidHom by
    rw [map_inf_eq (f := (MulAut.conj c).toMonoidHom) _ _ (MulAut.conj c).injective, hA]]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

lemma card_map_conj_inf {S : Subgroup Y} (hS : IsComponent S) (g : Y) :
    Nat.card (S.map (MulAut.conj g).toMonoidHom ⊓ A : Subgroup Y) =
      Nat.card (S ⊓ A : Subgroup Y) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hAB g
  rw [← conj_comp_conj, ← map_map, card_map_conj_inf_of_mem ha]
  have hS' : IsComponent (S.map (MulAut.conj b).toMonoidHom) := isComponent_conj hS b
  have h1 := card_component hAB hcop hS'
  have h2 := card_component hAB hcop hS
  rw [card_map_conj_inf_of_mem hb, Subgroup.card_map_of_injective (MulAut.conj b).injective,
    ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

omit hAB hcop in
variable (A) in
/-- The components `S` such that `S ∩ A` is not of prime-power order. -/
def compsA : Set (Subgroup Y) := {S | IsComponent S ∧ ¬ IsPPow (S ⊓ A)}

lemma compsA_conj : ∀ S ∈ compsA A, ∀ g : Y, S.map (MulAut.conj g).toMonoidHom ∈ compsA A := by
  rintro S ⟨hS, hp⟩ g
  refine ⟨isComponent_conj hS g, fun h => hp ?_⟩
  rwa [IsPPow, card_map_conj_inf hAB hcop hS g] at h

lemma kernelOf_compsA_normal : (kernelOf (compsA A)).Normal :=
  kernelOf_normal (compsA_conj hAB hcop)

omit hAB hcop in
include hF in
/-- **Lemma 3.3**: `F*(A)` normalizes every component `S` with `S ∩ A` not of prime-power
order. -/
lemma generalizedFitting_le_kernelOf :
    (generalizedFitting A).map A.subtype ≤ kernelOf (compsA A) := by
  intro x hx
  refine mem_kernelOf.2 fun S hS => ?_
  revert x
  rw [← SetLike.le_def, generalizedFitting.eq_sup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · refine (Subgroup.map_mono (fittingSubgroup_le_iSup_pCore A)).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hp => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyN
    apply hS.2
    have hpg : IsPGroup p (S ⊓ A : Subgroup Y) := by
      rintro ⟨t, ht⟩
      let t' : A := ⟨t, ht.2⟩
      have hc : t'⁻¹ * y⁻¹ * t' * y ∈ pCore p A := by
        have h1 : t'⁻¹ * y⁻¹ * t' ∈ pCore p A := by
          have := (pCore_normal (p := p) (G := A)).conj_mem _ (inv_mem hy) t'⁻¹
          simpa using this
        exact mul_mem h1 hy
      obtain ⟨k, hk⟩ := pCore_isPGroup (p := p) (G := A) ⟨_, hc⟩
      have hk' : ((t : Y)⁻¹ * ((y : Y)⁻¹ * t * y)) ^ (p ^ k) = 1 := by
        have := congrArg (fun z : pCore p A => ((z : A) : Y)) hk
        simpa [t', mul_assoc] using this
      set S' := S.map (MulAut.conj (y : Y)⁻¹).toMonoidHom
      have hS' : IsComponent S' := isComponent_conj hS.1 _
      have hne : S ≠ S' := by
        intro heq
        apply hyN
        have : ((y : Y))⁻¹ ∈ normalizer (S : Set Y) := mem_normalizer_of_map_conj_eq heq.symm
        simpa using inv_mem this
      have hu : (y : Y)⁻¹ * t * y ∈ S' := by
        rw [mem_map_conj_iff]; simpa [mul_assoc] using ht.1
      have hcomm : Commute ((t : Y)⁻¹) ((y : Y)⁻¹ * t * y) :=
        component_commute hS.1 hS' hne _ (inv_mem ht.1) _ hu
      rw [hcomm.mul_pow] at hk'
      have h3 : ((t : Y)⁻¹) ^ (p ^ k) ∈ S ⊓ S' := by
        refine ⟨S.pow_mem (S.inv_mem (mem_inf.1 ht).1) _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hk']
        exact S'.inv_mem (S'.pow_mem hu _)
      rw [component_inf_eq_bot hF hS.1 hS' hne, mem_bot, inv_pow, inv_eq_one] at h3
      exact ⟨k, Subtype.ext h3⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    exact ⟨p, n, hp, hn⟩
  · rw [map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rcases component_normal_subgroup hL
        (inferInstance : ((layer Y).subgroupOf A).Normal) with h | h
    · intro x hx
      exact layer_le_normalizer hS.1 (h hx)
    · have hnt : (S ⊓ A : Subgroup Y) ≠ ⊥ := by
        intro hbot
        apply hS.2
        exact ⟨2, 0, Nat.prime_two, by rw [hbot]; simp⟩
      obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hnt)
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      intro x hx
      have hzN : (⟨z, hz.2⟩ : A) ∈ (layer Y).subgroupOf A :=
        mem_subgroupOf.2 (component_le_layer hS.1 hz.1)
      have hcx : ⁅x, (⟨z, hz.2⟩ : A)⁆ ∈ ⁅L, (layer Y).subgroupOf A⁆ :=
        commutator_mem_commutator hx hzN
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcx
      have hcx' : (x : Y) * z = z * x := congrArg Subtype.val hcx
      exact mem_normalizer_of_commute (𝒮 := components Y) (fun S hS g => isComponent_conj hS g)
        (fun S hS S' hS' hne => component_inf_eq_bot hF hS hS' hne) hS.1 hz.1 hz1' hcx'

include hF in
/-- `K_A ∩ K_B = K`, by Burnside's `p^a q^b` theorem. -/
lemma kernelOf_compsA_inf [BurnsidePQ.{0}] : kernelOf (compsA A) ⊓ kernelOf (compsA B) = kernelOf (components Y) := by
  refine le_antisymm (fun x hx => mem_kernelOf.2 fun S hS => ?_)
    (le_inf (kernelOf_anti fun S hS => hS.1) (kernelOf_anti fun S hS => hS.1))
  by_cases hA' : IsPPow (S ⊓ A)
  · by_cases hB' : IsPPow (S ⊓ B)
    · exfalso
      obtain ⟨p, a, hp, ha⟩ := hA'
      obtain ⟨q, b, hq, hb⟩ := hB'
      apply (factorFamily_components hF).nonsol S hS
      have hcard : Nat.card S = p ^ a * q ^ b := by rw [← card_component hAB hcop hS, ha, hb]
      by_cases hpq : p = q
      · subst hpq
        haveI : Fact p.Prime := ⟨hp⟩
        rw [← pow_add] at hcard
        haveI := (IsPGroup.of_card hcard : IsPGroup p S).isNilpotent
        infer_instance
      · haveI := Fintype.ofFinite S
        exact BurnsidePQ.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
          (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    · exact mem_kernelOf.1 hx.2 S ⟨hS, hB'⟩
  · exact mem_kernelOf.1 hx.1 S ⟨hS, hA'⟩

end Components

end CFSGOutside.KhukhroShumyatskyFactorizedLength
