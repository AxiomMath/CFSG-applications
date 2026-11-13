import Mathlib
import CFSGOutside.WittDesigns.AutS5824.Main
import CFSGOutside.Corpus.IsMultiplyPretransitiveM22
import CFSGOutside.Corpus.M22LeHexadAut
import CFSGOutside.Corpus.M22Simple
import CFSGOutside.WittDesigns.M24FiveTransitive.M22Index

/-!
# The automorphism group of `S(5,8,24)` is 5-transitive

For a normalized `S(5,8,24)` the automorphism group `G` is transitive on the 276 pairs of points. An
involution of `G` swaps two points, so `G` is 2-transitive. The pointwise stabilizer of the two extra points
maps injectively into the automorphisms of the hexads and contains the image of `M22`: the elements of `M22`
that extend to automorphisms swapping the extra points form a complement of an index two subgroup, which is
trivial as `M22` is simple. Since `M22` is 3-transitive on the 22 ordinary points, `G` is 5-transitive.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.M24Five

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22 CFSGOutside.WittDesigns.Witt5824 CFSGOutside.WittDesigns.Aut5824

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple]
attribute [local instance] Classical.propDecidable

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple] in
noncomputable def fixExt (𝒮 : Finset (Finset Pt)) : Subgroup M22 where
  carrier := {a | ∃ g ∈ blockAut 𝒮, g (Sum.inr false) = Sum.inr false ∧
    ∀ i, g (Sum.inl i) = Sum.inl (a.1 i)}
  mul_mem' := by
    rintro a b ⟨g, hg, hgF, hga⟩ ⟨h, hh, hhF, hhb⟩
    refine ⟨g * h, mul_mem hg hh, ?_, fun i => ?_⟩
    · simp [Equiv.Perm.mul_apply, hhF, hgF]
    · simp [Equiv.Perm.mul_apply, hhb, hga]
  one_mem' := ⟨1, one_mem _, rfl, fun i => rfl⟩
  inv_mem' := by
    rintro a ⟨g, hg, hgF, hga⟩
    refine ⟨g⁻¹, inv_mem hg, ?_, fun i => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hgF]
    · rw [Equiv.Perm.inv_eq_iff_eq, hga]
      simp [Equiv.Perm.mul_apply]

theorem mem_P0_of_stab {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) {x : Pt} (hx : x ∈ P0) :
    g x ∈ P0 := by
  rw [← hg]
  exact Finset.mem_map_of_mem g.toEmbedding hx

theorem mem_P0_of_pair {s : Finset Pt} {g : Equiv.Perm Pt} (hg : s.map g.toEmbedding = P0) {x : Pt}
    (hx : x ∈ s) : g x ∈ P0 := by
  rw [← hg]
  exact Finset.mem_map_of_mem g.toEmbedding hx

theorem eq_F_or_T {x : Pt} (hx : x ∈ P0) : x = Sum.inr false ∨ x = Sum.inr true := by
  simpa [P0] using hx

theorem swap_of_not_mem {𝒮 : Finset (Finset Pt)} {b : M22} (hb : b ∉ fixExt 𝒮) {g : Equiv.Perm Pt}
    (hg : P0.map g.toEmbedding = P0) (hgb : ∀ i, g (Sum.inl i) = Sum.inl (b.1 i))
    (hgG : g ∈ blockAut 𝒮) :
    g (Sum.inr false) = Sum.inr true ∧ g (Sum.inr true) = Sum.inr false := by
  have hF := eq_F_or_T (mem_P0_of_stab hg (x := Sum.inr false) (by simp [P0]))
  have hT := eq_F_or_T (mem_P0_of_stab hg (x := Sum.inr true) (by simp [P0]))
  have hne : g (Sum.inr false) ≠ g (Sum.inr true) := fun h => by simpa using g.injective h
  rcases hF with hF | hF
  · exact absurd ⟨g, hgG, hF, hgb⟩ hb
  · rcases hT with hT | hT
    · exact ⟨hF, hT⟩
    · exact absurd (hF.trans hT.symm) hne

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple] in
def toFin : Pt → Fin 22 := Sum.elim id (fun _ => 0)

theorem eq_inl_toFin {x : Pt} (h1 : x ≠ Sum.inr false) (h2 : x ≠ Sum.inr true) :
    x = Sum.inl (toFin x) := by
  rcases x with i | b
  · rfl
  · cases b <;> simp_all

theorem rest_inl {h : Equiv.Perm Pt} {F : Fin 5 → Pt} (hF : Function.Injective F)
    (h0 : h (F 0) = Sum.inr false) (h1 : h (F 1) = Sum.inr true) (j : Fin 3) :
    h (F j.succ.succ) = Sum.inl (toFin (h (F j.succ.succ))) := by
  apply eq_inl_toFin
  · rw [← h0]
    intro e
    exact Fin.succ_ne_zero _ (hF (h.injective e))
  · rw [← h1]
    intro e
    exact Fin.succ_succ_ne_one j (hF (h.injective e))

section Main

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem fixExt_eq_top : fixExt 𝒮 = ⊤ := by
  refine m22_eq_top_of_mul _ fun a b ha hb => ?_
  obtain ⟨gb, hgbG, hgbP, hgb⟩ := exists_ext hN (M22LeHexadAut.M22_le_hexadAut b.2)
  obtain ⟨ga, hgaG, hgaP, hga⟩ := exists_ext hN (M22LeHexadAut.M22_le_hexadAut a.2)
  obtain ⟨hbF, hbT⟩ := swap_of_not_mem hb hgbP hgb hgbG
  obtain ⟨haF, haT⟩ := swap_of_not_mem ha hgaP hga hgaG
  refine ⟨gb * ga, mul_mem hgbG hgaG, ?_, fun i => ?_⟩
  · simp [Equiv.Perm.mul_apply, haF, hbT]
  · simp [Equiv.Perm.mul_apply, hga, hgb]

theorem exists_fix_three {u v : Fin 3 → Fin 22} (hu : Function.Injective u) (hv : Function.Injective v) :
    ∃ g ∈ blockAut 𝒮, g (Sum.inr false) = Sum.inr false ∧ g (Sum.inr true) = Sum.inr true ∧
      ∀ i, g (Sum.inl (u i)) = Sum.inl (v i) := by
  obtain ⟨m, hm⟩ := MulAction.isMultiplyPretransitive_iff.1 IsMultiplyPretransitiveM22.isMultiplyPretransitive_M22 (⟨u, hu⟩ : Fin 3 ↪ Fin 22) ⟨v, hv⟩
  have hmi : ∀ i, m.1 (u i) = v i := fun i => by
    have h2 : m • u i = v i := by simpa using congrArg (fun e : Fin 3 ↪ Fin 22 => e i) hm
    exact h2
  have hm' : m ∈ fixExt 𝒮 := by rw [fixExt_eq_top hN]; trivial
  obtain ⟨g, hgG, hgF, hg⟩ := hm'
  refine ⟨g, hgG, hgF, ?_, fun i => by rw [hg, hmi]⟩
  rcases h : g (Sum.inr true) with j | c
  · exfalso
    have h1 : g (Sum.inl ((m⁻¹).1 j)) = Sum.inl j := by
      rw [hg]; simp [Equiv.Perm.mul_apply]
    have := g.injective (h1.trans h.symm)
    cases this
  · cases c
    · exact absurd (g.injective (h.trans hgF.symm)) (by simp)
    · rfl

theorem exists_swap : ∃ s ∈ blockAut 𝒮, s (Sum.inr false) = Sum.inr true ∧
    s (Sum.inr true) = Sum.inr false := by
  haveI : Finite (blockAut 𝒮) := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := blockAut 𝒮) 2
    (by rw [card_aut_normal hN]; norm_num)
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have ht2 : ∀ z, x.1 (x.1 z) = z := fun z => by
    have := congrArg (fun y : blockAut 𝒮 => y.1 z) hx2
    simpa using this
  obtain ⟨z, hz⟩ : ∃ z, x.1 z ≠ z := by
    by_contra h
    push Not at h
    exact hx1 (Subtype.ext (Equiv.ext h))
  obtain ⟨g, hgG, hg⟩ := exists_aut_pair hN (s := {z, x.1 z}) (Finset.card_pair (Ne.symm hz))
  have hgz : g z ∈ P0 := mem_P0_of_pair hg (by simp)
  have hgy : g (x.1 z) ∈ P0 := mem_P0_of_pair hg (by simp)
  have hne : g z ≠ g (x.1 z) := fun h => hz (g.injective h).symm
  let s : Equiv.Perm Pt := g * x.1 * g⁻¹
  have hsG : s ∈ blockAut 𝒮 := mul_mem (mul_mem hgG x.2) (inv_mem hgG)
  have hs1 : s (g z) = g (x.1 z) := by simp [s, Equiv.Perm.mul_apply]
  have hs2 : s (g (x.1 z)) = g z := by simp [s, Equiv.Perm.mul_apply, ht2]
  refine ⟨s, hsG, ?_⟩
  rcases eq_F_or_T hgz with h1 | h1 <;> rcases eq_F_or_T hgy with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2] at hs1 hs2
    exact ⟨hs1, hs2⟩
  · rw [h1, h2] at hs1 hs2
    exact ⟨hs2, hs1⟩
  · exact absurd (h1.trans h2.symm) hne

theorem two_trans {p q : Pt} (hpq : p ≠ q) :
    ∃ h ∈ blockAut 𝒮, h p = Sum.inr false ∧ h q = Sum.inr true := by
  obtain ⟨g, hgG, hg⟩ := exists_aut_pair hN (s := {p, q}) (Finset.card_pair hpq)
  obtain ⟨s, hsG, hsF, hsT⟩ := exists_swap hN
  have h1 : g p ∈ P0 := mem_P0_of_pair hg (by simp)
  have h2 : g q ∈ P0 := mem_P0_of_pair hg (by simp)
  have hne : g p ≠ g q := fun h => hpq (g.injective h)
  rcases eq_F_or_T h1 with h1 | h1 <;> rcases eq_F_or_T h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨g, hgG, h1, h2⟩
  · refine ⟨s * g, mul_mem hsG hgG, ?_, ?_⟩ <;> simp [Equiv.Perm.mul_apply, h1, h2, hsF, hsT]
  · exact absurd (h1.trans h2.symm) hne

theorem five_trans {f f' : Fin 5 → Pt} (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ g ∈ blockAut 𝒮, ∀ i, g (f i) = f' i := by
  obtain ⟨h1, h1G, h1F, h1T⟩ := two_trans hN (hf.ne (show (0 : Fin 5) ≠ 1 by decide))
  obtain ⟨h2, h2G, h2F, h2T⟩ := two_trans hN (hf'.ne (show (0 : Fin 5) ≠ 1 by decide))
  have hu : Function.Injective fun j : Fin 3 => toFin (h1 (f j.succ.succ)) := by
    intro i j hij
    have := (rest_inl hf h1F h1T i).trans ((congrArg Sum.inl hij).trans (rest_inl hf h1F h1T j).symm)
    simpa using hf (h1.injective this)
  have hv : Function.Injective fun j : Fin 3 => toFin (h2 (f' j.succ.succ)) := by
    intro i j hij
    have := (rest_inl hf' h2F h2T i).trans ((congrArg Sum.inl hij).trans (rest_inl hf' h2F h2T j).symm)
    simpa using hf' (h2.injective this)
  obtain ⟨k, hkG, hkF, hkT, hk⟩ := exists_fix_three hN hu hv
  refine ⟨h2⁻¹ * (k * h1), mul_mem (inv_mem h2G) (mul_mem hkG h1G), fun i => ?_⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) i
  · show h2⁻¹ (k (h1 (f 0))) = f' 0
    rw [h1F, hkF, Equiv.Perm.inv_eq_iff_eq]
    exact h2F.symm
  · show h2⁻¹ (k (h1 (f 1))) = f' 1
    rw [h1T, hkT, Equiv.Perm.inv_eq_iff_eq]
    exact h2T.symm
  · show h2⁻¹ (k (h1 (f j.succ.succ))) = f' j.succ.succ
    have hkj : k (Sum.inl (toFin (h1 (f j.succ.succ)))) = Sum.inl (toFin (h2 (f' j.succ.succ))) := hk j
    rw [Equiv.Perm.inv_eq_iff_eq, rest_inl hf h1F h1T j, hkj]
    exact (rest_inl hf' h2F h2T j).symm

end Main

theorem isMultiplyPretransitive_blockAut {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω]
    {𝒮 : Finset (Finset Ω)} (h : IsSteiner5 𝒮) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒮) Ω 5 := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  refine MulAction.isMultiplyPretransitive_iff.2 fun e e' => ?_
  obtain ⟨g', hg'G, hg'⟩ := five_trans hφ (f := fun i => φ (e i)) (f' := fun i => φ (e' i))
    (φ.injective.comp e.injective) (φ.injective.comp e'.injective)
  have hconj : φ.trans (g'.trans φ.symm) ∈ blockAut 𝒮 := by
    have := conj_mem φ.symm hg'G
    rw [image_image_symm] at this
    exact this
  refine ⟨⟨_, hconj⟩, ?_⟩
  ext i
  simp [hg']

/-- **The automorphism group of `S(5,8,24)` is 5-transitive of order `|M24|`.** -/
theorem aut_S5824_five_transitive {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒮 : Finset (Finset Ω)}
    (h : IsSteiner5 𝒮) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒮) Ω 5 ∧ Nat.card (blockAut 𝒮) = 244823040 :=
  ⟨isMultiplyPretransitive_blockAut h, card_aut_S5824 h⟩

end CFSGOutside.WittDesigns.M24Five
