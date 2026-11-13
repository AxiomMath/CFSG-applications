import Mathlib
import CFSGOutside.WittDesigns.AutS4723.Main
import CFSGOutside.Corpus.IsMultiplyPretransitiveM22
import CFSGOutside.Corpus.M22LeHexadAut
import CFSGOutside.Corpus.M22Simple
import CFSGOutside.WittDesigns.M24FiveTransitive.M22Index

/-!
# The automorphism group of `S(4,7,23)` is 4-transitive

For a normalized `S(4,7,23)` the stabilizer of the point `Q` restricts onto the automorphisms of the hexads
that preserve a class of odd heptads. These form an index two subgroup of the hexad automorphisms. Its
intersection with `M22` has index at most two in `M22`, hence is all of `M22` by simplicity. So the
stabilizer of `Q` acts 3-transitively on the 22 other points, and the group is transitive on points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.M24Four

open CFSGOutside.WittDesigns.M24Five
open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt4723 CFSGOutside.WittDesigns.Aut4723
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven)
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple]

theorem pres_mul {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ hexadAut) (hb : b ∈ hexadAut) (hpa : Pres Y0 a) (hpb : Pres Y0 b) : Pres Y0 (a * b) := by
  unfold Pres at *
  rw [map_perm_mul']
  have h1 : IsOddSeven (Y0.map a.toEmbedding) := oddSeven_map_of_mem ha hY0
  have h2 : IsOddSeven ((Y0.map b.toEmbedding).map a.toEmbedding) :=
    oddSeven_map_of_mem ha (oddSeven_map_of_mem hb hY0)
  exact Kin.trans h2 h1 hY0 ((kin_map_iff a).2 hpb) hpa

theorem pres_mul_of_not {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ hexadAut) (hb : b ∈ hexadAut) (hpa : ¬ Pres Y0 a) (hpb : ¬ Pres Y0 b) :
    Pres Y0 (a * b) := by
  unfold Pres at *
  rw [map_perm_mul']
  have h1 : IsOddSeven (Y0.map a.toEmbedding) := oddSeven_map_of_mem ha hY0
  have h2 : IsOddSeven ((Y0.map b.toEmbedding).map a.toEmbedding) :=
    oddSeven_map_of_mem ha (oddSeven_map_of_mem hb hY0)
  have hn : ¬ Kin (Y0.map a.toEmbedding) ((Y0.map b.toEmbedding).map a.toEmbedding) := fun h =>
    hpb ((kin_map_iff a).1 h.symm)
  exact Kin.pigeon h1 h2 hY0 hn hpa

theorem map_one_perm (Y : Finset (Fin 22)) : Y.map (1 : Equiv.Perm (Fin 22)).toEmbedding = Y := by
  ext x
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple] in
noncomputable def presSub {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) : Subgroup M22 where
  carrier := {a | Pres Y0 a.1}
  mul_mem' {a b} ha hb := pres_mul hY0 (M22LeHexadAut.M22_le_hexadAut a.2) (M22LeHexadAut.M22_le_hexadAut b.2) ha hb
  one_mem' := Or.inl (map_one_perm Y0)
  inv_mem' {a} ha := by
    have e : (Y0.map (a.1⁻¹).toEmbedding).map a.1.toEmbedding = Y0 := by
      rw [← map_perm_mul', mul_inv_cancel]
      exact map_one_perm Y0
    show Kin (Y0.map (a.1⁻¹).toEmbedding) Y0
    rw [← kin_map_iff a.1, e]
    exact ha.symm

theorem presSub_eq_top {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) : presSub hY0 = ⊤ :=
  m22_eq_top_of_mul _ fun a b ha hb =>
    pres_mul_of_not hY0 (M22LeHexadAut.M22_le_hexadAut b.2) (M22LeHexadAut.M22_le_hexadAut a.2) hb ha

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple] in
def toFin23 : P23 → Fin 22 := Sum.elim id (fun _ => 0)

theorem eq_inl_toFin23 {x : P23} (h : x ≠ Q) : x = Sum.inl (toFin23 x) := by
  rcases x with i | u
  · rfl
  · cases u
    exact absurd rfl h

section Main

variable {𝒯 : Finset (Finset P23)} (hN : IsNormal 𝒯)
include hN

theorem exists_fix_three {u v : Fin 3 → Fin 22} (hu : Function.Injective u) (hv : Function.Injective v) :
    ∃ g ∈ blockAut 𝒯, g Q = Q ∧ ∀ i, g (Sum.inl (u i)) = Sum.inl (v i) := by
  obtain ⟨Y0, hY0⟩ := exists_noQ hN
  have hY0' := isOddSeven_of_mem hN hY0
  obtain ⟨m, hm⟩ := MulAction.isMultiplyPretransitive_iff.1 IsMultiplyPretransitiveM22.isMultiplyPretransitive_M22
    (⟨u, hu⟩ : Fin 3 ↪ Fin 22) ⟨v, hv⟩
  have hmi : ∀ i, m.1 (u i) = v i := fun i => by
    have h2 : m • u i = v i := by simpa using congrArg (fun e : Fin 3 ↪ Fin 22 => e i) hm
    exact h2
  have hpres : Pres Y0 m.1 := by
    have : m ∈ presSub hY0' := by rw [presSub_eq_top hY0']; trivial
    exact this
  obtain ⟨g, hgG, hgQ, hg⟩ := exists_ext hN hY0 (M22LeHexadAut.M22_le_hexadAut m.2) hpres
  exact ⟨g, hgG, hgQ, fun i => by rw [hg, hmi]⟩

theorem four_trans {f f' : Fin 4 → P23} (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ g ∈ blockAut 𝒯, ∀ i, g (f i) = f' i := by
  obtain ⟨h1, h1G, h1Q⟩ := exists_aut_to_Q hN (f 0)
  obtain ⟨h2, h2G, h2Q⟩ := exists_aut_to_Q hN (f' 0)
  have rest : ∀ (h : Equiv.Perm P23) (F : Fin 4 → P23), Function.Injective F → h (F 0) = Q →
      ∀ j : Fin 3, h (F j.succ) = Sum.inl (toFin23 (h (F j.succ))) := by
    intro h F hF h0 j
    apply eq_inl_toFin23
    rw [← h0]
    intro e
    exact Fin.succ_ne_zero _ (hF (h.injective e))
  have hu : Function.Injective fun j : Fin 3 => toFin23 (h1 (f j.succ)) := by
    intro i j hij
    have := (rest h1 f hf h1Q i).trans ((congrArg Sum.inl hij).trans (rest h1 f hf h1Q j).symm)
    simpa using hf (h1.injective this)
  have hv : Function.Injective fun j : Fin 3 => toFin23 (h2 (f' j.succ)) := by
    intro i j hij
    have := (rest h2 f' hf' h2Q i).trans ((congrArg Sum.inl hij).trans (rest h2 f' hf' h2Q j).symm)
    simpa using hf' (h2.injective this)
  obtain ⟨k, hkG, hkQ, hk⟩ := exists_fix_three hN hu hv
  refine ⟨h2⁻¹ * (k * h1), mul_mem (inv_mem h2G) (mul_mem hkG h1G), fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · show h2⁻¹ (k (h1 (f 0))) = f' 0
    rw [h1Q, hkQ, Equiv.Perm.inv_eq_iff_eq]
    exact h2Q.symm
  · show h2⁻¹ (k (h1 (f j.succ))) = f' j.succ
    have hkj : k (Sum.inl (toFin23 (h1 (f j.succ)))) = Sum.inl (toFin23 (h2 (f' j.succ))) := hk j
    rw [Equiv.Perm.inv_eq_iff_eq, rest h1 f hf h1Q j, hkj]
    exact (rest h2 f' hf' h2Q j).symm

end Main

theorem isMultiplyPretransitive_blockAut_four {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω]
    {𝒯 : Finset (Finset Ω)} (h : IsSteiner4 𝒯) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒯) Ω 4 := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  refine MulAction.isMultiplyPretransitive_iff.2 fun e e' => ?_
  obtain ⟨g', hg'G, hg'⟩ := four_trans hφ (f := fun i => φ (e i)) (f' := fun i => φ (e' i))
    (φ.injective.comp e.injective) (φ.injective.comp e'.injective)
  have hconj : φ.trans (g'.trans φ.symm) ∈ blockAut 𝒯 := by
    have := CFSGOutside.WittDesigns.Aut5824.conj_mem φ.symm hg'G
    rw [CFSGOutside.WittDesigns.Aut5824.image_image_symm] at this
    exact this
  refine ⟨⟨_, hconj⟩, ?_⟩
  ext i
  simp [hg']

/-- **The automorphism group of `S(4,7,23)` is 4-transitive of order `|M23|`.** -/
theorem aut_S4723_four_transitive {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner4 𝒯) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒯) Ω 4 ∧ Nat.card (blockAut 𝒯) = 10200960 :=
  ⟨isMultiplyPretransitive_blockAut_four h, card_aut_S4723 h⟩

end CFSGOutside.WittDesigns.M24Four
