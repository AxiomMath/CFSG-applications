import CFSGOutside.HallPaige.Lie.ExcTits
import CFSGOutside.Corpus.HallPaige.LieExcTw

/-!
# Tits systems from the corpus notion `IsSplitBNPair`

`CFSGOutside.HallPaige.ExcTw.titsOfIsSplitBNPair`: a corpus split `(B, N)`-pair (with an unnamed set `S` of
simple reflections) gives a `TauCeti.TitsSystem`, whose Bruhat cells are then disjoint
(`TauCeti.TitsSystem.eq_of_mem_bruhatCell_of_mem`).
-/

namespace CFSGOutside.HallPaige.ExcTw

open DoubleCoset TauCeti CFSGOutside.Corpus.ExcTw
open scoped Pointwise

variable {G : Type} [Group G] {p : ℕ} {B N : Subgroup G}

theorem inf_subgroupOf_eq' (B N : Subgroup G) : (B ⊓ N).subgroupOf N = B.subgroupOf N := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem normal_subgroupOf (h : IsSplitBNPair p B N) : (B.subgroupOf N).Normal :=
  inf_subgroupOf_eq' B N ▸ h.normal_inter

/-- The simple reflections of a corpus split `(B, N)`-pair. -/
noncomputable def splitS (h : IsSplitBNPair p B N) : Set G := h.coxeter.choose

theorem splitS_spec (h : IsSplitBNPair p B N) :
    (∀ s ∈ splitS h, s ∈ N ∧ s ∉ B ∧ s ^ 2 ∈ B) ∧
    Subgroup.closure (splitS h) ⊔ (B ⊓ N) = N ∧
    (∀ s ∈ splitS h, ∀ w ∈ N, ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂) ∧
    (∀ s ∈ splitS h, ∃ b ∈ B, s * b * s ∉ B) :=
  h.coxeter.choose_spec

/-- **The Tits system of a corpus split `(B, N)`-pair.** -/
noncomputable def titsOfIsSplitBNPair (h : IsSplitBNPair p B N) : TauCeti.TitsSystem G :=
  have hnorm : (B.subgroupOf N).Normal := normal_subgroupOf h
  { subgroupB := B
    subgroupN := N
    closure_subgroupB_union_subgroupN := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      exact h.gen
    intersection_normal := hnorm
    simple := {w | ∃ s : N, (s : G) ∈ splitS h ∧ w = QuotientGroup.mk s}
    closure_simple := by
      intro _
      rw [eq_top_iff]
      rintro w -
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
      set C := Subgroup.closure {w : N ⧸ B.subgroupOf N |
        ∃ s : N, (s : G) ∈ splitS h ∧ w = QuotientGroup.mk s}
      let D : Subgroup G := ((C.comap (QuotientGroup.mk' (B.subgroupOf N))).map N.subtype)
      have hS : Subgroup.closure (splitS h) ≤ D := by
        rw [Subgroup.closure_le]
        intro s hs
        have hsN := ((splitS_spec h).1 s hs).1
        exact ⟨⟨s, hsN⟩, Subgroup.subset_closure ⟨⟨s, hsN⟩, hs, rfl⟩, rfl⟩
      have hBN : B ⊓ N ≤ D := by
        intro x hx
        have hx' := Subgroup.mem_inf.1 hx
        refine ⟨⟨x, hx'.2⟩, ?_, rfl⟩
        show QuotientGroup.mk' (B.subgroupOf N) ⟨x, hx'.2⟩ ∈ C
        rw [QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff _).2 (show (⟨x, hx'.2⟩ : N) ∈ B.subgroupOf N from hx'.1)]
        exact C.one_mem
      have hN : N ≤ D := (splitS_spec h).2.1 ▸ sup_le hS hBN
      obtain ⟨m, hm, hmn⟩ := hN n.2
      have : m = n := Subtype.ext hmn
      subst this
      exact hm
    exists_simpleRep_sq_mem := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s, rfl, ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, ← pow_two]
      exact ((splitS_spec h).1 s hs).2.2
    mul_doubleCoset_subset := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s, rfl, fun w => ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_doubleCoset.1 hx
      obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := mem_doubleCoset.1 hy
      obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ :=
        (splitS_spec h).2.2.1 s hs w w.2 (b₂ * b₃) (B.mul_mem hb₂ hb₃)
      have key : b₁ * (s : G) * b₂ * (b₃ * (w : G) * b₄) =
          b₁ * ((s : G) * (b₂ * b₃) * w) * b₄ := by group
      show b₁ * (s : G) * b₂ * (b₃ * (w : G) * b₄) ∈ _
      rw [key]
      rcases hc with hc | hc
      · refine Or.inr (mem_doubleCoset.2 ⟨b₁ * c₁, B.mul_mem hb₁ hc₁, c₂ * b₄,
          B.mul_mem hc₂ hb₄, ?_⟩)
        rw [hc]; group
      · refine Or.inl (mem_doubleCoset.2 ⟨b₁ * c₁, B.mul_mem hb₁ hc₁, c₂ * b₄,
          B.mul_mem hc₂ hb₄, ?_⟩)
        rw [hc, Subgroup.coe_mul]; group
    exists_conj_not_mem := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s, rfl, ?_⟩
      obtain ⟨b, hb, hsb⟩ := (splitS_spec h).2.2.2 s hs
      refine ⟨⟨b, hb⟩, fun hin => hsb ?_⟩
      have h2 : (s : G) * s ∈ B := by rw [← pow_two]; exact ((splitS_spec h).1 s hs).2.2
      have : (s : G) * b * s = ((s : G) * b * (s : G)⁻¹) * ((s : G) * s) := by group
      rw [this]
      exact B.mul_mem hin h2 }

end CFSGOutside.HallPaige.ExcTw
