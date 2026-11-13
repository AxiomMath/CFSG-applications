import Mathlib

/-!
# Copied corpus definitions: `p`-soluble groups

`CFSGOutside.Corpus.IsPSolvable` is `CFSG.HallHigman.IsPSolvable`, copied verbatim from
`CFSG/GroupTheory/HallHigmanPiCore.lean` (line 18) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/PSolvable.lean` shows that the copy
equals the original.

A group is `p`-soluble when every simple section `H/T` of a subnormal subgroup `H` has order `p` or prime to `p`.
The closure properties the proofs need (homomorphic images, extensions, soluble groups, groups of order prime to
`p`) are proved here, following `CFSG/LocalAnalysis/AGLEmbeddingD2/Tits/OrdinaryProofs/PSolvableClosure.lean`.
-/

namespace CFSGOutside.Corpus

open Subgroup

/-- A group is `p`-soluble if every simple section of a subnormal subgroup has order `p` or prime to `p`. Copy of
`CFSG.HallHigman.IsPSolvable`, `CFSG/GroupTheory/HallHigmanPiCore.lean` line 18. -/
def IsPSolvable (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ H : Subgroup X, H.IsSubnormal → ∀ (T : Subgroup H) [T.Normal], IsSimpleGroup (H ⧸ T) →
    T.index = p ∨ Nat.Coprime p T.index

variable {p : ℕ}

/-- A simple quotient of a subnormal subgroup of a `p`-soluble group has order `p` or prime to `p`. -/
theorem IsPSolvable.card_simple_quotient {X : Type*} [Group X] (hX : IsPSolvable p X)
    {B : Subgroup X} (hB : B.IsSubnormal) {Q : Type*} [Group Q] [IsSimpleGroup Q] (ψ : B →* Q)
    (hψ : Function.Surjective ψ) : Nat.card Q = p ∨ Nat.Coprime p (Nat.card Q) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  haveI : IsSimpleGroup (B ⧸ ψ.ker) := e.isSimpleGroup
  have hidx : ψ.ker.index = Nat.card Q := Nat.card_congr e.toEquiv
  rw [← hidx]
  exact hX B hB ψ.ker this

/-- Homomorphic images of `p`-soluble groups are `p`-soluble. -/
theorem IsPSolvable.of_surjective {X Y : Type*} [Group X] [Group Y] (hX : IsPSolvable p X)
    (f : X →* Y) (hf : Function.Surjective f) : IsPSolvable p Y := by
  intro H hH T _ hs
  have hB : (H.comap f).IsSubnormal := hH.comap f
  let g : H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  let ψ : H.comap f →* H ⧸ T := (QuotientGroup.mk' T).comp g
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx⟩ := hf h
    have hxB : f x ∈ H := hx ▸ h.2
    refine ⟨⟨x, hxB⟩, ?_⟩
    exact congrArg (QuotientGroup.mk' T) (Subtype.ext hx : g ⟨x, hxB⟩ = h)
  exact hX.card_simple_quotient hB ψ hψ

theorem isPSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : IsPSolvable p A) :
    IsPSolvable p B :=
  h.of_surjective e.toMonoidHom e.surjective

theorem isPSolvable_quotient {X : Type*} [Group X] (h : IsPSolvable p X) (N : Subgroup X) [N.Normal] :
    IsPSolvable p (X ⧸ N) :=
  h.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- A finite soluble group is `p`-soluble. -/
theorem isPSolvable_of_isSolvable [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (h : Group.IsSolvable X) : IsPSolvable p X := by
  intro H _ T _ hs
  haveI := h
  haveI : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (f := H.subtype)
    H.subtype_injective
  haveI : Group.IsSolvable (H ⧸ T) := Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective T)
  letI : CommGroup (H ⧸ T) := { (inferInstance : Group (H ⧸ T)) with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance }
  have hq : (Nat.card (H ⧸ T)).Prime := IsSimpleGroup.prime_card
  by_cases hpq : p = Nat.card (H ⧸ T)
  · exact Or.inl hpq.symm
  · exact Or.inr ((Nat.coprime_primes Fact.out hq).2 hpq)

/-- A finite group of order prime to `p` is `p`-soluble. -/
theorem isPSolvable_of_coprime {X : Type*} [Group X] [Finite X] (h : Nat.Coprime p (Nat.card X)) :
    IsPSolvable p X := by
  intro H _ T _ _
  right
  exact Nat.Coprime.coprime_dvd_right
    ((T.index_dvd_card).trans (Subgroup.card_subgroup_dvd_card H)) h

/-- An extension of a `p`-soluble group by a `p`-soluble group is `p`-soluble. -/
theorem isPSolvable_of_normal {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hN : IsPSolvable p N) (hQ : IsPSolvable p (X ⧸ N)) : IsPSolvable p X := by
  intro H hH T hT hs
  have hMn : ((N.subgroupOf H).map (QuotientGroup.mk' T)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective T)
  by_cases hM : (N.subgroupOf H).map (QuotientGroup.mk' T) = ⊥
  · -- `N ∩ H ≤ T`, so `H/T` is a quotient of the subnormal subgroup `HN/N` of `X/N`
    have hKT : N.subgroupOf H ≤ T := by
      intro k hk
      have hmem : QuotientGroup.mk' T k ∈ (⊥ : Subgroup (H ⧸ T)) := by
        rw [← hM]; exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    let S : Subgroup (X ⧸ N) := H.map (QuotientGroup.mk' N)
    have hS : S.IsSubnormal := hH.map (QuotientGroup.mk'_surjective N)
    let φ : H →* S := MonoidHom.codRestrict ((QuotientGroup.mk' N).comp H.subtype) S
      (fun h => Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨h, hh⟩, Subtype.ext rfl⟩
    have hker : φ.ker ≤ T := by
      intro k hk
      have hk1 : (QuotientGroup.mk' N) (k : X) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      exact hKT (Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff _).mp hk1))
    let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    let ψ : S →* H ⧸ T :=
      (QuotientGroup.map φ.ker T (MonoidHom.id H) hker).comp e.symm.toMonoidHom
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨e (QuotientGroup.mk h), ?_⟩
      show (QuotientGroup.map φ.ker T (MonoidHom.id H) hker) (e.symm (e (QuotientGroup.mk h)))
        = QuotientGroup.mk h
      rw [MulEquiv.symm_apply_apply]
      rfl
    exact hQ.card_simple_quotient hS ψ hψ
  · -- `N ∩ H` maps onto `H/T`, so `H/T` is a quotient of the subnormal subgroup `H ∩ N` of `N`
    have hM' : (N.subgroupOf H).map (QuotientGroup.mk' T) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((N.subgroupOf H).map (QuotientGroup.mk' T)) with h | h
      · exact absurd h hM
      · exact h
    let f : ↥(H.subgroupOf N) →* H :=
      { toFun := fun x => ⟨(x.1 : X), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let ψ : ↥(H.subgroupOf N) →* H ⧸ T := (QuotientGroup.mk' T).comp f
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      have hmem : QuotientGroup.mk' T h ∈ (N.subgroupOf H).map (QuotientGroup.mk' T) := by
        rw [hM']; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.mp hmem
      refine ⟨⟨⟨(k : X), Subgroup.mem_subgroupOf.mp hk⟩, Subgroup.mem_subgroupOf.mpr k.2⟩, ?_⟩
      exact hkh
    exact hN.card_simple_quotient hH.subgroupOf ψ hψ

end CFSGOutside.Corpus
