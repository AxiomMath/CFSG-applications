import CFSGOutside.ChillagSonn.Lemma15
import CFSGOutside.ChillagSonn.Simple
import CFSGOutside.ChillagSonn.Overgroups
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutside.Corpus.AutAlternatingBijectiveConj
import CFSGOutside.Corpus.M11AutInner

/-!
# Lemma (1.6): the structure of `G/S(G)`

If `G` is a nonsolvable Sylow-metacyclic group, then `G/S(G)` is `A₇`, `M₁₁`, `PSL(2, pⁿ)` or `PGL(2, pⁿ)` with
`n ≤ 2` and `pⁿ ≥ 5`, or `PGL*(2, p²)`.

Proof as in the paper: `X = G/S(G)` has no nontrivial normal solvable subgroup; a minimal normal subgroup `N` of `X`
is simple (`simple_main`) with `C_X(N) = 1` (otherwise `C_X(N)` contains another simple minimal normal subgroup and
`X` an elementary abelian subgroup of order 16), so `N ≤ X ≤ Aut(N)` and `N` is one of the groups of Lemma (1.5).
`Aut(A₇) = S₇` is not Sylow-metacyclic, `M₁₁` has no outer automorphisms, and the overgroups of `PSL(2, q)` in
`PΓL(2, q)` are handled in `Overgroups.lean`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Equiv

/-! ### `S₇` is not Sylow-metacyclic -/

theorem swap01_comm_swap23 : swap (0 : Fin 7) 1 * swap 2 3 = swap 2 3 * swap 0 1 := by decide
theorem swap01_comm_swap45 : swap (0 : Fin 7) 1 * swap 4 5 = swap 4 5 * swap 0 1 := by decide
theorem swap23_comm_swap45 : swap (2 : Fin 7) 3 * swap 4 5 = swap 4 5 * swap 2 3 := by decide

/-- Eight elements of `⟨(0 1), (2 3), (4 5)⟩ ≤ S₇`. -/
def permEightSet : Finset (Perm (Fin 7)) :=
  {1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5}

set_option maxRecDepth 100000 in
theorem card_permEightSet : permEightSet.card = 8 := by decide

/-- `S₇` contains the elementary abelian subgroup `⟨(0 1), (2 3), (4 5)⟩` of order 8, so it is not
Sylow-metacyclic. -/
theorem not_sylowMetacyclic_perm_seven : ¬ SylowMetacyclic (Perm (Fin 7)) := by
  intro h
  set s : Set (Perm (Fin 7)) := {swap 0 1, swap 2 3, swap 4 5}
  set E := Subgroup.closure s
  have hs : s.Pairwise Commute := by
    have key : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
        first | rfl | exact swap01_comm_swap23 | exact swap01_comm_swap45 | exact swap23_comm_swap45 |
          exact swap01_comm_swap23.symm | exact swap01_comm_swap45.symm | exact swap23_comm_swap45.symm
    exact fun x hx y hy _ => key x hx y hy
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    have := Subgroup.isMulCommutative_closure hs
    intro x hx y hy
    exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl <;> rw [pow_two, swap_mul_self]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [(Commute.mul_pow (hcomm y hy z hz) 2), ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have h4 := h.card_le_four E hsq
  have hsub : (permEightSet : Set (Perm (Fin 7))) ⊆ E := by
    have h01 : swap (0 : Fin 7) 1 ∈ E := Subgroup.subset_closure (by simp [s])
    have h23 : swap (2 : Fin 7) 3 ∈ E := Subgroup.subset_closure (by simp [s])
    have h45 : swap (4 : Fin 7) 5 ∈ E := Subgroup.subset_closure (by simp [s])
    intro x hx
    simp only [permEightSet, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h01
    · exact h23
    · exact h45
    · exact mul_mem h01 h23
    · exact mul_mem h01 h45
    · exact mul_mem h23 h45
    · exact mul_mem (mul_mem h01 h23) h45
  have h8 : 8 ≤ Nat.card E := by
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset, card_permEightSet] at this
    exact this
  omega

/-! ### Minimal normal subgroups and the soluble radical -/

section General

variable {X : Type} [Group X] [Finite X]

/-- A nontrivial normal subgroup contains a minimal normal subgroup. -/
theorem exists_minimalNormal_le {C : Subgroup X} (hC : C.Normal) (hC1 : C ≠ ⊥) :
    ∃ N : Subgroup X, N ≤ C ∧ N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup X, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
  classical
  have hex : ∃ n, ∃ N : Subgroup X, N ≤ C ∧ N.Normal ∧ N ≠ ⊥ ∧ Nat.card N = n :=
    ⟨_, C, le_rfl, hC, hC1, rfl⟩
  obtain ⟨N, hNC, hNn, hN1, hNc⟩ := Nat.find_spec hex
  refine ⟨N, hNC, hNn, hN1, fun M hM hMN => ?_⟩
  by_cases hM1 : M = ⊥
  · exact Or.inl hM1
  · right
    have hle : Nat.find hex ≤ Nat.card M := Nat.find_min' hex ⟨M, hMN.trans hNC, hM, hM1, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hMN (by omega)

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple {N : Type*} [Group N] [IsSimpleGroup N] (hnab : ∃ a b : N, a * b ≠ b * a) :
    Subgroup.center N = ⊥ := by
  rcases (Subgroup.center N).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

/-- In a Sylow-metacyclic group without nontrivial normal solvable subgroups, a nonabelian minimal normal
subgroup `N` has trivial centralizer. -/
theorem centralizer_eq_bot [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}]
    (hX : SylowMetacyclic X) (hrad : ∀ M : Subgroup X, M.Normal → Group.IsSolvable M → M = ⊥)
    {N : Subgroup X} [hN : N.Normal] [IsSimpleGroup N] (hnab : ∃ a b : N, a * b ≠ b * a) :
    Subgroup.centralizer (N : Set X) = ⊥ := by
  by_contra hC1
  obtain ⟨M, hMC, hMn, hM1, hmin⟩ := exists_minimalNormal_le (inferInstance : (Subgroup.centralizer (N : Set X)).Normal) hC1
  have hnabM : ∃ a b : M, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hM1 (hrad M hMn (Group.isSolvable_of_comm hcon))
  have := simple_main hX hMn hM1 hmin hnabM
  obtain ⟨F0, c0, s0, k0⟩ := exists_elem4 N hnab
  obtain ⟨F1, c1, s1, k1⟩ := exists_elem4 M hnabM
  have hF0 : ∀ x ∈ F0.map N.subtype, x ∈ N := by rintro _ ⟨k, _, rfl⟩; exact k.2
  have hF1 : ∀ x ∈ F1.map M.subtype, x ∈ M := by rintro _ ⟨k, _, rfl⟩; exact k.2
  have hcross : ∀ a ∈ F0.map N.subtype, ∀ b ∈ F1.map M.subtype, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hMC (hF1 b hb)) a (hF0 a ha))
  have hinter : ∀ x, x ∈ N → x ∈ M → x = 1 := by
    intro x hxN hxM
    have hz : (⟨x, hxN⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hMC hxM) y y.2)
    rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hb := sup_elem_bound hX (F0.map N.subtype) (F1.map M.subtype)
    (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simpa using congrArg N.subtype (c0 a ha b hb))
    (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simpa using congrArg M.subtype (c1 a ha b hb))
    (by rintro _ ⟨a, ha, rfl⟩; rw [← map_pow, s0 a ha, map_one])
    (by rintro _ ⟨a, ha, rfl⟩; rw [← map_pow, s1 a ha, map_one]) hcross
  have hcard0 : Nat.card (F0.map N.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, k0]
  have heq := Subgroup.eq_of_le_of_card_ge
    (le_sup_left : F0.map N.subtype ≤ F0.map N.subtype ⊔ F1.map M.subtype) (by omega)
  have hF1le : F1.map M.subtype ≤ F0.map N.subtype := by rw [heq]; exact le_sup_right
  have hbot : F1.map M.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (hinter x (hF0 x (hF1le hx)) (hF1 x hx))
  have : Nat.card (F1.map M.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, k1]
  rw [hbot] at this
  simp at this

/-- Conjugation embeds `X` in `Aut(N)` when `C_X(N) = 1`. -/
theorem conjNormal_injective {N : Subgroup X} [N.Normal] (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : X)) hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc n * g = (g * n * g⁻¹) * g := by rw [this]
    _ = g * n := by group

/-- A normal `PSL(2, K)` with trivial centralizer embeds `X` in `PΓL(2, K)`, with image containing `PSL(2, K)`
(from `GiuliettiKorchmaros/Thm61Nonabelian.lean`). -/
theorem embedding_PGammaL2 [SemilinearEquivAut.{0}] {K : Type} [Field K] [Finite K] {N : Subgroup X}
    [N.Normal] (e : N ≃* PSL2 K) (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    ∃ φ : X →* PGammaL2 K, Function.Injective φ ∧ pslInPGammaL K ≤ φ.range := by
  obtain ⟨e', he'⟩ := SemilinearEquivAut.semilinearEquivAut K
  refine ⟨e'.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal),
    e'.symm.injective.comp ((MulAut.congr e).injective.comp (conjNormal_injective hC)), ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨((e.symm x : N) : X), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [← he' x]
  congr 1
  apply MulEquiv.ext
  intro y
  obtain ⟨n, rfl⟩ := e.surjective y
  have hc : (MulAut.conjNormal ((e.symm x : N) : X)) n = e.symm x * n * (e.symm x)⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  change e ((MulAut.conjNormal ((e.symm x : N) : X)) (e.symm (e n))) = x * e n * x⁻¹
  rw [MulEquiv.symm_apply_apply, hc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- `A₇` case: `X = N` (adapted from `GiuliettiKorchmaros/Thm61Nonabelian.lean`). -/
theorem eq_top_of_alternatingSeven [AutAlternatingBijectiveConj] (hX : SylowMetacyclic X)
    {N : Subgroup X} [N.Normal] (e : N ≃* alternatingGroup (Fin 7))
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : N = ⊤ := by
  classical
  let Φ : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7) →* MulAut _)
    (AutAlternatingBijectiveConj.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num))
  let ψ : X →* Equiv.Perm (Fin 7) :=
    Φ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  have hψ : Function.Injective ψ :=
    Φ.symm.injective.comp ((MulAut.congr e).injective.comp (conjNormal_injective hC))
  have hψN : ∀ n : N, ψ n = (e n : Equiv.Perm (Fin 7)) := by
    intro n
    have : Φ (e n) = MulAut.congr e (MulAut.conjNormal (n : X)) := by
      apply MulEquiv.ext
      intro y
      obtain ⟨m, rfl⟩ := e.surjective y
      apply Subtype.ext
      have hc : (MulAut.conjNormal (n : X)) m = n * m * n⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      change ((e n : Equiv.Perm (Fin 7)) * (e m) * (e n)⁻¹ : Equiv.Perm (Fin 7)) =
        ((e ((MulAut.conjNormal (n : X)) (e.symm (e m)))) : Equiv.Perm (Fin 7))
      rw [MulEquiv.symm_apply_apply, hc, map_mul, map_mul, map_inv]
      rfl
    change Φ.symm (MulAut.congr e (MulAut.conjNormal (n : X))) = _
    rw [← this, MulEquiv.symm_apply_apply]
  by_contra hNtop
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ N := by
    by_contra h; push Not at h; exact hNtop (eq_top_iff.2 fun g _ => h g)
  have hgodd : ψ g ∉ alternatingGroup (Fin 7) := by
    intro hgA
    obtain ⟨n, hn⟩ := e.surjective ⟨ψ g, hgA⟩
    have : ψ g = ψ n := by rw [hψN, hn]
    exact hg (hψ this ▸ n.2)
  have hrange : ψ.range = ⊤ := by
    have hle : alternatingGroup (Fin 7) ≤ ψ.range := by
      intro σ hσ
      obtain ⟨n, hn⟩ := e.surjective ⟨σ, hσ⟩
      exact ⟨n, by rw [hψN, hn]⟩
    have hidx := Subgroup.index_dvd_of_le hle
    rw [alternatingGroup.index_eq_two] at hidx
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hrel := Subgroup.relIndex_mul_index hle
      rw [h2, alternatingGroup.index_eq_two] at hrel
      have hrel1 : (alternatingGroup (Fin 7)).relIndex ψ.range = 1 := by omega
      exact hgodd (Subgroup.relIndex_eq_one.mp hrel1 ⟨g, rfl⟩)
  let eX : X ≃* Equiv.Perm (Fin 7) := MulEquiv.ofBijective ψ ⟨hψ, MonoidHom.range_eq_top.mp hrange⟩
  exact not_sylowMetacyclic_perm_seven (hX.of_mulEquiv eX)

/-- `M₁₁` case: `X = N` (adapted from `GiuliettiKorchmaros/Thm61Nonabelian.lean`). -/
theorem eq_top_of_M11 [M11AutInner] {N : Subgroup X} [N.Normal] (e : N ≃* Open.StatedM11)
    (hC : Subgroup.centralizer (N : Set X) = ⊥) : N = ⊤ := by
  let f : N ≃* Blueprint.NativeSporadic.M11 := e
  apply eq_top_iff.2
  intro g _
  obtain ⟨k, hk⟩ := M11AutInner.m11_aut_inner (MulAut.congr f (MulAut.conjNormal g))
  set n : N := f.symm k
  have h2 : ∀ m ∈ N, g * m * g⁻¹ = n * m * (n : X)⁻¹ := by
    intro m hm
    have h1 := congrArg (fun φ : MulAut Blueprint.NativeSporadic.M11 => f.symm (φ (f ⟨m, hm⟩))) hk
    change f.symm (f ((MulAut.conjNormal g) (f.symm (f ⟨m, hm⟩)))) = f.symm (k * f ⟨m, hm⟩ * k⁻¹) at h1
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at h1
    have := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply, n] using this
  have hc : (n : X)⁻¹ * g ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := h2 m hm
    calc m * ((n : X)⁻¹ * g) = (n : X)⁻¹ * (n * m * (n : X)⁻¹) * g := by group
      _ = (n : X)⁻¹ * (g * m * g⁻¹) * g := by rw [this]
      _ = (n : X)⁻¹ * g * m := by group
  rw [hC, Subgroup.mem_bot] at hc
  have : g = n := by
    calc g = (n : X) * ((n : X)⁻¹ * g) := by group
      _ = n := by rw [hc, mul_one]
  rw [this]
  exact n.2

end General

/-- `G/S(G)` has no nontrivial normal solvable subgroup. -/
theorem eq_bot_of_normal_solvable_quotient {G : Type} [Group G] [Finite G]
    (M : Subgroup (G ⧸ solvableRadical G)) (hM : M.Normal) (hs : Group.IsSolvable M) : M = ⊥ := by
  set S := solvableRadical G
  set M' : Subgroup G := M.comap (QuotientGroup.mk' S)
  have hSM : S ≤ M' := fun x hx => by
    change QuotientGroup.mk' S x ∈ M
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have : Group.IsSolvable S := isSolvable_solvableRadical
  have hM's : Group.IsSolvable M' := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hSM) ((QuotientGroup.mk' S).subgroupComap M) ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : (x : G) ∈ S := by
      have h1 : ((x : G) : G ⧸ S) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, this⟩, rfl⟩
  have hle : M' ≤ S := le_solvableRadical (hM.comap _) hM's
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S x
  exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff g).mpr (hle hx))

end CFSGOutside.ChillagSonn
