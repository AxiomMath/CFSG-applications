import CFSGOutside.Gagola.Main
import CFSGOutside.Gagola.D8Struct
import CFSGOutside.Gagola.D8Pullback
import CFSGOutside.Gagola.AlmostSimple
import CFSGOutside.Gagola.PSL2Primes
import CFSGOutside.Corpus.ASevenOrExistsNormalPsl2
import CFSGOutside.Corpus.CardMulAutPsl2GF
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy

/-!
# Gagola, Lemma 4.4, the dihedral branch (`p = 2`)

Let `(H, Z, χ)` be a fully ramified triple, `Z ≤ K ⊴ H` with `|H : K| = 2`, such that `X = K/Z` has dihedral Sylow
2-subgroups of order 8 and no nontrivial 2-group quotient (`O²(X) = X`). Then we get a contradiction.

By the classification of groups with dihedral Sylow 2-subgroups, `X/O(X)` has a characteristic subgroup `N`
with trivial centralizer, `N ≅ A₇` or `PSL(2, q)` (`ybar_structure`). Pulling back to `H`
(`pullback_characteristic`), `H/C` has a normal subgroup `S ≅ N` with trivial centralizer and `[H/C : S] ∣ 4f`.
Then `almost_simple_false` (Theorem 2.5) contradicts the choice of primes (`psl2_prime_choice`).
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus
open scoped MatrixGroups

noncomputable section

theorem hD8_of_equiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] (e : Y ≃* Y')
    (h : ∀ P : Sylow 2 Y, Nonempty ((P : Subgroup Y) ≃* DihedralGroup 4)) :
    ∀ P : Sylow 2 Y', Nonempty ((P : Subgroup Y') ≃* DihedralGroup 4) := by
  intro P'
  let Q : Sylow 2 Y := P'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : (Q : Subgroup Y) = (P' : Subgroup Y').map e.symm.toMonoidHom := Sylow.coe_mapSurjective _ _
  obtain ⟨φ⟩ := h Q
  exact ⟨(((P' : Subgroup Y').equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
    (MulEquiv.subgroupCongr hQ.symm)).trans φ⟩

theorem hno2_of_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∀ (N : Subgroup Y) (_ : N.Normal), IsPGroup 2 (Y ⧸ N) → N = ⊤) :
    ∀ (N : Subgroup Y') (_ : N.Normal), IsPGroup 2 (Y' ⧸ N) → N = ⊤ := by
  intro N' hN' hp
  haveI := hN'
  haveI hNn : (N'.comap e.toMonoidHom).Normal := hN'.comap _
  have hmap : (N'.comap e.toMonoidHom).map e.toMonoidHom = N' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N'
  let q : Y ⧸ (N'.comap e.toMonoidHom) ≃* Y' ⧸ N' :=
    QuotientGroup.congr (N'.comap e.toMonoidHom) N' e hmap
  have hN : N'.comap e.toMonoidHom = ⊤ := h _ hNn (hp.of_equiv q.symm)
  rw [eq_top_iff]
  intro y' _
  have : e.symm y' ∈ N'.comap e.toMonoidHom := by rw [hN]; trivial
  simpa using this

theorem sylow_prop_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X ≃* Y) {p : ℕ}
    [Fact p.Prime]
    (h : ∀ P : Sylow p Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1 ∧
      (Nat.card P).factorial < Nat.card Y) :
    ∀ P : Sylow p X, IsCyclic (P : Subgroup X) ∧ Nat.card P ≠ 1 ∧
      (Nat.card P).factorial < Nat.card X := by
  intro P
  haveI : Finite Y := Finite.of_equiv X φ.toEquiv
  obtain ⟨P'⟩ := (inferInstance : Nonempty (Sylow p Y))
  have hc : Nat.card X = Nat.card Y := Nat.card_congr φ.toEquiv
  have hcard : Nat.card P = Nat.card P' := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, hc]
  obtain ⟨c, n, f⟩ := h P'
  obtain ⟨c', n'⟩ := cyclic_sylow_of_equiv φ (fun Q => ⟨(h Q).1, (h Q).2.1⟩) P
  exact ⟨c', n', by rw [hcard, hc]; exact f⟩

section Main

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}

/-- **Gagola, Lemma 4.4 (p = 2), the dihedral branch.** Let `(H, Z, χ)` be a fully ramified triple and
`Z ≤ K ⊴ H` with `|H : K| = 2`. If `K/Z` has Sylow 2-subgroups isomorphic to `D₈` and no nontrivial 2-group
quotient, we get a contradiction. -/
theorem d8_branch [ASevenOrExistsNormalPsl2] [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy]
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) (hidx : K.index = 2)
    (hD8 : ∀ P : Sylow 2 (K ⧸ Z.subgroupOf K), Nonempty ((P : Subgroup (K ⧸ Z.subgroupOf K)) ≃* DihedralGroup 4))
    (hno2 : ∀ (N : Subgroup (K ⧸ Z.subgroupOf K)) (_ : N.Normal),
      IsPGroup 2 ((K ⧸ Z.subgroupOf K) ⧸ N) → N = ⊤) : False := by
  -- `K/Z` as a normal subgroup `K'` of `G = H/Z`
  let f : K →* H ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have hker : f.ker = Z.subgroupOf K := by
    ext k; simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = K.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  haveI hK'n : f.range.Normal := by
    rw [hrange]; exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  let e : K ⧸ Z.subgroupOf K ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange f)
  have hK'idx : f.range.index = 2 := by
    rw [hrange, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective Z)
      (by rw [QuotientGroup.ker_mk']; exact hZK), hidx]
  have hD8' := hD8_of_equiv e hD8
  have hno2' := hno2_of_equiv e hno2
  obtain ⟨N, hNc, hNcent, hcases⟩ := ybar_structure (Y := f.range) hD8' hno2'
  haveI := oddCore_normal (f.range)
  haveI := oddCore_characteristic (Y := f.range)
  obtain ⟨C, hC, S, hS, hSc, ⟨eS⟩, hSidx⟩ :=
    pullback_characteristic f.range (oddCore f.range) N hNcent
  -- the quotient map `H → (H/Z)/C`
  let φ : H →* (H ⧸ Z) ⧸ C := (QuotientGroup.mk' C).comp (QuotientGroup.mk' Z)
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective C).comp (QuotientGroup.mk'_surjective Z)
  have hZφ : Z ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    simp [φ, (QuotientGroup.eq_one_iff z).mpr hz]
  rw [hK'idx] at hSidx
  rcases hcases with ⟨hNtop, ⟨eN⟩⟩ | ⟨F, _, _, p, f', _, hF, hf, hodd, h5, ⟨eN⟩, hNidx⟩
  · -- `A₇`
    haveI := isSimpleGroup_alt7
    haveI : Nontrivial S := (eS.trans eN).toEquiv.nontrivial
    haveI : IsSimpleGroup S := by
      exact IsSimpleGroup.isSimpleGroup_of_surjective (eS.trans eN).symm.toMonoidHom
        (eS.trans eN).symm.surjective
    have hNidx1 : N.index = 1 := by rw [hNtop]; exact Subgroup.index_top
    refine almost_simple_false hfr φ hφ hZφ S ?_ hSc (Or.inr ⟨5, ⟨by norm_num⟩, ?_, ?_⟩)
    · obtain ⟨a, b, hab⟩ := not_comm_alt7
      refine ⟨(eS.trans eN).symm a, (eS.trans eN).symm b, fun h => hab ?_⟩
      simpa using congrArg (eS.trans eN) h
    · intro h5S
      have : S.index ∣ 2 := by rw [hNidx1] at hSidx; simpa using hSidx
      have := h5S.trans this
      omega
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact sylow_prop_of_equiv (eS.trans eN) sylow5_alt7
  · haveI : Fact p.Prime := inferInstance
    have h4 : 4 ≤ Fintype.card F := by rw [hF]; omega
    haveI := isSimpleGroup_psl2 F h4
    let eP : S ≃* PSL(2, F) := eS.trans eN
    haveI : Nontrivial S := eP.toEquiv.nontrivial
    haveI : IsSimpleGroup S :=
      IsSimpleGroup.isSimpleGroup_of_surjective eP.symm.toMonoidHom eP.symm.surjective
    have hdiv : S.index ∣ 4 * f' := by
      have h1 : 2 * N.index ∣ 2 * (2 * f') := Nat.mul_dvd_mul_left 2 hNidx
      have h2 : S.index ∣ 2 * N.index := hSidx
      exact (h2.trans h1).trans (by rw [← mul_assoc]; exact dvd_rfl)
    have hnab : ∃ a b : S, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := not_comm_psl2 F h4
      refine ⟨eP.symm a, eP.symm b, fun h => hab ?_⟩
      simpa using congrArg eP h
    rcases psl2_prime_choice F p f' hF hf hodd h5 with
      ⟨r₁, r₂, h1, h2, hne, hn1, hn2, hs1, hs2⟩ | ⟨h9, hc, hn5, hs5⟩
    · exact almost_simple_false hfr φ hφ hZφ S hnab hSc (Or.inl ⟨r₁, r₂, h1, h2, hne,
        fun h => hn1 (h.trans hdiv), fun h => hn2 (h.trans hdiv),
        fun P => cyclic_sylow_of_equiv eP hs1 P, fun P => cyclic_sylow_of_equiv eP hs2 P⟩)
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      refine almost_simple_false hfr φ hφ hZφ S hnab hSc (Or.inr ⟨5, inferInstance,
        fun h => hn5 (h.trans hdiv), ?_⟩)
      refine sylow_prop_of_equiv eP fun P => ⟨(hs5 P).1, by rw [(hs5 P).2]; norm_num, ?_⟩
      rw [(hs5 P).2, hc]; norm_num [Nat.factorial]

end Main

end

end CFSGOutside.Gagola
