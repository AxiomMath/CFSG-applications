import Mathlib
import CFSGOutside.Corpus.DicksonPsl2
import CFSGOutside.Corpus.BurnsidePQ
import CFSGOutside.GaloisMinimalDegree.Basic
import CFSGOutside.LoefflerPsl2Sections.Defs

/-!
# Nonabelian simple sections of `PSL₂(𝔽_q)`

D. Loeffler, *Images of adelic Galois representations for modular forms*, Glasgow Math. J. 59 (2017),
Lemma 1.1.2 (finite part): a nonabelian finite simple section of `PSL₂(k)`, with `k` of characteristic `p`,
is isomorphic to `A₅` or to `PSL₂(F)` for a finite field `F` of characteristic `p` with `#F ≥ 4`.
We prove the sharper statement that `F` is a subfield of `k`. Conditional on Dickson's classification and
Burnside's `p^a q^b` theorem, stated as classes in `CFSGOutside.Corpus`.
-/

open CFSGOutside.Corpus

namespace CFSGOutside.LoefflerPsl2Sections

lemma isSolvable_of_card_dvd [BurnsidePQ.{0}] (X : Type) [Group X] [Finite X] (h : Nat.card X ∣ 48) : Group.IsSolvable X := by
  have key : ∀ d < 49, d ∣ 48 → ∃ a < 5, ∃ b < 2, d = 2 ^ a * 3 ^ b := by decide
  obtain ⟨a, -, b, -, hab⟩ := key _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) h)) h
  haveI := Fintype.ofFinite X
  exact BurnsidePQ.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hab)

lemma not_nonab_of_solvable {X Q : Type} [Group X] [Group Q] [IsSimpleGroup Q] (π : X →* Q)
    (hπ : Function.Surjective π) (hX : Group.IsSolvable X) (hnonab : ∃ a b : Q, a * b ≠ b * a) : False := by
  haveI := hX
  haveI := solvable_of_surjective hπ
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr this) a b)

lemma isSolvable_of_cyclic (G : Type) [Group G] [IsCyclic G] : Group.IsSolvable G := by
  exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup (α := G)).mul_comm a b

def sgn (z : ℕ) : DihedralGroup z →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;> simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr] <;> decide

def rot (z : ℕ) : Multiplicative (ZMod z) →* DihedralGroup z where
  toFun i := DihedralGroup.r i.toAdd
  map_one' := rfl
  map_mul' a b := by simp [DihedralGroup.r_mul_r]

lemma isSolvable_dihedral (z : ℕ) : Group.IsSolvable (DihedralGroup z) := by
  refine solvable_of_ker_le_range (rot z) (sgn z) ?_
  intro x hx
  cases x with
  | r i => exact ⟨Multiplicative.ofAdd i, rfl⟩
  | sr i =>
    exfalso
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.ofAdd (1 : ZMod 2) = 1 at hx
    have h1 := congrArg Multiplicative.toAdd hx
    change (1 : ZMod 2) = 0 at h1
    exact absurd h1 (by decide)

lemma simple_quot {X Q : Type} [Group X] [Group Q] [IsSimpleGroup X] (π : X →* Q)
    (hπ : Function.Surjective π) (hnonab : ∃ a b : Q, a * b ≠ b * a) : Nonempty (X ≃* Q) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp h, hπ⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    have hx : π x = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
    have hy : π y = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
    exact hab (by rw [hx, hy])

lemma central_quot {S Q : Type} [Group S] [Group Q] [IsSimpleGroup Q] [IsSimpleGroup (S ⧸ Subgroup.center S)]
    (ψ : S →* Q) (hψ : Function.Surjective ψ) (hnonab : ∃ a b : Q, a * b ≠ b * a) :
    Nonempty (Q ≃* S ⧸ Subgroup.center S) := by
  have hZ : Subgroup.center S ≤ ψ.ker := by
    haveI hn : ((Subgroup.center S).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center S).map ψ) with h | h
    · intro z hz
      rw [MonoidHom.mem_ker]
      have : ψ z ∈ (Subgroup.center S).map ψ := ⟨z, hz, rfl⟩
      rw [h] at this
      simpa using this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ (Subgroup.center S).map ψ := h ▸ Subgroup.mem_top a
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hψ b
      exact hab (by rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y])
  have hker : ψ.ker = Subgroup.center S := by
    haveI hn : (ψ.ker.map (QuotientGroup.mk' (Subgroup.center S))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map (QuotientGroup.mk' (Subgroup.center S))) with h | h
    · refine le_antisymm ?_ hZ
      intro k hk
      have : QuotientGroup.mk' (Subgroup.center S) k ∈ ψ.ker.map (QuotientGroup.mk' (Subgroup.center S)) :=
        ⟨k, hk, rfl⟩
      rw [h] at this
      simpa [QuotientGroup.eq_one_iff] using this
    · exfalso
      have htop : ψ.ker = ⊤ := by
        rw [eq_top_iff]
        intro s _
        have : QuotientGroup.mk' (Subgroup.center S) s ∈ ψ.ker.map (QuotientGroup.mk' (Subgroup.center S)) :=
          h ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hks⟩ := this
        have : k⁻¹ * s ∈ Subgroup.center S := by
          rw [← QuotientGroup.eq]; exact hks
        have := hZ this
        have := ψ.ker.mul_mem hk this
        simpa using this
      obtain ⟨a, b, hab⟩ := hnonab
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : ψ x = 1 := by rw [← MonoidHom.mem_ker, htop]; trivial
      have hy : ψ y = 1 := by rw [← MonoidHom.mem_ker, htop]; trivial
      exact hab (by rw [hx, hy])
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

lemma exists_sl_of_det_one {F : Type} [Field F] (B : GL (Fin 2) F)
    (h : Matrix.GeneralLinearGroup.det B = 1) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F, Matrix.SpecialLinearGroup.toGL t = B := by
  refine ⟨⟨B.1, ?_⟩, ?_⟩
  · have := congrArg Units.val h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  · first | exact Units.ext rfl | (ext i j; rfl)

lemma pgl_quot {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) {Q : Type} [Group Q] [IsSimpleGroup Q]
    (π : Matrix.ProjGenLinGroup (Fin 2) F →* Q) (hπ : Function.Surjective π)
    (hnonab : ∃ a b : Q, a * b ≠ b * a) : Nonempty (Q ≃* PSL2 F) := by
  haveI : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let φ : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL
  let ψ := π.comp φ
  have hψ : Function.Surjective ψ := by
    haveI hKn : ψ.range.Normal := by
      refine ⟨fun k hk q => ?_⟩
      obtain ⟨s, rfl⟩ := hk
      obtain ⟨g, rfl⟩ := hπ q
      obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
      have hd : Matrix.GeneralLinearGroup.det (A * Matrix.SpecialLinearGroup.toGL s * A⁻¹) = 1 := by
        have : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL s) = 1 := by
          ext; simp [Matrix.GeneralLinearGroup.val_det_apply]
        rw [map_mul, map_mul, this, mul_one, map_inv, mul_inv_cancel]
      obtain ⟨t, ht⟩ := exists_sl_of_det_one _ hd
      refine ⟨t, ?_⟩
      have key : φ t = Matrix.ProjGenLinGroup.mk A * φ s * (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
        simp only [φ, MonoidHom.comp_apply, ht, map_mul, map_inv]
      simp only [ψ, MonoidHom.comp_apply, key, map_mul, map_inv]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.range with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
      obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
      have hd : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact mul_comm _ _
      obtain ⟨t, ht⟩ := exists_sl_of_det_one _ hd
      have h1 : ψ t = 1 := by
        have : ψ t ∈ ψ.range := ⟨t, rfl⟩
        rw [h] at this; simpa using this
      apply hab
      have : ψ t = π (Matrix.ProjGenLinGroup.mk A) * π (Matrix.ProjGenLinGroup.mk B) *
          (π (Matrix.ProjGenLinGroup.mk A))⁻¹ * (π (Matrix.ProjGenLinGroup.mk B))⁻¹ := by
        simp only [ψ, φ, MonoidHom.comp_apply, ht, map_mul, map_inv]
      rw [h1] at this
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this.symm)
    · exact MonoidHom.range_eq_top.mp h
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := this
  exact central_quot ψ hψ hnonab


/-- **Loeffler, Lemma 1.1.2.** Let `F` be a finite field with `p ^ f` elements. A nonabelian simple section `Y / N`
of `PSL₂(F)` is isomorphic to `A₅` or to `PSL₂(𝔽_{p^m})` for some `m` dividing `f` with `p ^ m ≥ 4`.

Source: D. Loeffler, Images of adelic Galois representations for modular forms, Glasgow Math. J. 59 (2017), 11–25,
Lemma 1.1.2. The published lemma gives a field of characteristic `p`; here it is a subfield of `F`. -/
theorem loeffler_simple_section [DicksonPsl2SubgroupClassification.{0}] [BurnsidePQ.{0}] {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (Y : Subgroup (PSL2 F)) (N : Subgroup Y) [N.Normal]
    [IsSimpleGroup (Y ⧸ N)] (hnonab : ∃ a b : Y ⧸ N, a * b ≠ b * a) :
    Nonempty (Y ⧸ N ≃* alternatingGroup (Fin 5)) ∨
      ∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ 4 ≤ p ^ m ∧ Nonempty (Y ⧸ N ≃* PSL2 (GaloisField p m)) := by
  have hπ := QuotientGroup.mk'_surjective N
  let π := QuotientGroup.mk' N
  rcases DicksonPsl2SubgroupClassification.huppert_II_8_27_dickson_psl2_subgroup_classification hF Y with
    hEA | ⟨z, -, -, hC⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, -, M, C, hM, hMe, -, hCc, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf2, ⟨e⟩⟩
  · exfalso
    haveI := hEA.toIsMulCommutative
    exact not_nonab_of_solvable π hπ (Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b)
      hnonab
  · exfalso
    haveI := hC
    exact not_nonab_of_solvable π hπ (isSolvable_of_cyclic _) hnonab
  · exfalso
    haveI := isSolvable_dihedral z
    exact not_nonab_of_solvable π hπ (solvable_of_solvable_injective (f := e.toMonoidHom) e.injective) hnonab
  · exfalso
    have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card]
      convert (card_alternatingGroup (α := Fin 4)).trans (by decide : (Fintype.card (Fin 4)).factorial / 2 = 12)
    exact not_nonab_of_solvable π hπ
      (isSolvable_of_card_dvd Y (by rw [Nat.card_congr e.toEquiv, hc]; norm_num)) hnonab
  · exfalso
    have hc : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    exact not_nonab_of_solvable π hπ
      (isSolvable_of_card_dvd Y (by rw [Nat.card_congr e.toEquiv, hc]; norm_num)) hnonab
  · left
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    obtain ⟨e'⟩ := simple_quot (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective) hnonab
    exact ⟨e'.symm⟩
  · exfalso
    haveI := hM
    haveI := hMe.toIsMulCommutative
    haveI : Group.IsSolvable M := Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
    haveI : IsCyclic C := hCc
    haveI : Group.IsSolvable C := isSolvable_of_cyclic _
    let g : C →* Y ⧸ M := (QuotientGroup.mk' M).comp C.subtype
    have hg : Function.Surjective g := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy : y ∈ ((C ⊔ M : Subgroup Y) : Set Y) := by
        rw [sup_comm, hsup]; trivial
      rw [Subgroup.mul_normal] at hy
      obtain ⟨c, hc, m', hm', rfl⟩ := hy
      refine ⟨⟨c, hc⟩, ?_⟩
      show QuotientGroup.mk c = QuotientGroup.mk (c * m')
      rw [QuotientGroup.eq]
      have : c⁻¹ * (c * m') = m' := by group
      rw [this]
      exact hm'
    haveI : Group.IsSolvable (Y ⧸ M) := solvable_of_surjective hg
    haveI : Group.IsSolvable Y := solvable_of_ker_le_range M.subtype (QuotientGroup.mk' M) (by
      intro x hx
      exact ⟨⟨x, by simpa using hx⟩, rfl⟩)
    exact not_nonab_of_solvable π hπ inferInstance hnonab
  · have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    by_cases h4 : 4 ≤ p ^ m
    · right
      haveI : IsSimpleGroup (PSL2 (GaloisField p m)) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      obtain ⟨e'⟩ := simple_quot (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective) hnonab
      exact ⟨m, hm, hmf, h4, ⟨e'.symm⟩⟩
    · exfalso
      have hq : 2 ≤ p ^ m := by
        have := (Fact.out : p.Prime).one_lt
        calc 2 ≤ p := this
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      have hd := CFSGOutside.Psl2Basic.card_psl2_dvd' (GaloisField p m)
      rw [hcard] at hd
      have : p ^ m = 2 ∨ p ^ m = 3 := by omega
      refine not_nonab_of_solvable π hπ (isSolvable_of_card_dvd Y ?_) hnonab
      rw [Nat.card_congr e.toEquiv]
      rcases this with h | h <;> rw [h] at hd <;> exact hd.trans (by norm_num)
  · have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    by_cases h4 : 4 ≤ p ^ m
    · right
      obtain ⟨e'⟩ := pgl_quot (F := GaloisField p m) (by omega)
        (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective) hnonab
      exact ⟨m, hm, (dvd_mul_left m 2).trans hmf2, h4, ⟨e'⟩⟩
    · exfalso
      have hq : 2 ≤ p ^ m := by
        have := (Fact.out : p.Prime).one_lt
        calc 2 ≤ p := this
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      have hd := CFSGOutside.Psl2Basic.card_pgl2_dvd' (GaloisField p m)
      rw [hcard] at hd
      have : p ^ m = 2 ∨ p ^ m = 3 := by omega
      refine not_nonab_of_solvable π hπ (isSolvable_of_card_dvd Y ?_) hnonab
      rw [Nat.card_congr e.toEquiv]
      rcases this with h | h <;> rw [h] at hd <;> exact hd.trans (by norm_num)

end CFSGOutside.LoefflerPsl2Sections
