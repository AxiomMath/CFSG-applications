import CFSGOutside.Corpus.HallPaige.Th
import CFSGOutside.HallPaige.Sporadic.Ly.Criterion
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import CFSGOutside.HallPaige.Sporadic.Th.C0
import CFSGOutside.HallPaige.Sporadic.Th.C1
import CFSGOutside.HallPaige.Sporadic.Th.C2
import CFSGOutside.HallPaige.Sporadic.Th.C3
import CFSGOutside.HallPaige.Sporadic.Th.C4
import CFSGOutside.HallPaige.Sporadic.Th.C5
import CFSGOutside.HallPaige.Sporadic.Th.C6
import CFSGOutside.HallPaige.Sporadic.Th.C7
import CFSGOutside.HallPaige.Sporadic.Th.C8
import CFSGOutside.HallPaige.Sporadic.Th.C9
import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Transport

/-!
# The Thompson group `Th`

`Th` acts on the 283599225 cosets of the Dempwolff group `2⁵·L₅(2)`. In the corpus 248-dimensional model
`J ≤ GL₂₄₈(𝔽₂)` this is the orbit of the subspace `u = sp (U0 dempData)`; the corpus theorems
`suborbitHyp` and `SuborbitHyp.cover` give that its stabilizer is the Dempwolff group `Dg = ⟨d₀, d₁⟩` and
that every point of the orbit lies in the `Dg`-orbit of `u` or of one of the ten representatives
`sp (pt dempData orbData i) = gᵢ⁻¹ • u`, `gᵢ` the word `orbData.words i` in the registers.

Each double coset `Dg gᵢ⁻¹ Dg` has a triangle witness (`Sporadic/Ly/Criterion.lean`): an element
`h ∈ Dg` (a product of chain transversal elements) with `(h * gᵢ)³ ∈ Dg`, so that `x = (h * gᵢ)⁻¹` lies in
the double coset and `x³ ∈ Dg`. The ten checks `(h * gᵢ)³ • u = u` are kernel computations with packed
5-row products (`Sporadic/Th/C0.lean` … `C9.lean`). `Dg` is good: two commuting involutions of its
normal `2⁵` (`Sporadic/Th/Defs.lean`). `J ≃* Th` from the corpus `nonempty_mulEquiv`.
-/

namespace CFSGOutside.HallPaige.Th

open MulAction DoubleCoset CFSGOutside.Corpus.Th CFSGOutside.Corpus.Th.KC.Th
  CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Th.Spec CFSGOutside.Corpus.Th.KC.ThDemp
  CFSGOutside.Corpus.Th.KC.Loop
  CFSGOutside.Corpus.Th.Certificates.ThDemp CFSGOutside.Corpus.Th.Certificates.ThDemp.Act
  CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab CFSGOutside.Corpus.Th.Certificates.ThDemp.Pts
  CFSGOutside.Corpus.Th.Sporadic.Th CFSGOutside.Corpus.Th.KernelThDemp CFSGOutside.HallPaige.Ly

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

set_option maxRecDepth 100000

/-! ### Group-theoretic lemmas -/

section Generic

variable {G : Type*} [Group G]

/-- An element `x` of `H r H` with `x ^ 3 ∈ H` is a triangle witness: `(x * x)⁻¹ = x * (x ^ 3)⁻¹`. -/
theorem triWit_of_cube' {H : Subgroup G} {x r : G} (hx : mk H H x = mk H H r) (h3 : x ^ 3 ∈ H) :
    TriWit H r := by
  refine ⟨x, x, hx, hx, Or.inr ?_⟩
  have e : (x * x)⁻¹ = x * (x ^ 3)⁻¹ := by group
  rw [e, mk_mul_right_of_mem (H.inv_mem h3), hx]

/-- Two involutions `u, v` with `u * v` an involution generate a Klein four-group (as in
`Sporadic/Ly.lean`). -/
theorem isGood_of_three [Finite G] (K : Subgroup G) {u v : G}
    (hu : u ∈ K) (hv : v ∈ K) (u2 : u * u = 1) (v2 : v * v = 1) (uv2 : u * v * (u * v) = 1)
    (u1 : u ≠ 1) (v1 : v ≠ 1) (uv1 : u * v ≠ 1) : IsGood K := by
  have huv : u * v = v * u := by
    have h1 := eq_inv_of_mul_eq_one_left uv2
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right u2, inv_eq_of_mul_eq_one_right v2] at h1
    exact h1
  have hne : u ≠ v := by
    rintro rfl
    exact uv1 u2
  exact Subgroup.isGood_of_commuting_involutions K hu hv (by rw [pow_two]; exact u2)
    (by rw [pow_two]; exact v2) huv u1 v1 hne

end Generic

/-! ### Matrices and subspaces -/

section Mat

variable {H : Subgroup (GL (Fin 248) (ZMod 2))}

theorem mat_one : 𝕄 (1 : H) = 1 := rfl

theorem mat_prod (l : List H) : 𝕄 l.prod = (l.map fun g => 𝕄 g).prod := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.prod_cons, mat_mul', ih, List.map_cons, List.prod_cons]

theorem eq_one_of_mat {x : H} (h : 𝕄 x = 1) : x = 1 := Subtype.ext (Units.ext h)

/-- A subspace mapped into itself by an element of `GL₂₄₈(𝔽₂)` is fixed by it. -/
theorem smul_eq_of_le (x : H) (W : Pts) (h : x • W ≤ W) : x • W = W := by
  have e : ((x • W : Pts) : Set V) = (fun v => Matrix.vecMul v (𝕄 x⁻¹)) '' (W : Set V) := by
    rw [smul_eq_mapM, mapM, Submodule.map_coe]
    rfl
  have hinj : Function.Injective (fun v : V => Matrix.vecMul v (𝕄 x⁻¹)) := by
    intro v w hvw
    have h2 := congrArg (fun z => Matrix.vecMul z (𝕄 x)) hvw
    simp only [Matrix.vecMul_vecMul, mat_inv_mul, Matrix.vecMul_one] at h2
    exact h2
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr h) ?_ (Set.toFinite _)
  exact le_of_eq (by rw [e, Set.ncard_image_of_injective _ hinj])

end Mat

section Corpus

variable [Theorems]

theorem hF : DempFacts dempData := Theorems.dempChk_facts dempData Theorems.demp_chk

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem wordR_eq (D : DempData) (cn : ℕ) :
    ∀ (w : List ℕ) (X : ℕ), wordR D cn X w = w.foldl (fun S r => mulB cn D.rm S (D.RB r)) X
  | [], _ => rfl
  | r :: w, X => by
    show strictN (mulB cn D.rm X (D.RB r)) (fun S => wordR D cn S w) = _
    rw [strictN_eq]
    exact wordR_eq D cn w _

theorem pt_eq (i : ℕ) : pt dempData orbData i = blk (U0 dempData) (gMats i) := by
  rw [pt, wordR_eq, gMats, blk, List.foldl_map, rm_eq]
  rfl

theorem sp_blk (P : ℕ) (ms : List ℕ) : sp (blk P ms) = mapM (ms.map pkMat).prod (sp P) := by
  induction ms generalizing P with
  | nil => exact (mapM_one _).symm
  | cons N ms ih =>
    show sp (blk (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) ms) = _
    rw [ih, Theorems.sp_mulB, List.map_cons, List.prod_cons, mapM_mul]

theorem mat_word {J' : Subgroup (GL (Fin 248) (ZMod 2))} (xr : ℕ → J')
    (hxr : ∀ r, 0 < r → r < dempData.nreg → 𝕄 (xr r) = pkMat (dempData.RB r)) :
    ∀ w : List ℕ, (∀ r ∈ w, 0 < r ∧ r < dempData.nreg) →
      𝕄 (w.map xr).prod = ((w.map dempData.RB).map pkMat).prod
  | [], _ => rfl
  | r :: w, hw => by
    have h0 := hw r List.mem_cons_self
    rw [List.map_cons, List.prod_cons, mat_mul', hxr r h0.1 h0.2,
      mat_word xr hxr w fun r' h' => hw r' (List.mem_cons_of_mem r h')]
    simp only [List.map_cons, List.prod_cons]

/-- A passed witness check: the element with matrix `∏ ms` fixes `u` (up to inversion). -/
theorem fix_of_chk {J' : Subgroup (GL (Fin 248) (ZMod 2))} {g : J'} {ms : List ℕ}
    (hm : (ms.map pkMat).prod = 𝕄 g) {code : ℕ}
    (hc : combChk (2 ^ 248 - 1) (blk (U0 dempData) ms) (U0 dempData) code = true) :
    g⁻¹ • sp (U0 dempData) = sp (U0 dempData) := by
  have hle := Theorems.sp_le_of_combChk hc
  rw [sp_blk, hm, ← inv_smul_eq] at hle
  exact smul_eq_of_le _ _ hle

/-- The chain of checks for one representative, given the chain data and the registers. -/
theorem triWit_rep {J' : Subgroup (GL (Fin 248) (ZMod 2))} (K : Subgroup J')
    (u : Pts) (hu : u = sp (U0 dempData)) (hK : stabilizer J' u = K)
    (t : ℕ → ℕ → J') (ht : ∀ l < 6, ∀ i < dempData.oszL l, t l i ∈ K ∧
      𝕄 (t l i) = pkMat (dempData.T l i))
    (xr : ℕ → J') (hxr : ∀ r, 0 < r → r < dempData.nreg → 𝕄 (xr r) = pkMat (dempData.RB r))
    (i : ℕ) (hi : i < 10)
    (hc : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats i (wY i))) (U0 dempData) (wC i) =
      true) :
    TriWit K ((lgetL orbData.words i).map xr).prod⁻¹ := by
  set g : J' := ((lgetL orbData.words i).map xr).prod with hg
  set y := wY i
  have hT : ∀ l < 6, t l (y.getD l 0) ∈ K ∧ 𝕄 (t l (y.getD l 0)) = pkMat (dempData.T l (y.getD l 0)) :=
    fun l hl => ht l hl _ (wY_lt i hi l hl)
  set h : J' := [t 5 (y.getD 5 0), t 4 (y.getD 4 0), t 3 (y.getD 3 0), t 2 (y.getD 2 0),
    t 1 (y.getD 1 0), t 0 (y.getD 0 0)].prod with hh
  have hhK : h ∈ K := by
    rw [hh]
    refine K.list_prod_mem ?_
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hT 5 (by norm_num)).1
    · exact (hT 4 (by norm_num)).1
    · exact (hT 3 (by norm_num)).1
    · exact (hT 2 (by norm_num)).1
    · exact (hT 1 (by norm_num)).1
    · exact (hT 0 (by norm_num)).1
  have mh : 𝕄 h = ((hMats y).map pkMat).prod := by
    rw [hh, mat_prod]
    simp only [List.map_cons, List.map_nil, hMats]
    rw [(hT 5 (by norm_num)).2, (hT 4 (by norm_num)).2, (hT 3 (by norm_num)).2,
      (hT 2 (by norm_num)).2, (hT 1 (by norm_num)).2, (hT 0 (by norm_num)).2]
  have mg : 𝕄 g = ((gMats i).map pkMat).prod := mat_word xr hxr _ (words_lt i hi)
  have mz : ((cubeMats i y).map pkMat).prod = 𝕄 (g * h * g * h * g) := by
    rw [mat_mul', mat_mul', mat_mul', mat_mul', mg, mh, cubeMats]
    simp only [List.map_append, List.prod_append, mul_assoc]
  have hz := fix_of_chk mz hc
  have hzK : (g * h * g * h * g)⁻¹ ∈ K := by
    rw [← hK, mem_stabilizer_iff, hu]
    exact hz
  have h3 : (h * g) ^ 3 ∈ K := by
    have e : (h * g) ^ 3 = h * (g * h * g * h * g) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact K.mul_mem hhK (by simpa using K.inv_mem hzK)
  refine triWit_of_cube' (x := (h * g)⁻¹) ?_ (by rw [inv_pow]; exact K.inv_mem h3)
  rw [mul_inv_rev]
  exact mk_mul_right_of_mem (K.inv_mem hhK) g⁻¹

/-- The model `J` is isomorphic to the presented group `Th`. -/
theorem nonempty_mulEquiv : Nonempty (J ≃* TauCeti.SporadicName.Th.Group) := by
  obtain ⟨e⟩ := Theorems.nonempty_mulEquiv
  exact ⟨(Blueprint.NativeSporadic.matrixSeedEquiv 2 248 (by norm_num) matA matB
    matA_det_ne_zero matB_det_ne_zero).symm.trans e⟩

theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [Theorems.card_J]; norm_num)

/-- **The Wilcox criterion for the 248-dimensional model of `Th`.** -/
theorem wilcoxCriterion_J [Generic.{0, 0}] : WilcoxCriterion J := by
  haveI := finite_J
  have hF := hF
  have hk := hF.consts
  obtain ⟨hreg, d₀, d₁, hd₀, hd₁, t, ht, huniq, hDc, hlev5⟩ :=
    Theorems.exists_chain hF (a := a) (b := b) (by rw [a_val, Theorems.pkMat_SA])
      (by rw [b_val, Theorems.pkMat_SB])
  have hinv := Theorems.invChk_sound Theorems.orb_checks.inv
  let C : Ctx dempData orbData J :=
    { d₀ := d₀
      d₁ := d₁
      t := t
      mem := fun l hl i hi => (ht l hl i hi).1
      mat := fun l hl i hi => (ht l hl i hi).2
      uniq := huniq
      inv := fun l hl i hi => by
        have hi64 : i < 64 := by
          obtain ⟨o0, o1, o2, -⟩ := hF.osz
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> omega
        have e := congrArg pkMat (hinv l hl i hi hi64)
        rw [DempData.mul, Theorems.pkMat_mulB hk, Theorems.pkMat_one hk,
          ← (ht l (by omega) i hi).2] at e
        calc pkMat (orbData.TI l i) = (𝕄 (t l i)⁻¹ * 𝕄 (t l i)) * pkMat (orbData.TI l i) := by
              rw [mat_inv_mul, Matrix.one_mul]
          _ = 𝕄 (t l i)⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
      osz := hF.osz
      md₀ := hd₀
      md₁ := hd₁
      lev5 := hlev5 }
  have H := Theorems.suborbitHyp C hF hreg Theorems.orb_checks Theorems.card_J.le hDc
  obtain ⟨hstab, hcov⟩ := Generic.cover H
  choose! xr hxr using hreg
  set u : Pts := sp (U0 dempData) with hu
  let g : ℕ → J := fun i => ((lgetL orbData.words i).map xr).prod
  let r : Fin 11 → J := Fin.cases 1 fun j => (g j)⁻¹
  have hr : ∀ i, r i • u = OrbMain.pts u (fun i : Fin 10 => sp (pt dempData orbData i)) i := by
    intro i
    induction i using Fin.cases with
    | zero =>
      show (1 : J) • u = u
      rw [one_smul]
    | succ j =>
      show (g j)⁻¹ • u = sp (pt dempData orbData j)
      have mg : 𝕄 (g j) = ((gMats j).map pkMat).prod := mat_word xr hxr _ (words_lt j j.isLt)
      rw [inv_smul_eq, mg, pt_eq, sp_blk]
  have hgood : IsGood C.Dg := by
    have hU := ht 5 (by norm_num) 1 (by rw [hF.osz.2.2.2.2.2]; norm_num)
    have hV := ht 5 (by norm_num) 2 (by rw [hF.osz.2.2.2.2.2]; norm_num)
    have mulE : ∀ x y : J, ∀ X Y : ℕ, 𝕄 x = pkMat X → 𝕄 y = pkMat Y →
        𝕄 (x * y) = pkMat (dempData.mul X Y) := fun x y X Y hx hy => by
      rw [mat_mul', hx, hy, DempData.mul, Theorems.pkMat_mulB hk]
    have oneE : ∀ x : J, ∀ X : ℕ, 𝕄 x = pkMat X → X = dempData.ONE → x = 1 := fun x X hx hX =>
      eq_one_of_mat (by rw [hx, hX, Theorems.pkMat_one hk])
    have neE : ∀ x : J, ∀ X : ℕ, ∀ k : Fin 248, 𝕄 x = pkMat X → X.testBit (256 * k.val + k.val) = false →
        x ≠ 1 := fun x X k hx hb h1 => by
      have e := congrFun (congrFun hx k) k
      rw [h1, mat_one] at e
      simp [pkMat, hb] at e
    have mUV := mulE _ _ _ _ hU.2 hV.2
    refine isGood_of_three C.Dg hU.1 hV.1 (oneE _ _ (mulE _ _ _ _ hU.2 hU.2) chkU)
      (oneE _ _ (mulE _ _ _ _ hV.2 hV.2) chkV) (oneE _ _ (mulE _ _ _ _ mUV mUV) chkUV)
      (neE _ _ 1 hU.2 bitU) (neE _ _ 1 hV.2 bitV) (neE _ _ 0 mUV bitUV)
  have hne : C.Dg ≠ ⊤ := by
    intro htop
    have h1 := hDc
    change Nat.card C.Dg = 319979520 at h1
    rw [htop, Subgroup.card_top, Theorems.card_J] at h1
    norm_num at h1
  refine wilcoxCriterion_of_cover u r (by rw [hstab]; exact hne) (by rw [hstab]; exact hgood)
    (fun x => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hcov (x • u) (mem_orbit u x)
    exact ⟨i, by rw [hstab, hr]; exact hi⟩
  · rw [hstab]
    induction i using Fin.cases with
    | zero => exact triWit_one _
    | succ j =>
      have hw : ∀ j : Fin 10, combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats j (wY j)))
          (U0 dempData) (wC j) = true := by
        intro j
        fin_cases j
        exacts [chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9]
      exact triWit_rep C.Dg u hu hstab t (fun l hl i hi => ht l hl i hi) xr hxr j j.isLt (hw j)

theorem psa_J (hP : ProperSubgroupsAdmissible TauCeti.SporadicName.Th.Group) :
    ProperSubgroupsAdmissible J := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  exact ProperSubgroupsAdmissible.of_mulEquiv e.symm hP

theorem hasCompleteMapping_J [Generic.{0, 0}] (hPJ : ProperSubgroupsAdmissible J) :
    HasCompleteMapping J :=
  @hasCompleteMapping_of_wilcoxCriterion J _ finite_J cosetStatement wilcoxCriterion_J hPJ

/-- Transport of complete mappings, with the isomorphism in the other direction. -/
theorem hasCompleteMapping_of_mulEquiv_symm {G H : Type} [Group G] [Group H] (e : H ≃* G)
    (h : HasCompleteMapping G) : HasCompleteMapping H :=
  HasCompleteMapping.of_mulEquiv e.symm h

theorem hasCompleteMapping_of_J (hJ : HasCompleteMapping J) :
    HasCompleteMapping TauCeti.SporadicName.Th.Group := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  exact @hasCompleteMapping_of_mulEquiv_symm _ (↥J) TauCeti.SporadicName.Th.Group (Subgroup.toGroup J) _
    e.symm hJ

/-- `Th` has a complete mapping if its proper good subgroups do. -/
theorem hasCompleteMapping_Th [Generic.{0, 0}]
    (hP : ProperSubgroupsAdmissible TauCeti.SporadicName.Th.Group) :
    HasCompleteMapping TauCeti.SporadicName.Th.Group :=
  hasCompleteMapping_of_J (hasCompleteMapping_J (psa_J hP))

end Corpus

end CFSGOutside.HallPaige.Th

namespace CFSGOutside.HallPaige

open CFSGOutside.Corpus.Th

/-- **The catalogue case of `Th`.** -/
theorem catalogueCase_Th [Theorems] [Generic.{0, 0}] : CatalogueCase (.sporadic .Th) :=
  fun _ hP => Th.hasCompleteMapping_Th hP

end CFSGOutside.HallPaige
