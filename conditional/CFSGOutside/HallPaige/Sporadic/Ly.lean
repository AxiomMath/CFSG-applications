import CFSGOutside.HallPaige.Sporadic.Ly.Criterion
import CFSGOutside.HallPaige.Sporadic.Ly.Words
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Transport

/-!
# The Lyons group `Ly`

`Ly` acts on the 8835156 cosets of `G₂(5)`; in the corpus 111-dimensional model `J` this is the
orbit `Ω` of `opE`, with stabilizer `lyH ≅ G₂(5)`, and the corpus theorem `F1_all` lists the five
`lyH`-orbits on `Ω` (sizes 1, 19530, 968750, 2034375, 5812500) with representatives `gRep i`.
Triangle witnesses for the Wilcox criterion (`Sporadic/Ly/Criterion.lean`):

* the three smaller double cosets: `g = h * gRep i` with `h` a word in `lyH` and `g ^ 3 = 1`,
  checked in the kernel with packed matrices (`Sporadic/Ly/Words.lean`);
* the largest: counting, `2 · 5812500 > 8835156`.

`lyH` is good: two commuting involutions, checked the same way. `J ≃* Ly` from the corpus
homomorphism `bridge_hom` and the order bound `finite_card_le`.
-/

namespace CFSGOutside.HallPaige.Ly

open MulAction CFSGOutside.Corpus.Ly

set_option maxRecDepth 100000

/-- `wilcoxCriterion_of_cover` with the stabilizer named. -/
theorem wilcoxCriterion_of_cover' {G X : Type*} [Group G] [MulAction G X] (x₀ : X)
    (H : Subgroup G) (hH : stabilizer G x₀ = H) {ι : Type*} (r : ι → G)
    (hne : H ≠ ⊤) (hgood : IsGood H) (hcov : ∀ g : G, ∃ i, g • x₀ ∈ orbit H (r i • x₀))
    (hw : ∀ i, TriWit H (r i)) : WilcoxCriterion G := by
  subst hH
  exact wilcoxCriterion_of_cover x₀ r hne hgood hcov hw

/-- Witness words in `lyH` for the double cosets of `gRep 1`, `gRep 2`, `gRep 3`. -/
def hW : ℕ → List ℕ
  | 1 => [13, 10, 10, 13, 12, 2, 2]
  | 2 => [2, 12, 10, 6, 6, 2, 11]
  | _ => [5, 11, 2, 13, 13, 13]

/-- The words for the two commuting involutions of `lyH`. -/
def uW : List ℕ := [11, 11, 11, 11]

def vW : List ℕ :=
  [11, 11, 11, 11, 3, 3, 11, 11, 11, 11, 10, 10, 11, 11, 11, 11, 3, 3, 11, 11, 11, 11, 10, 10]

/-! ### Kernel checks -/

theorem chk1 : Nat.beq (pw BC.ONEF ((hW 1 ++ WG1.map abL) ++ (hW 1 ++ WG1.map abL) ++
    (hW 1 ++ WG1.map abL))) BC.ONEF = true := by decide +kernel

theorem chk2 : Nat.beq (pw BC.ONEF ((hW 2 ++ WG2.map abL) ++ (hW 2 ++ WG2.map abL) ++
    (hW 2 ++ WG2.map abL))) BC.ONEF = true := by decide +kernel

theorem chk3 : Nat.beq (pw BC.ONEF ((hW 3 ++ WG3.map abL) ++ (hW 3 ++ WG3.map abL) ++
    (hW 3 ++ WG3.map abL))) BC.ONEF = true := by decide +kernel

theorem chkU2 : Nat.beq (pw BC.ONEF (uW ++ uW)) BC.ONEF = true := by decide +kernel

theorem chkV2 : Nat.beq (pw BC.ONEF (vW ++ vW)) BC.ONEF = true := by decide +kernel

theorem chkUV2 : Nat.beq (pw BC.ONEF ((uW ++ vW) ++ (uW ++ vW))) BC.ONEF = true := by
  decide +kernel

theorem chkU : pw BC.ONEF uW % 2 ^ 12 = 3 := by decide +kernel

theorem chkV : pw BC.ONEF vW % 2 ^ 12 = 3 := by decide +kernel

theorem chkUV : pw BC.ONEF (uW ++ vW) % 2 ^ 12 = 4 := by decide +kernel

theorem lt_u : ∀ k ∈ uW, k < 14 := by decide
theorem lt_v : ∀ k ∈ vW, k < 14 := by decide
theorem lt_uv : ∀ k ∈ uW ++ vW, k < 14 := by decide
theorem lt_uu : ∀ k ∈ uW ++ uW, k < 14 := by decide
theorem lt_vv : ∀ k ∈ vW ++ vW, k < 14 := by decide
theorem lt_uvuv : ∀ k ∈ (uW ++ vW) ++ (uW ++ vW), k < 14 := by decide
theorem mem_u : ∀ k ∈ uW, (2 ≤ k ∧ k ≤ 6) ∨ (9 ≤ k ∧ k ≤ 13) := by decide
theorem mem_v : ∀ k ∈ vW, (2 ≤ k ∧ k ≤ 6) ∨ (9 ≤ k ∧ k ≤ 13) := by decide

/-- Two involutions `u, v` with `u * v` an involution generate a Klein four-group. -/
theorem isGood_of_three {G : Type*} [Group G] [Finite G] (K : Subgroup G) {u v : G}
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

section

variable [Theorems] [LySeed]

theorem gRep_eq (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 4) :
    gRep i = wJ (([WG1, WG2, WG3, WG4].getD (i - 1) []).map abL) := by
  unfold gRep
  apply abWord_eq
  obtain ⟨h1, h2⟩ := hi
  interval_cases i <;> decide

theorem triWit_small (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 3)
    (hc : Nat.beq (pw BC.ONEF ((hW i ++ ([WG1, WG2, WG3, WG4].getD (i - 1) []).map abL) ++
      (hW i ++ ([WG1, WG2, WG3, WG4].getD (i - 1) []).map abL) ++
      (hW i ++ ([WG1, WG2, WG3, WG4].getD (i - 1) []).map abL))) BC.ONEF = true) :
    TriWit lyH (gRep i) := by
  set w := hW i ++ ([WG1, WG2, WG3, WG4].getD (i - 1) []).map abL with hw
  have hlt : ∀ k ∈ w ++ w ++ w, k < 14 := by
    obtain ⟨h1, h2⟩ := hi
    rw [hw]
    interval_cases i <;> decide
  have hmem : wJ (hW i) ∈ lyH := by
    apply wJ_mem_lyH
    obtain ⟨h1, h2⟩ := hi
    interval_cases i <;> decide
  refine triWit_of_cube hmem ?_
  have e : wJ (hW i) * gRep i = wJ w := by
    rw [gRep_eq i ⟨hi.1, by omega⟩, hw, wJ_append]
  rw [e, pow_succ, pow_two, ← wJ_append, ← wJ_append, eq_one_of_pw _ hlt hc]
  exact lyH.one_mem

theorem card_J : Nat.card J = 51765179004000000 := by
  obtain ⟨⟨hstab, hH, hO⟩, -⟩ := Theorems.F1_all
  have h1 := Subgroup.card_mul_index (stabilizer J opE)
  rw [index_stabilizer, ← Nat.card_coe_set_eq, hO, hstab, hH] at h1
  omega

theorem finite_J : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)

theorem isGood_lyH : IsGood lyH := by
  haveI := finite_J
  have u2 : wJ (uW ++ uW) = 1 := eq_one_of_pw _ lt_uu chkU2
  have v2 : wJ (vW ++ vW) = 1 := eq_one_of_pw _ lt_vv chkV2
  have uv2 : wJ ((uW ++ vW) ++ (uW ++ vW)) = 1 := eq_one_of_pw _ lt_uvuv chkUV2
  have u1 : wJ uW ≠ 1 := ne_one_of_pw _ lt_u chkU (by decide)
  have v1 : wJ vW ≠ 1 := ne_one_of_pw _ lt_v chkV (by decide)
  have uv1 : wJ (uW ++ vW) ≠ 1 := ne_one_of_pw _ lt_uv chkUV (by decide)
  rw [wJ_append] at u2 v2 uv2 uv1
  rw [wJ_append] at uv2
  exact isGood_of_three lyH (wJ_mem_lyH _ mem_u) (wJ_mem_lyH _ mem_v) u2 v2 uv2 u1 v1 uv1

theorem nonempty_mulEquiv : Nonempty (TauCeti.SporadicName.Ly.Group ≃* J) := by
  obtain ⟨φ, hφ⟩ := Theorems.bridge_hom
  obtain ⟨hfin, hcard⟩ := Theorems.finite_card_le
  let ψ : TauCeti.SporadicName.Ly.Group →* GL (Fin 111) (ZMod 5) := φ
  have hJ : J ≤ ψ.range := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hφ _ (Or.inl rfl)
    · exact hφ _ (Or.inr rfl)
  have hsurj : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have hfr : Finite ψ.range := Finite.of_surjective _ hsurj
  have c1 : Nat.card ψ.range ≤ Nat.card TauCeti.SporadicName.Ly.Group :=
    Nat.card_le_card_of_surjective _ hsurj
  have c2 : Nat.card J ≤ Nat.card ψ.range := Subgroup.card_le_of_le hJ
  rw [card_J] at c2
  have hEq : J = ψ.range := Subgroup.eq_of_le_of_card_ge hJ (by rw [card_J]; omega)
  have hbij : Function.Bijective ψ.rangeRestrict :=
    hsurj.bijective_of_nat_card_le (by omega)
  exact ⟨(MulEquiv.ofBijective ψ.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hEq.symm)⟩

open Classical in
theorem wilcoxCriterion_J : WilcoxCriterion J := by
  obtain ⟨⟨hstab, hH, hO⟩, hcov, -, -, -, -, -, h4⟩ := Theorems.F1_all
  let r : Fin 5 → J := fun i => if i.val = 0 then 1 else gRep i.val
  have hr : ∀ i : Fin 5, repOp i.val = r i • opE := by
    intro i
    show repOp i.val = (if i.val = 0 then 1 else gRep i.val) • opE
    by_cases h : i.val = 0
    · rw [if_pos h, repOp, if_pos h, one_smul]
    · rw [if_neg h, repOp, if_neg h]
  refine wilcoxCriterion_of_cover' opE lyH hstab r ?_ isGood_lyH ?_ ?_
  · intro htop
    rw [htop, Subgroup.card_top, card_J] at hH
    omega
  · intro g
    have hg : g • opE ∈ orbit J opE := mem_orbit opE g
    rw [← hcov] at hg
    rw [Finset.mem_coe, Finset.mem_biUnion] at hg
    obtain ⟨i, -, hi⟩ := hg
    refine ⟨i, ?_⟩
    rw [← hr]
    unfold subO at hi
    exact (Set.Finite.mem_toFinset _).1 hi
  · intro i
    fin_cases i
    · exact triWit_one lyH
    · exact triWit_small 1 ⟨le_rfl, by norm_num⟩ chk1
    · exact triWit_small 2 ⟨by norm_num, by norm_num⟩ chk2
    · exact triWit_small 3 ⟨by norm_num, le_rfl⟩ chk3
    · have hfin : (orbit J opE).Finite := Set.toFinite _
      have := triWit_of_ncard opE (r := gRep 4) hfin (by
        rw [hstab, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hO, h4]
        norm_num)
      rw [hstab] at this
      exact this

theorem hasCompleteMapping_J (hP : ProperSubgroupsAdmissible J) : HasCompleteMapping J :=
  @hasCompleteMapping_of_wilcoxCriterion J _ finite_J cosetStatement wilcoxCriterion_J hP

end

end CFSGOutside.HallPaige.Ly

namespace CFSGOutside.HallPaige

open CFSGOutside.Corpus.Ly CFSGOutside.HallPaige.Ly

/-- **The catalogue case of the Lyons group.** -/
theorem catalogueCase_Ly [Theorems] : CatalogueCase (.sporadic .Ly) := by
  intro _ hP
  haveI : LySeed := Theorems.lySeed
  obtain ⟨e⟩ := nonempty_mulEquiv
  exact @HasCompleteMapping.of_mulEquiv J _ TauCeti.SporadicName.Ly.Group _ e.symm
    (hasCompleteMapping_J
      (@ProperSubgroupsAdmissible.of_mulEquiv TauCeti.SporadicName.Ly.Group J _ _ e hP))

end CFSGOutside.HallPaige
