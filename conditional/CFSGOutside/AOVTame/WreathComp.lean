import CFSGOutside.AOVTame.PiBasic
import CFSGOutside.AOVTame.SplitTwo

/-!
# AOV tameness: components of a coordinate-preserving `α ∈ Aut_typ^I(L(ι → H))`

For `α` whose `β` preserves every coordinate subgroup `S_i` of `∏ S`, the `i`-th component
`α_i ∈ Aut_typ^I(L(H))` is the first component of `α` transported along `(ι → H) ≃ H × H^{ι∖i}`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

lemma mulSingle_mem_piSub {i : ι} {x : H} (hx : x ∈ (S : Subgroup H)) :
    Pi.mulSingle i x ∈ piSub ι S := by
  rw [mem_piSub]
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp [Pi.mulSingle_eq_of_ne hj]

variable {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))

/-- `β(α)` as a map on `ι → H` (on `∏ S`). -/
noncomputable def betaPi (x : ι → H) (hx : x ∈ piSub ι S) : ι → H :=
  (betaFun hα ⟨x, hx⟩ : ι → H)

/-- `β(α)` preserves every coordinate subgroup. -/
def CoordPres : Prop :=
  ∀ (i : ι) (x : H) (hx : x ∈ (S : Subgroup H)),
    ∃ y, betaPi hα (Pi.mulSingle i x) (mulSingle_mem_piSub hx) = Pi.mulSingle i y

lemma betaPi_mul {a b : ι → H} (ha : a ∈ piSub ι S) (hb : b ∈ piSub ι S) :
    betaPi hα (a * b) (mul_mem ha hb) = betaPi hα a ha * betaPi hα b hb := by
  have := betaFun_mul hα ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

lemma betaPi_one : betaPi hα 1 (one_mem _) = 1 := by
  have : betaFun hα (1 : ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) = 1 := by
    rw [← beta_apply hα]; exact map_one _
  exact congrArg Subtype.val this

lemma betaPi_congr {a b : ι → H} (h : a = b) (ha : a ∈ piSub ι S) (hb : b ∈ piSub ι S) :
    betaPi hα a ha = betaPi hα b hb := by subst h; rfl

variable {hα}

lemma CoordPres.snd (hc : CoordPres hα) (i : ι) {x : ι → H} (hx : x ∈ piSub ι S) (hxi : x i = 1) :
    betaPi hα x hx i = 1 := by
  let K : Subgroup (ι → H) :=
    { carrier := {y | ∃ hy : y ∈ piSub ι S, betaPi hα y hy i = 1 ∧ y i = 1}
      one_mem' := ⟨one_mem _, by rw [betaPi_one hα]; rfl, rfl⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
        refine ⟨mul_mem ha hb, ?_, by simp [ha2, hb2]⟩
        rw [betaPi_mul hα ha hb, Pi.mul_apply, ha1, hb1, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha1, ha2⟩
        refine ⟨inv_mem ha, ?_, by simp [ha2]⟩
        have e := betaPi_mul hα ha (inv_mem ha)
        rw [betaPi_congr hα (mul_inv_cancel a) _ (one_mem _), betaPi_one hα] at e
        have e' := congrFun e i
        simp only [Pi.one_apply, Pi.mul_apply, ha1, one_mul] at e'
        exact e'.symm }
  have hK : x ∈ K := by
    apply pi_mem_of_mulSingle_mem
    intro j
    have hxj : x j ∈ (S : Subgroup H) := (mem_piSub ι S).1 hx j
    by_cases hj : j = i
    · subst hj
      rw [hxi, Pi.mulSingle_one]
      exact one_mem K
    · refine ⟨mulSingle_mem_piSub hxj, ?_, Pi.mulSingle_eq_of_ne (Ne.symm hj) _⟩
      obtain ⟨y, hy⟩ := hc j (x j) hxj
      rw [hy]
      exact Pi.mulSingle_eq_of_ne (Ne.symm hj) _
  obtain ⟨hx', h1, -⟩ := hK
  exact h1

/-- `α` transported along `(ι → H) ≃ H × H^{ι∖i}`. -/
noncomputable def coordAut (i : ι)
    (α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    LAut p ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H))) :=
  conjIso (coordEquiv i) (map_coordEquiv_piSylow i S) α

include hα in
variable (hα) in
lemma coordAut_mem (i : ι) : coordAut i α ∈ autTypI p
    ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H))) :=
  conjIso_mem _ _ hα

variable (hα) in
lemma betaFun_coordAut (i : ι) {x : ι → H} (hx : x ∈ piSub ι S) :
    ((betaFun (coordAut_mem hα i) ⟨coordEquiv i x, by
      rw [← map_coordEquiv_piSylow i S]; exact mem_map_of_mem _ hx⟩ : _) : H × _) =
      coordEquiv i (betaPi hα x hx) :=
  betaFun_conjIso _ _ hα ⟨x, hx⟩ _

lemma coordEquiv_mulSingle (i : ι) (a : H) : coordEquiv i (Pi.mulSingle i a) = (a, 1) := by
  ext j
  · simp
  · simp [Pi.mulSingle_eq_of_ne j.2]

lemma CoordPres.presFactors (hc : CoordPres hα) (i : ι) : PresFactors (coordAut_mem hα i) := by
  constructor
  · intro a ha
    have hx := mulSingle_mem_piSub (ι := ι) (i := i) ha
    have e := betaFun_coordAut hα i hx
    have e' : (⟨coordEquiv i (Pi.mulSingle i a), by
        rw [← map_coordEquiv_piSylow i S]; exact mem_map_of_mem _ hx⟩ :
        ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H)))) =
        ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ := Subtype.ext (coordEquiv_mulSingle i a)
    rw [e'] at e
    rw [e]
    obtain ⟨y, hy⟩ := hc i a ha
    change betaPi hα _ hx = _ at hy
    rw [hy, coordEquiv_mulSingle]
  · intro b hb
    let x := (coordEquiv i).symm (1, b)
    have hx : x ∈ piSub ι S := by
      have : (1, b) ∈ ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H))) :=
        mem_prodSylow (one_mem _) hb
      rw [← map_coordEquiv_piSylow i S] at this
      obtain ⟨y, hy, e⟩ := this
      have : y = x := by
        change y = (coordEquiv i).symm (1, b)
        rw [← e]; exact ((coordEquiv i).symm_apply_apply y).symm
      rw [← this]; exact hy
    have e := betaFun_coordAut hα i hx
    have e' : (⟨coordEquiv i x, by
        rw [← map_coordEquiv_piSylow i S]; exact mem_map_of_mem _ hx⟩ :
        ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H)))) =
        ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ := Subtype.ext ((coordEquiv i).apply_symm_apply _)
    rw [e'] at e
    rw [e]
    have hxi : x i = 1 := coordEquiv_symm_apply_self i (1, b)
    exact hc.snd i hx hxi

/-- The `i`-th component `α_i ∈ Aut_typ^I(L(H))`. -/
noncomputable def coordComp (hc : CoordPres hα) (i : ι) : LAut p (S : Subgroup H) :=
  lautA (piSylow {j // j ≠ i} S) (coordAut_mem hα i) (CoordPres.presFactors hc i)

lemma coordComp_mem (hc : CoordPres hα) (i : ι) : coordComp hc i ∈ autTypI p (S : Subgroup H) :=
  lautA_mem _ _

end AndersenOliverVentura.Tame
