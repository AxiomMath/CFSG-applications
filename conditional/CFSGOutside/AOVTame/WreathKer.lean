import CFSGOutside.AOVTame.WreathComp
import CFSGOutside.AOVTame.Decomp

/-!
# AOV tameness: a coordinate-preserving `α` with trivial components is trivial

(The injectivity of `Ψ : Aut⁰_typ(L(ι → H)) → ∏ Aut_typ^I(L(H))`, AOV proof of Theorem 3.6.)
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

section
variable {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hα)
  (h1 : ∀ i, coordComp hc i = 1)
include h1

/-- `β(α)` is the identity on coordinate elements. -/
lemma betaPi_mulSingle_of_comp (i : ι) {x : H} (hx : x ∈ (S : Subgroup H)) :
    betaPi hα (Pi.mulSingle i x) (mulSingle_mem_piSub hx) = Pi.mulSingle i x := by
  have hA := betaFun_lautA (coordAut_mem hα i) (CoordPres.presFactors hc i) ⟨x, hx⟩
  have h2 : ((betaFun (lautA_mem (coordAut_mem hα i) (CoordPres.presFactors hc i)) ⟨x, hx⟩ : _) : H) = x := by
    have := betaFun_congr (h1 i) (coordComp_mem hc i) (one_mem _) ⟨x, hx⟩
    change ((betaFun (coordComp_mem hc i) ⟨x, hx⟩ : _) : H) = x
    rw [this, betaFun_one_aut]
  rw [h2] at hA
  have hP := betaFun_pair (coordAut_mem hα i) (CoordPres.presFactors hc i) x hx 1 (one_mem _)
  rw [← hA, bB_one (coordAut_mem hα i) (CoordPres.presFactors hc i)] at hP
  have e := betaFun_coordAut hα i (mulSingle_mem_piSub (ι := ι) (i := i) hx)
  have e' : (⟨coordEquiv i (Pi.mulSingle i x), by
      rw [← map_coordEquiv_piSylow i S]; exact mem_map_of_mem _ (mulSingle_mem_piSub hx)⟩ :
      ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
        Subgroup (H × ({j // j ≠ i} → H)))) = ⟨(x, 1), mem_prodSylow hx (one_mem _)⟩ :=
    Subtype.ext (coordEquiv_mulSingle i x)
  rw [e', hP, ← coordEquiv_mulSingle] at e
  exact (coordEquiv i).injective e.symm

/-- `β(α)` is the identity. -/
lemma betaPi_eq_of_comp {x : ι → H} (hx : x ∈ piSub ι S) : betaPi hα x hx = x := by
  let K : Subgroup (ι → H) :=
    { carrier := {y | ∃ hy : y ∈ piSub ι S, betaPi hα y hy = y}
      one_mem' := ⟨one_mem _, betaPi_one hα⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        exact ⟨mul_mem ha hb, by rw [betaPi_mul hα ha hb, ha1, hb1]⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨inv_mem ha, ?_⟩
        have e := betaPi_mul hα ha (inv_mem ha)
        rw [betaPi_congr hα (mul_inv_cancel a) _ (one_mem _), betaPi_one hα, ha1] at e
        exact eq_inv_of_mul_eq_one_right e.symm }
  have hK : x ∈ K := by
    apply pi_mem_of_mulSingle_mem
    intro j
    exact ⟨_, betaPi_mulSingle_of_comp hc h1 j ((mem_piSub ι S).1 hx j)⟩
  obtain ⟨_, h⟩ := hK
  exact h

lemma beta_eq_refl_of_comp : beta hα = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact betaPi_eq_of_comp hc h1 x.2

/-- `α` fixes every object. -/
lemma obj_eq_of_comp (P : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    α.fn.obj P = P := by
  apply Obj.ext
  rw [obj_val_eq hα, beta_eq_refl_of_comp hc h1]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; exact hz
  · intro hy; exact ⟨_, ⟨⟨y, P.2.1 hy⟩, hy, rfl⟩, rfl⟩

end

section Slab
variable (i : ι)

/-- `e_i : L(ι → H) → L(H × H^{ι∖i})`. -/
noncomputable abbrev coordF : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) ⥤
    Obj p ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H))) :=
  mapFunctor p (coordEquiv i) (map_coordEquiv_piSylow i S)

/-- `e_i⁻¹`. -/
noncomputable abbrev coordF' : Obj p ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p (H × ({j // j ≠ i} → H))) :
      Subgroup (H × ({j // j ≠ i} → H))) ⥤
    Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  mapFunctor p (coordEquiv i).symm (map_symm_map _ (map_coordEquiv_piSylow i S))

lemma coordF_coordF' : coordF (S := S) i ⋙ coordF' i = 𝟭 _ := by
  rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.self_trans_symm _) _ (map_refl _),
    mapFunctor_refl]

lemma coordF'_coordF : coordF' (S := S) i ⋙ coordF i = 𝟭 _ := by
  rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.symm_trans_self _) _ (map_refl _),
    mapFunctor_refl]

/-- The slab `{x | x i ∈ P}` over an object `P` of `L(H)`. -/
noncomputable def slab (P : Obj p (S : Subgroup H)) :
    Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  (coordF' i).obj (prodObj (piSylow {j // j ≠ i} S) P)

lemma mem_slab {P : Obj p (S : Subgroup H)} {x : ι → H} :
    x ∈ (slab i P).val ↔ x i ∈ P.val ∧ ∀ j, j ≠ i → x j ∈ (S : Subgroup H) := by
  change x ∈ (P.val.prod _).map (coordEquiv i).symm.toMonoidHom ↔ _
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    refine ⟨by simpa [coordEquiv_symm_apply_self] using ha, fun j hj => ?_⟩
    change (coordEquiv i).symm (a, b) j ∈ _
    rw [coordEquiv_symm_apply_ne i _ hj]
    exact (mem_piSub _ S).1 hb _
  · rintro ⟨h1, h2⟩
    refine ⟨coordEquiv i x, ⟨h1, (mem_piSub _ S).2 fun j => h2 j j.2⟩, ?_⟩
    exact (coordEquiv i).symm_apply_apply x

lemma coordF_slab (P : Obj p (S : Subgroup H)) :
    (coordF i).obj (slab i P) = prodObj (piSylow {j // j ≠ i} S) P := by
  change ((coordF' i) ⋙ (coordF i)).obj _ = _
  rw [coordF'_coordF]; rfl

lemma mulSingle_mem_transporter_slab {P Q : Obj p (S : Subgroup H)} {g : H}
    (hg : g ∈ transporter P.val Q.val) :
    Pi.mulSingle i g ∈ transporter (slab i P).val (slab i Q).val := by
  intro x hx
  rw [mem_slab] at hx ⊢
  refine ⟨?_, fun j hj => ?_⟩
  · simpa using hg _ hx.1
  · simpa [Pi.mulSingle_eq_of_ne hj] using hx.2 j hj

end Slab

lemma liftA_heq {B : Type} [Group B] [Finite B] {SB : Sylow p B} {P P' Q Q' : Obj p (S : Subgroup H)}
    (hP : P = P') (hQ : Q = Q') {f : P ⟶ Q} {f' : P' ⟶ Q'} (h : HEq f f') :
    HEq (liftA SB f) (liftA SB f') := by
  subst hP hQ; cases h; rfl

section Fix
variable {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hα)
  (h1 : ∀ i, coordComp hc i = 1)
include h1

lemma alpha_fn_eq (i : ι) : α.fn = coordF i ⋙ (coordAut i α).fn ⋙ coordF' i := by
  rw [coordAut, conjIso_fn]
  change α.fn = coordF i ⋙ (coordF' i ⋙ α.fn ⋙ coordF i) ⋙ coordF' i
  rw [← Functor.assoc, ← Functor.assoc, coordF_coordF', Functor.id_comp, Functor.assoc,
    coordF_coordF', Functor.comp_id]

/-- **Coordinate morphisms are fixed.** -/
lemma fix_coord (i : ι) {P Q : Obj p (S : Subgroup H)} {g : H} (hg : g ∈ transporter P.val Q.val) :
    HEq (α.fn.map (show slab i P ⟶ slab i Q from
      mk p (Pi.mulSingle i g) (mulSingle_mem_transporter_slab i hg)))
      (show slab i P ⟶ slab i Q from mk p (Pi.mulSingle i g) (mulSingle_mem_transporter_slab i hg)) := by
  set m := (show slab i P ⟶ slab i Q from mk p (Pi.mulSingle i g) (mulSingle_mem_transporter_slab i hg))
  have hE : HEq ((coordF i).map m) (liftA (piSylow {j // j ≠ i} S) (show P ⟶ Q from mk p g hg)) := by
    rw [liftA_mk]
    change HEq (mk p (coordEquiv i (Pi.mulSingle i g)) _) _
    exact mk_heq p (congrArg Obj.val (coordF_slab i P)) (congrArg Obj.val (coordF_slab i Q))
      (coordEquiv_mulSingle i g) _ _
  set αe := coordAut i α
  have hαe := coordAut_mem hα i
  have hf := CoordPres.presFactors hc i
  -- `α_e` fixes `liftA [g]`
  have hA : HEq (αe.fn.map (liftA (piSylow {j // j ≠ i} S) (show P ⟶ Q from mk p g hg)))
      (liftA (piSylow {j // j ≠ i} S) (show P ⟶ Q from mk p g hg)) := by
    refine (liftA_fnA hαe hf _).trans ?_
    have hid : (lautA (piSylow {j // j ≠ i} S) hαe hf).fn = 𝟭 _ := by
      have := congrArg (fun γ : LAut p (S : Subgroup H) => γ.fn) (h1 i)
      exact this
    rw [lautA_fn] at hid
    refine liftA_heq (Functor.congr_obj hid P) (Functor.congr_obj hid Q) ?_
    exact Functor.hcongr_hom hid _
  have hobj : ∀ R, (coordF i).obj (α.fn.obj R) = αe.fn.obj ((coordF i).obj R) := by
    intro R
    have := Functor.congr_obj (alpha_fn_eq hc h1 i) R
    rw [this]
    change ((coordF' i) ⋙ (coordF i)).obj _ = _
    rw [coordF'_coordF]; rfl
  have h2 : HEq (α.fn.map m) ((coordF' i).map (αe.fn.map ((coordF i).map m))) :=
    Functor.hcongr_hom (alpha_fn_eq hc h1 i) m
  refine h2.trans ?_
  have h3 : HEq (αe.fn.map ((coordF i).map m)) ((coordF i).map m) := by
    have h4 := Functor.map_heq' αe.fn (coordF_slab i P) (coordF_slab i Q) hE
    exact h4.trans (hA.trans hE.symm)
  have h5 := Functor.map_heq' (coordF' i)
    (by rw [← hobj, obj_eq_of_comp hc h1]) (by rw [← hobj, obj_eq_of_comp hc h1]) h3
  refine h5.trans ?_
  exact Functor.hcongr_hom (coordF_coordF' i) m

end Fix

section Hull

/-- The `j`-th projection. -/
def projSub (j : ι) (P : Subgroup (ι → H)) : Subgroup H := P.map (Pi.evalMonoidHom (fun _ => H) j)

lemma projSub_le {j : ι} {P : Subgroup (ι → H)} (h : P ≤ piSub ι S) : projSub j P ≤ S := by
  rintro _ ⟨x, hx, rfl⟩; exact (mem_piSub ι S).1 (h hx) j

lemma conj_mem_projSub {P Q : Subgroup (ι → H)} {g : ι → H} (hg : g ∈ transporter P Q) (j : ι) :
    g j ∈ transporter (projSub j P) (projSub j Q) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨g * x * g⁻¹, hg x hx, rfl⟩

/-- `R_A = ∏_j (Q_j if j ∈ A else P_j)`. -/
def mixSub (P Q : Subgroup (ι → H)) (A : Finset ι) : Subgroup (ι → H) :=
  Subgroup.pi Set.univ (fun j => if j ∈ A then projSub j Q else projSub j P)

lemma mem_mixSub {P Q : Subgroup (ι → H)} {A : Finset ι} {x : ι → H} :
    x ∈ mixSub P Q A ↔ ∀ j, x j ∈ (if j ∈ A then projSub j Q else projSub j P : Subgroup H) := by
  simp [mixSub, mem_pi]

/-- `g_A = (g_j if j ∈ A else 1)`. -/
def mixElt (g : ι → H) (A : Finset ι) : ι → H := fun j => if j ∈ A then g j else 1

lemma mixElt_insert (g : ι → H) {A : Finset ι} {i : ι} (hi : i ∉ A) :
    mixElt g (insert i A) = Pi.mulSingle i (g i) * mixElt g A := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [mixElt, hi]
  · simp [mixElt, hj, Pi.mulSingle_eq_of_ne hj]

lemma mixElt_mem {P Q : Subgroup (ι → H)} {g : ι → H} (hg : g ∈ transporter P Q) (A : Finset ι) :
    mixElt g A ∈ transporter (mixSub P Q ∅) (mixSub P Q A) := by
  intro x hx
  rw [mem_mixSub] at hx ⊢
  intro j
  have := hx j
  simp only [Finset.notMem_empty, if_false] at this
  by_cases hj : j ∈ A
  · have e : (mixElt g A * x * (mixElt g A)⁻¹) j = g j * x j * (g j)⁻¹ := by
      simp [mixElt, hj]
    rw [e]
    simp only [hj, if_true]
    exact conj_mem_projSub hg j _ this
  · simp only [hj, if_false, mixElt, Pi.mul_apply, Pi.inv_apply, one_mul, inv_one, mul_one]
    exact this

lemma le_mixSub_empty (P Q : Subgroup (ι → H)) : P ≤ mixSub P Q ∅ := by
  intro x hx
  rw [mem_mixSub]
  intro j
  simp only [Finset.notMem_empty, if_false]
  exact ⟨x, hx, rfl⟩

lemma le_mixSub_univ (P Q : Subgroup (ι → H)) : Q ≤ mixSub P Q Finset.univ := by
  intro x hx
  rw [mem_mixSub]
  intro j
  simp only [Finset.mem_univ, if_true]
  exact ⟨x, hx, rfl⟩

lemma mixSub_le {P Q : Subgroup (ι → H)} (hP : P ≤ piSub ι S) (hQ : Q ≤ piSub ι S) (A : Finset ι) :
    mixSub P Q A ≤ piSub ι S := by
  intro x hx
  rw [mem_mixSub] at hx
  rw [mem_piSub]
  intro j
  have := hx j
  split_ifs at this
  · exact projSub_le hQ this
  · exact projSub_le hP this

lemma isCentric_mixSub {P Q : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {g : ι → H} (hg : g ∈ transporter P.val Q.val) (A : Finset ι) :
    IsCentric ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) (mixSub P.val Q.val A) := by
  have hle := mixSub_le (S := S) P.2.1 Q.2.1 A
  have h0 : IsCentric ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) (mixSub P.val Q.val ∅) :=
    isCentric_mono P.2 (le_mixSub_empty _ _) (mixSub_le P.2.1 Q.2.1 ∅)
  have hc : conjSub (mixElt g A) (mixSub P.val Q.val ∅) ≤ mixSub P.val Q.val A := by
    rintro _ ⟨x, hx, rfl⟩; exact mixElt_mem hg A x hx
  exact isCentric_mono (isCentric_conjSub h0 (hc.trans hle)) hc hle

/-- `R_A` as an object. -/
noncomputable def mixObj {P Q : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {g : ι → H} (hg : g ∈ transporter P.val Q.val) (A : Finset ι) :
    Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  ⟨mixSub P.val Q.val A, isCentric_mixSub hg A⟩

/-- The `i`-th projection of an object, as an object of `L(H)`. -/
noncomputable def projObj (i : ι) (P : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    Obj p (S : Subgroup H) :=
  ⟨projSub i P.val, by
    have := isCentric_fst ((coordF i).obj P).2
    convert this using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨coordEquiv i x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩⟩

lemma mixObj_le_slab {P Q : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {g : ι → H} (hg : g ∈ transporter P.val Q.val) {A : Finset ι} {i : ι} (hi : i ∉ A) :
    (mixObj hg A).val ≤ (slab i (projObj i P)).val := by
  intro x hx
  rw [mem_slab]
  change x ∈ mixSub _ _ _ at hx
  have hx' := hx
  rw [mem_mixSub] at hx
  refine ⟨?_, fun j _ => ?_⟩
  · have := hx i; simp only [hi, if_false] at this; exact this
  · exact (mem_piSub ι S).1 (mixSub_le (S := S) P.2.1 Q.2.1 A hx') j

lemma mixObj_insert_le_slab {P Q : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {g : ι → H} (hg : g ∈ transporter P.val Q.val) (A : Finset ι) (i : ι) :
    (mixObj hg (insert i A)).val ≤ (slab i (projObj i Q)).val := by
  intro x hx
  rw [mem_slab]
  change x ∈ mixSub _ _ _ at hx
  have hx' := hx
  rw [mem_mixSub] at hx
  refine ⟨?_, fun j _ => ?_⟩
  · have := hx i; simp only [Finset.mem_insert_self, if_true] at this; exact this
  · exact (mem_piSub ι S).1 (mixSub_le (S := S) P.2.1 Q.2.1 _ hx') j

end Hull

section Main
variable {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hα)
  (h1 : ∀ i, coordComp hc i = 1)
include h1

/-- A morphism `[g]` is fixed by `α` if some (equivalently every) representative is. -/
lemma fixed_of_restrict {X Y X' Y' : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hX : X.val ≤ X'.val) (hY : Y.val ≤ Y'.val) {g : ι → H} (hg : g ∈ transporter X.val Y.val)
    (hg' : g ∈ transporter X'.val Y'.val)
    (h : HEq (α.fn.map (show X' ⟶ Y' from mk p g hg')) (show X' ⟶ Y' from mk p g hg')) :
    HEq (α.fn.map (show X ⟶ Y from mk p g hg)) (show X ⟶ Y from mk p g hg) := by
  obtain ⟨hk', e⟩ := eq_mk_of_heq (obj_eq_of_comp hc h1 X') (obj_eq_of_comp hc h1 Y') h
  obtain ⟨hk, e2⟩ := alpha_restrict hα hX hY hg hg' e
  rw [e2]
  exact mk_heq p (congrArg Obj.val (obj_eq_of_comp hc h1 X)) (congrArg Obj.val (obj_eq_of_comp hc h1 Y))
    rfl _ _

lemma fixed_comp {X Y Z : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {f : X ⟶ Y} {f' : Y ⟶ Z} (h : HEq (α.fn.map f) f) (h' : HEq (α.fn.map f') f') :
    HEq (α.fn.map (f ≫ f')) (f ≫ f') := by
  rw [α.fn.map_comp]
  have hX := obj_eq_of_comp hc h1 X
  have hY := obj_eq_of_comp hc h1 Y
  have hZ := obj_eq_of_comp hc h1 Z
  revert h h'
  generalize α.fn.map f = a
  generalize α.fn.map f' = b
  intro h h'
  revert a b
  rw [hX, hY, hZ]
  intro a b h h'
  cases h; cases h'; rfl

/-- **Every morphism is fixed.** -/
theorem fixed_all {P Q : Obj p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} {g : ι → H}
    (hg : g ∈ transporter P.val Q.val) :
    HEq (α.fn.map (show P ⟶ Q from mk p g hg)) (show P ⟶ Q from mk p g hg) := by
  -- the hull statement
  have key : ∀ A : Finset ι, HEq (α.fn.map (show mixObj hg ∅ ⟶ mixObj hg A from
      mk p (mixElt g A) (mixElt_mem hg A))) (show mixObj hg ∅ ⟶ mixObj hg A from
      mk p (mixElt g A) (mixElt_mem hg A)) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      have e : (show mixObj hg ∅ ⟶ mixObj hg ∅ from mk p (mixElt g ∅) (mixElt_mem hg ∅)) = 𝟙 _ :=
        mk_congr p (by funext j; simp [mixElt]) _ _
      rw [e, α.fn.map_id, obj_eq_of_comp hc h1]
    | @insert i A hi ih =>
      have hstep : Pi.mulSingle i (g i) ∈ transporter (mixObj hg A).val (mixObj hg (insert i A)).val := by
        intro x hx
        change x ∈ mixSub _ _ _ at hx
        change _ ∈ mixSub _ _ _
        rw [mem_mixSub] at hx ⊢
        intro j
        by_cases hj : j = i
        · subst hj
          have := hx j
          simp only [hi, if_false] at this
          simp only [Finset.mem_insert_self, if_true, Pi.mul_apply, Pi.inv_apply,
            Pi.mulSingle_eq_same]
          exact conj_mem_projSub hg j _ this
        · have := hx j
          have hjA : (j ∈ insert i A) ↔ j ∈ A := by simp [hj]
          simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hj, one_mul, inv_one,
            mul_one]
          by_cases hjA' : j ∈ A
          · simp only [hjA', if_true] at this; simp only [hjA.2 hjA', if_true]; exact this
          · simp only [hjA', if_false] at this
            have : j ∉ insert i A := fun h => hjA' (hjA.1 h)
            simp only [this, if_false]; exact (by assumption)
      have e : (show mixObj hg ∅ ⟶ mixObj hg (insert i A) from
          mk p (mixElt g (insert i A)) (mixElt_mem hg _)) =
          (show mixObj hg ∅ ⟶ mixObj hg A from mk p (mixElt g A) (mixElt_mem hg A)) ≫
            (show mixObj hg A ⟶ mixObj hg (insert i A) from mk p (Pi.mulSingle i (g i)) hstep) :=
        mk_congr p (mixElt_insert g hi) _ _
      rw [e]
      refine fixed_comp hc h1 ih ?_
      have hgi := conj_mem_projSub hg i
      exact fixed_of_restrict hc h1 (mixObj_le_slab hg hi) (mixObj_insert_le_slab hg A i) hstep
        (mulSingle_mem_transporter_slab i (P := projObj i P) (Q := projObj i Q) hgi)
        (fix_coord hc h1 i hgi)
  have hU := key Finset.univ
  have hmixU : mixElt g Finset.univ = g := by funext j; simp [mixElt]
  have hgU : g ∈ transporter (mixObj hg ∅).val (mixObj hg Finset.univ).val := by
    have := mixElt_mem hg Finset.univ; rwa [hmixU] at this
  have hU' : HEq (α.fn.map (show mixObj hg ∅ ⟶ mixObj hg Finset.univ from mk p g hgU))
      (show mixObj hg ∅ ⟶ mixObj hg Finset.univ from mk p g hgU) := by
    have e : (show mixObj hg ∅ ⟶ mixObj hg Finset.univ from mk p g hgU) =
        (show mixObj hg ∅ ⟶ mixObj hg Finset.univ from mk p (mixElt g Finset.univ)
          (mixElt_mem hg Finset.univ)) := mk_congr p hmixU.symm _ _
    rw [e]; exact hU
  exact fixed_of_restrict hc h1 (le_mixSub_empty _ _) (le_mixSub_univ _ _) hg hgU hU'

/-- **A coordinate-preserving `α` with trivial components is trivial.** -/
theorem eq_one_of_comp : α = 1 := by
  apply LAut.ext_fn
  rw [LAut.fn_one]
  refine Functor.hext (obj_eq_of_comp hc h1) ?_
  rintro P Q ⟨⟨g, hg⟩⟩
  exact fixed_all hc h1 hg

end Main

end AndersenOliverVentura.Tame


