import CFSGOutside.AOVTame.WreathPerm
import CFSGOutside.AOVTame.SplitTwoMain

/-!
# AOV tameness: the splitting of `κ_{H^ι}` (the wreath case of AOV Theorem 3.6)

If every `α ∈ Aut_typ^I(L(H^ι))` permutes the coordinate subgroups of `∏ S` (with `S ≠ 1`) and
`κ_H` is split by `s_H`, then `s(x) = (∏ s_H[α⁰_i]) ∘ σ̂_α` splits `κ_{H^ι}`, where
`α⁰ = α σ̂_α⁻¹` is coordinate-preserving.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime]
variable {H : Type} [Group H] [Finite H] {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

section Basic

lemma coordComp_congr {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (h : α = α') {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hc : CoordPres hα) (hc' : CoordPres hα') (i : ι) : coordComp hc i = coordComp hc' i := by
  subst h; rfl

lemma coordComp_class_eq {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hc : CoordPres hα) (hc' : CoordPres hα') (ω : α.fn ≅ α'.fn) (i : ι) :
    autClass (coordComp_mem hc i) = autClass (coordComp_mem hc' i) := by
  unfold coordComp
  refine classA_eq_of_iso (coordAut_mem hα i) (CoordPres.presFactors hc i) (coordAut_mem hα' i)
    (CoordPres.presFactors hc' i) ?_
  unfold coordAut
  rw [conjIso_fn, conjIso_fn]
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ω _)

/-- An `Aut(G, T)`-representative of an outer class. -/
noncomputable def repN {G : Type} [Group G] [Finite G] (T : Sylow p G) (w : Out G) : MulAut G :=
  (exists_rep_normalizing T w).choose

lemma repN_map {G : Type} [Group G] [Finite G] (T : Sylow p G) (w : Out G) :
    (T : Subgroup G).map (repN T w).toMonoidHom = T :=
  (exists_rep_normalizing T w).choose_spec.choose

lemma repN_mk {G : Type} [Group G] [Finite G] (T : Sylow p G) (w : Out G) :
    (QuotientGroup.mk (repN T w) : Out G) = w :=
  (exists_rep_normalizing T w).choose_spec.choose_spec

variable (S) in
/-- `∏ : (ι → Out H) → Out(H^ι)`. -/
noncomputable def outPi (w : ι → Out H) : Out (ι → H) :=
  QuotientGroup.mk (piAut (fun i => repN S (w i)))

lemma outPi_eq (γ : ι → MulAut H) (hγ : ∀ i, (S : Subgroup H).map (γ i).toMonoidHom = S) :
    outPi S (fun i => QuotientGroup.mk (γ i)) = QuotientGroup.mk (piAut γ) := by
  unfold outPi
  apply QuotientGroup.eq.2
  -- `repN (mk γ_i) = γ_i ∘ c_{n_i}`
  have h : ∀ i, ∃ n : H, (repN S (QuotientGroup.mk (γ i)))⁻¹ * γ i = MulAut.conj n := by
    intro i
    have := repN_mk S (QuotientGroup.mk (γ i))
    have := QuotientGroup.eq.1 this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn.symm⟩
  choose n hn using h
  refine ⟨n, ?_⟩
  rw [← piAut_conj]
  ext g j
  have := congrArg (fun φ : MulAut H => φ (g j)) (hn j)
  change (repN S (QuotientGroup.mk (γ j)))⁻¹ (γ j (g j)) = MulAut.conj (n j) (g j) at this
  symm
  exact this

lemma outPi_mul (w w' : ι → Out H) : outPi S (w * w') = outPi S w * outPi S w' := by
  have e1 : w = fun i => QuotientGroup.mk (repN S (w i)) := funext fun i => (repN_mk S (w i)).symm
  have e2 : w' = fun i => QuotientGroup.mk (repN S (w' i)) := funext fun i => (repN_mk S (w' i)).symm
  have e3 : w * w' = fun i => QuotientGroup.mk (repN S (w i) * repN S (w' i)) := by
    funext i; rw [Pi.mul_apply, QuotientGroup.mk_mul, repN_mk, repN_mk]
  rw [e3, outPi_eq (fun i => repN S (w i) * repN S (w' i)) (fun i => by
    rw [show (repN S (w i) * repN S (w' i)).toMonoidHom =
      (repN S (w i)).toMonoidHom.comp (repN S (w' i)).toMonoidHom from rfl, ← map_map, repN_map,
      repN_map]),
    show (piAut fun i => repN S (w i) * repN S (w' i)) =
      piAut (fun i => repN S (w i)) * piAut (fun i => repN S (w' i)) from by ext g j; rfl,
    QuotientGroup.mk_mul]
  conv_rhs => rw [e1, e2]
  rw [outPi_eq _ (fun i => repN_map S (w i)), outPi_eq _ (fun i => repN_map S (w' i))]

lemma outPi_perm (w : ι → Out H) (σ : Equiv.Perm ι) :
    outPi S (fun i => w (σ.symm i)) * QuotientGroup.mk (permEquiv σ) =
      QuotientGroup.mk (permEquiv σ) * outPi S w := by
  unfold outPi
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  ext g j
  rfl

lemma kappa_outPi (w : ι → Out H) :
    kappa p (piSylow ι S) (outPi S w) =
      kappaElt p (piAut (fun i => repN S (w i))) (map_piAut _ (fun i => repN_map S (w i))) :=
  kappa_mk p _ _ _

end Basic

section Main
variable (hS : (S : Subgroup H) ≠ ⊥)
  (hperm : ∀ (α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))), ∃ σ, PermBy hα σ)
  (sH : OutTyp p (S : Subgroup H) →* Out H) (hsH : (kappa p S).comp sH = MonoidHom.id _)

/-- The permutation of `α`. -/
noncomputable def permOf {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) : Equiv.Perm ι :=
  (hperm α hα).choose

lemma permOf_spec {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    PermBy hα (permOf hperm hα) :=
  (hperm α hα).choose_spec

/-- `σ̂` in `Aut(L)`. -/
noncomputable abbrev permL (σ : Equiv.Perm ι) :
    LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  mapAut p (permEquiv (H := H) σ) (map_permEquiv_piSylow σ S)

lemma permL_mem (σ : Equiv.Perm ι) :
    permL (S := S) σ ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  mapAut_mem p _ _

/-- `α⁰ = α σ̂_α⁻¹`. -/
noncomputable abbrev norm0 {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  α * permL (permOf hperm hα)⁻¹

lemma norm0_mem {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    norm0 hperm hα ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  mul_mem hα (permL_mem _)

lemma norm0_coordPres {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    CoordPres (norm0_mem hperm hα) := by
  have h := (permOf_spec hperm hα).mul (permBy_permEquiv (S := S) (permOf hperm hα)⁻¹)
  rw [mul_inv_cancel] at h
  exact h

/-- `Θ(α⁰)`. -/
noncomputable def theta0 {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    ι → OutTyp p (S : Subgroup H) :=
  fun i => autClass (coordComp_mem (norm0_coordPres hperm hα) i)

/-- The candidate splitting, on representatives. -/
noncomputable def splitF {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) : Out (ι → H) :=
  outPi S (fun i => sH (theta0 hperm hα i)) * QuotientGroup.mk (permEquiv (permOf hperm hα))

lemma coordPres_congr {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (h : α = α') {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))
    (hc : CoordPres hα) : CoordPres hα' := by
  subst h; exact hc

lemma splitF_congr {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (h : α = α') (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))
    (hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    splitF hperm sH hα = splitF hperm sH hα' := by
  subst h; rfl

section Laws
variable {α β : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))
  (hβ : β ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))

include hS in
lemma permOf_mul : permOf hperm (mul_mem hα hβ) = permOf hperm hα * permOf hperm hβ :=
  PermBy.unique hS (permOf_spec hperm _) ((permOf_spec hperm hα).mul (permOf_spec hperm hβ))

include hS in
/-- The permutation of `α` only depends on the class of `α`. -/
lemma permOf_iso (ω : α.fn ≅ β.fn) : permOf hperm hβ = permOf hperm hα := by
  obtain ⟨n, hn, e⟩ := eq_conj_of_iso hα hβ ω
  have e' : β = mapAut p (MulAut.conj n) hn * α :=
    LAut.ext_fn p _ (by rw [e, LAut.fn_mul, mapAut_fn])
  have h := (permBy_conj n hn).mul (permOf_spec hperm hα)
  rw [one_mul] at h
  subst e'
  exact PermBy.unique hS (permOf_spec hperm _) h

include hS in
/-- `(αβ)⁰ = α⁰ · σ̂_α β⁰ σ̂_α⁻¹`. -/
lemma norm0_mul : norm0 hperm (mul_mem hα hβ) =
    norm0 hperm hα * permConj (permOf hperm hα) (norm0 hperm hβ) := by
  rw [permConj_eq]
  simp only [norm0, permL, permOf_mul hS hperm hα hβ, mapAut_permEquiv_inv, mapAut_permEquiv_mul]
  group

include hS in
lemma theta0_mul (k : ι) : theta0 hperm (mul_mem hα hβ) k =
    theta0 hperm hα k * theta0 hperm hβ ((permOf hperm hα).symm k) := by
  have hc := (norm0_coordPres hperm hα).mul
    (CoordPres.perm (norm0_coordPres hperm hβ) (permOf hperm hα))
  have e := coordComp_congr (norm0_mul hS hperm hα hβ) (norm0_coordPres hperm (mul_mem hα hβ)) hc k
  unfold theta0
  rw [autClass_congr e _ (coordComp_mem hc k)]
  rw [autClass_congr (coordComp_mul (norm0_coordPres hperm hα)
    (CoordPres.perm (norm0_coordPres hperm hβ) (permOf hperm hα)) k) _
    (mul_mem (coordComp_mem _ k) (coordComp_mem _ k)),
    autClass_mul]
  rw [autClass_congr (coordComp_perm (norm0_coordPres hperm hβ) (permOf hperm hα) k) _
    (coordComp_mem _ _)]
  all_goals exact coordComp_mem _ _

include hS in
/-- **Multiplicativity** of the splitting, on representatives. -/
lemma splitF_mul : splitF hperm sH (mul_mem hα hβ) = splitF hperm sH hα * splitF hperm sH hβ := by
  unfold splitF
  have e1 : (fun i => sH (theta0 hperm (mul_mem hα hβ) i)) = (fun i => sH (theta0 hperm hα i)) *
      (fun i => sH (theta0 hperm hβ ((permOf hperm hα).symm i))) := by
    funext i; rw [theta0_mul hS hperm hα hβ, map_mul]; rfl
  have key := outPi_perm (S := S) (fun j => sH (theta0 hperm hβ j)) (permOf hperm hα)
  rw [e1, outPi_mul, permOf_mul hS hperm hα hβ, permEquiv_mul,
    show ((permEquiv (permOf hperm hβ)).trans (permEquiv (permOf hperm hα)) : MulAut (ι → H)) =
      permEquiv (permOf hperm hα) * permEquiv (permOf hperm hβ) from rfl, QuotientGroup.mk_mul]
  rw [mul_assoc, ← mul_assoc (outPi S fun i => sH (theta0 hperm hβ ((permOf hperm hα).symm i))),
    key]
  simp only [mul_assoc]

include hS in
/-- The splitting only depends on the class of `α`. -/
lemma splitF_iso (ω : α.fn ≅ β.fn) : splitF hperm sH hβ = splitF hperm sH hα := by
  have hσ := permOf_iso hS hperm hα hβ ω
  have e : norm0 hperm hβ = β * permL (permOf hperm hα)⁻¹ := by
    show β * permL (permOf hperm hβ)⁻¹ = _
    rw [hσ]
  have hc := coordPres_congr e (mul_mem hβ (permL_mem (S := S) (permOf hperm hα)⁻¹))
    (norm0_coordPres hperm hβ)
  have ω' : (norm0 hperm hα).fn ≅ (β * permL (permOf hperm hα)⁻¹).fn :=
    Functor.isoWhiskerLeft _ ω
  have ht : theta0 hperm hβ = theta0 hperm hα := by
    funext i
    unfold theta0
    rw [autClass_congr (coordComp_congr e (norm0_coordPres hperm hβ) hc i) _ (coordComp_mem hc i)]
    exact (coordComp_class_eq (norm0_coordPres hperm hα) hc ω' i).symm
  unfold splitF
  rw [ht, hσ]

include hsH in
/-- **`κ ∘ s = id`**, on representatives. -/
lemma kappa_splitF : kappa p (piSylow ι S) (splitF hperm sH hα) = autClass hα := by
  unfold splitF
  rw [map_mul, kappa_outPi, kappa_mk p _ _ (map_permEquiv_piSylow _ S)]
  have hc := norm0_coordPres hperm hα
  rw [kappa_piAut hc (fun i => repN S (sH (theta0 hperm hα i))) (fun i => repN_map S _)
    (fun i => by
      rw [← kappa_mk p S _ (repN_map S _), repN_mk]
      exact DFunLike.congr_fun hsH _)]
  rw [← autClass_eq_kappaElt, ← autClass_mul]
  exact autClass_congr (by simp only [norm0, permL, mapAut_permEquiv_inv, inv_mul_cancel_right])
    _ _

end Laws

include hS in
lemma splitF_one : splitF hperm sH (one_mem (autTypI p ((piSylow ι S : Sylow p (ι → H)) :
    Subgroup (ι → H)))) = 1 := by
  have h := splitF_mul hS hperm sH (one_mem (autTypI p ((piSylow ι S : Sylow p (ι → H)) :
    Subgroup (ι → H)))) (one_mem _)
  rw [splitF_congr hperm sH (mul_one 1) _ (one_mem _)] at h
  exact left_eq_mul.1 h

include hS in
/-- The splitting on isotypical self-equivalences. -/
noncomputable def splitTyp : typEquivs p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) →*
    Out (ι → H) where
  toFun x := splitF hperm sH (repAut_mem x)
  map_one' := by
    have ω := Classical.choice (repAut_iso (1 : typEquivs p ((piSylow ι S : Sylow p (ι → H)) :
      Subgroup (ι → H))))
    rw [splitF_iso hS hperm sH (one_mem _) (repAut_mem 1) ω]
    exact splitF_one hS hperm sH
  map_mul' x y := by
    rw [splitF_iso hS hperm sH (mul_mem (repAut_mem x) (repAut_mem y)) (repAut_mem (x * y))
      (repAutMulIso x y).symm]
    exact splitF_mul hS hperm sH _ _

include hS in
/-- **The splitting of `κ_{H^ι}`** (AOV, proof of Theorem 3.6, wreath case). -/
noncomputable def wreathSplit : OutTyp p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) →*
    Out (ι → H) :=
  (natIsoCon p _).lift (splitTyp hS hperm sH) (by
    rintro x y ⟨e⟩
    exact (splitF_iso hS hperm sH (repAut_mem x) (repAut_mem y)
      ((Classical.choice (repAut_iso x)).symm ≪≫ e ≪≫ Classical.choice (repAut_iso y))).symm)

include hS hsH in
theorem wreath_split : (kappa p (piSylow ι S)).comp (wreathSplit hS hperm sH) = MonoidHom.id _ := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (natIsoCon p _).mk'_surjective z
  change kappa p (piSylow ι S) (splitF hperm sH (repAut_mem x)) = _
  rw [kappa_splitF hperm sH hsH (repAut_mem x)]
  exact (natIsoCon p _).eq.2 ⟨(Classical.choice (repAut_iso x)).symm⟩

end Main

end AndersenOliverVentura.Tame
