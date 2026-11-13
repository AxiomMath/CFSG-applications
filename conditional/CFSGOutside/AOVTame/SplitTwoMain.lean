import CFSGOutside.AOVTame.SplitTwo

/-!
# AOV tameness: the splitting of `κ_{A × B}` for factor-preserving `Aut_typ^I(L(A × B))`

AOV, proof of Theorem 3.6: when every element of `Aut_typ^I(L(A × B))` preserves both factors
(`Aut_typ^I = Aut⁰_typ`), `s = (s_A × s_B) ∘ Ψ̄` splits `κ_{A × B}`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

/-- An `Aut(G, T)`-representative of an outer automorphism class. -/
lemma exists_rep_normalizing {G : Type u} [Group G] [Finite G] (T : Sylow p G) (w : Out G) :
    ∃ (γ : MulAut G) (hγ : (T : Subgroup G).map γ.toMonoidHom = T), (QuotientGroup.mk γ : Out G) = w := by
  obtain ⟨γ', rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨g, hg⟩ := exists_map_eq_conjSub p T γ'
  refine ⟨(MulAut.conj g)⁻¹ * γ', conj_inv_mul_mem p T γ' hg, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (inv_mem (MonoidHom.mem_range.2 ⟨g, rfl⟩)),
    one_mul]

lemma mapAut_prodCongr {γA : MulAut A} {γB : MulAut B} (hA : (SA : Subgroup A).map γA.toMonoidHom = SA)
    (hB : (SB : Subgroup B).map γB.toMonoidHom = SB) :
    mapAut p (MulEquiv.prodCongr γA γB) (prodCongr_mem hA hB) =
      phiAut SB (mapAut_mem p γA hA) * phiBAut (SA := SA) (mapAut_mem p γB hB) := by
  apply LAut.ext_fn
  rw [LAut.fn_mul, phiAut_fn, mapAut_fn, phiFunctor_mapIso, phiBAut_mapIso_fn, mapFunctor_comp]
  exact mapFunctor_congr p (by ext <;> rfl) _ _

/-- The isomorphism `repAut (x * y) ≅ repAut x * repAut y`. -/
noncomputable def repAutMulIso {G : Type u} [Group G] [Finite G] {T : Sylow p G}
    (x y : typEquivs p (T : Subgroup G)) : (repAut (x * y)).fn ≅ (repAut x * repAut y).fn :=
  (Classical.choice (repAut_iso (x * y))).symm ≪≫
    Functor.isoWhiskerLeft y.1.toFunctor (Classical.choice (repAut_iso x)) ≪≫
      Functor.isoWhiskerRight (Classical.choice (repAut_iso y)) (repAut x).fn

section
variable (hpres : ∀ (α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))), PresFactors hα)
include hpres

lemma autClass_lautA_one :
    autClass (lautA_mem (one_mem (autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))))
      (hpres _ (one_mem _))) = 1 := by
  have : lautA SB (one_mem (autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))))
      (hpres _ (one_mem _)) = 1 := LAut.ext_fn p _ fnA_one
  rw [autClass_congr this _ (one_mem _)]
  exact map_one ((natIsoCon p (SA : Subgroup A)).mk')

lemma autClass_lautB_one :
    autClass (lautB_mem (one_mem (autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))))
      (hpres _ (one_mem _))) = 1 := by
  have h1 : swapAut (1 : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) = 1 := by
    apply LAut.ext_fn
    unfold swapAut
    rw [conjIso_fn, LAut.fn_one, Functor.id_comp, mapFunctor_comp,
      mapFunctor_congr p (MulEquiv.symm_trans_self _) _ (map_refl _), mapFunctor_refl]
    rfl
  have : lautB SA (one_mem (autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))))
      (hpres _ (one_mem _)) = 1 := by
    apply LAut.ext_fn
    change fnA SA (α := swapAut 1) = _
    rw [fnA_congr h1, fnA_one]
    rfl
  rw [autClass_congr this _ (one_mem _)]
  exact map_one ((natIsoCon p (SB : Subgroup B)).mk')

/-- `x ↦ [α_A]` for `α` an `Aut_typ^I`-representative of `x`. -/
noncomputable def compA : typEquivs p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) →*
    OutTyp p (SA : Subgroup A) where
  toFun x := autClass (lautA_mem (repAut_mem x) (hpres _ (repAut_mem x)))
  map_one' := by
    have ω := Classical.choice (repAut_iso (1 : typEquivs p ((prodSylow SA SB : Sylow p (A × B)) :
      Subgroup (A × B))))
    rw [classA_eq_of_iso (repAut_mem 1) (hpres _ _) (one_mem _) (hpres _ (one_mem _)) ω.symm]
    exact autClass_lautA_one hpres
  map_mul' x y := by
    rw [classA_eq_of_iso (repAut_mem (x * y)) (hpres _ _) (mul_mem (repAut_mem x) (repAut_mem y))
      (hpres _ _) (repAutMulIso x y)]
    rw [show hpres _ (mul_mem (repAut_mem x) (repAut_mem y)) = presFactors_mul (repAut_mem x)
      (hpres _ _) (repAut_mem y) (hpres _ _) from rfl, classA_mul]

/-- `x ↦ [α_B]`. -/
noncomputable def compB : typEquivs p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) →*
    OutTyp p (SB : Subgroup B) where
  toFun x := autClass (lautB_mem (repAut_mem x) (hpres _ (repAut_mem x)))
  map_one' := by
    have ω := Classical.choice (repAut_iso (1 : typEquivs p ((prodSylow SA SB : Sylow p (A × B)) :
      Subgroup (A × B))))
    rw [classB_eq_of_iso (repAut_mem 1) (hpres _ _) (one_mem _) (hpres _ (one_mem _)) ω.symm]
    exact autClass_lautB_one hpres
  map_mul' x y := by
    rw [classB_eq_of_iso (repAut_mem (x * y)) (hpres _ _) (mul_mem (repAut_mem x) (repAut_mem y))
      (hpres _ _) (repAutMulIso x y)]
    rw [show hpres _ (mul_mem (repAut_mem x) (repAut_mem y)) = presFactors_mul (repAut_mem x)
      (hpres _ _) (repAut_mem y) (hpres _ _) from rfl, classB_mul]

end

section
variable (hpres : ∀ (α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))), PresFactors hα)
include hpres

/-- `Ψ̄_A : Out_typ(L(A × B)) → Out_typ(L(A))`. -/
noncomputable def psiA : OutTyp p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) →*
    OutTyp p (SA : Subgroup A) :=
  (natIsoCon p _).lift (compA hpres) (by
    rintro x y ⟨e⟩
    exact classA_eq_of_iso (repAut_mem x) (hpres _ _) (repAut_mem y) (hpres _ _)
      ((Classical.choice (repAut_iso x)).symm ≪≫ e ≪≫ Classical.choice (repAut_iso y)))

/-- `Ψ̄_B : Out_typ(L(A × B)) → Out_typ(L(B))`. -/
noncomputable def psiB : OutTyp p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) →*
    OutTyp p (SB : Subgroup B) :=
  (natIsoCon p _).lift (compB hpres) (by
    rintro x y ⟨e⟩
    exact classB_eq_of_iso (repAut_mem x) (hpres _ _) (repAut_mem y) (hpres _ _)
      ((Classical.choice (repAut_iso x)).symm ≪≫ e ≪≫ Classical.choice (repAut_iso y)))

variable {sA : OutTyp p (SA : Subgroup A) →* Out A} (hsA : (kappa p SA).comp sA = MonoidHom.id _)
  {sB : OutTyp p (SB : Subgroup B) →* Out B} (hsB : (kappa p SB).comp sB = MonoidHom.id _)
include hsA hsB

/-- **The splitting** (AOV, proof of Theorem 3.6, on `Out⁰_typ`). -/
theorem split_two : (kappa p (prodSylow SA SB)).comp
    (outProd.comp ((sA.prodMap sB).comp ((psiA hpres).prod (psiB hpres)))) = MonoidHom.id _ := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (natIsoCon p _).mk'_surjective z
  set α := repAut x
  have hα := repAut_mem x
  have hf := hpres α hα
  obtain ⟨ω⟩ := repAut_iso x
  obtain ⟨γA, hA, eA⟩ := exists_rep_normalizing SA (sA (psiA hpres ((natIsoCon p _).mk' x)))
  obtain ⟨γB, hB, eB⟩ := exists_rep_normalizing SB (sB (psiB hpres ((natIsoCon p _).mk' x)))
  have kA : kappaElt p γA hA = autClass (lautA_mem hα hf) := by
    rw [← kappa_mk p SA γA hA, eA]
    exact DFunLike.congr_fun hsA _
  have kB : kappaElt p γB hB = autClass (lautB_mem hα hf) := by
    rw [← kappa_mk p SB γB hB, eB]
    exact DFunLike.congr_fun hsB _
  obtain ⟨ωA⟩ := (natIsoCon p _).eq.1 kA
  obtain ⟨ωB⟩ := (natIsoCon p _).eq.1 kB
  change kappa p (prodSylow SA SB) (outProd (sA (psiA hpres ((natIsoCon p _).mk' x)),
    sB (psiB hpres ((natIsoCon p _).mk' x)))) = _
  rw [← eA, ← eB, outProd_mk, kappa_mk p (prodSylow SA SB) _ (prodCongr_mem hA hB),
    ← autClass_eq_kappaElt]
  rw [autClass_congr (mapAut_prodCongr hA hB) _
    (mul_mem (phiAut_mem (mapAut_mem p γA hA)) (phiBAut_mem (mapAut_mem p γB hB))),
    autClass_mul (phiAut_mem (mapAut_mem p γA hA)) (phiBAut_mem (mapAut_mem p γB hB)),
    autClass_phiAut_eq (mapAut_mem p γA hA) (lautA_mem hα hf) ωA,
    autClass_phiBAut_eq (mapAut_mem p γB hB) (lautB_mem hα hf) ωB, ← autClass_decomp hα hf]
  exact ((natIsoCon p _).eq.2 ⟨ω⟩).symm

end

end AndersenOliverVentura.Tame
