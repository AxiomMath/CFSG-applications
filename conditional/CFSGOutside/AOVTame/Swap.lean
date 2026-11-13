import CFSGOutside.AOVTame.PsiFactor
import CFSGOutside.AOVTame.ConjIso

/-!
# AOV tameness: the second component `α_B` of a factor-preserving `α`, via `A × B ≅ B × A`
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]

variable (SA : Sylow p A) (SB : Sylow p B)

lemma map_prodComm_prodSylow :
    ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map
      (MulEquiv.prodComm : A × B ≃* B × A).toMonoidHom =
      ((prodSylow SB SA : Sylow p (B × A)) : Subgroup (B × A)) := by
  ext ⟨b, a⟩
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, e⟩
    change (y, x) = (b, a) at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨hy, hx⟩
  · rintro ⟨hb, ha⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

variable {SA SB}

section
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)

/-- `α` transported to `L(B × A)`. -/
noncomputable def swapAut (α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    LAut p ((prodSylow SB SA : Sylow p (B × A)) : Subgroup (B × A)) :=
  conjIso MulEquiv.prodComm (map_prodComm_prodSylow SA SB) α

include hα in
lemma swapAut_mem : swapAut α ∈ autTypI p ((prodSylow SB SA : Sylow p (B × A)) : Subgroup (B × A)) :=
  conjIso_mem _ _ hα

lemma betaFun_swapAut {b : B} {a : A} (hb : b ∈ (SB : Subgroup B)) (ha : a ∈ (SA : Subgroup A)) :
    ((betaFun (swapAut_mem hα) ⟨(b, a), mem_prodSylow hb ha⟩ : _) : B × A) =
      (((betaFun hα ⟨(a, b), mem_prodSylow ha hb⟩ : _) : A × B).2,
        ((betaFun hα ⟨(a, b), mem_prodSylow ha hb⟩ : _) : A × B).1) := by
  have := betaFun_conjIso MulEquiv.prodComm (map_prodComm_prodSylow SA SB) hα
    ⟨(a, b), mem_prodSylow ha hb⟩ (mem_prodSylow hb ha)
  exact this

include hf in
lemma presFactors_swap : PresFactors (swapAut_mem hα) := by
  constructor
  · intro b hb
    rw [betaFun_swapAut hα hb (one_mem _)]
    exact hf.snd b hb
  · intro a ha
    rw [betaFun_swapAut hα (one_mem _) ha]
    exact hf.fst a ha

include hf in
lemma bA_swap {b : B} (hb : b ∈ (SB : Subgroup B)) :
    bA (swapAut_mem hα) b hb = bB hα b hb := by
  unfold bA bB
  rw [betaFun_swapAut hα hb (one_mem _)]

variable (SA) in
/-- `α_B ∈ Aut_typ^I(L(B))`. -/
noncomputable def lautB : LAut p (SB : Subgroup B) :=
  lautA SA (swapAut_mem hα) (presFactors_swap hα hf)

lemma lautB_mem : lautB SA hα hf ∈ autTypI p (SB : Subgroup B) := lautA_mem _ _

lemma betaFun_lautB (y : (SB : Subgroup B)) :
    ((betaFun (lautB_mem hα hf) y : _) : B) = bB hα y y.2 := by
  rw [← bA_swap hα hf]
  exact betaFun_lautA (swapAut_mem hα) (presFactors_swap hα hf) y

end

end AndersenOliverVentura.Tame
