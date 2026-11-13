import CFSGOutside.AOVTame.PiSplit
import CFSGOutside.AOVTame.MinTame

/-!
# AOV tameness: assembling a tame realization from tame minimal factors (AOV Theorem 3.7)

Let `G` satisfy `Good T`, and suppose every minimal direct factor `X` of `T` has `F_X(G)` tame.
Group the minimal factors into isomorphism classes `c`, choose a tame realization `H_c` of each
class, and set `G' = ∏_c H_c^{ι_c}`, where `ι_c` is the set of minimal factors in the class `c`.
Then `F_T(G) ≅ F_{T'}(G')` (`MinDec.realizedBy_piE`). Every `α ∈ Aut_typ^I(L(G'))` induces an
automorphism of `F_T(G)` which permutes the minimal factors and preserves their classes
(`IsMinFactor.emap`, `fusionIso_restrict`); so `α` permutes the coordinate subgroups within each
block, and `pi_split` gives a splitting of `κ_{G'}`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

/-- The isomorphism `S ≃ T` of a realization `E : S → G` with image `T`. -/
noncomputable def isoOfRealized {S : Type*} [Group S] {F : FusionSystem S} {G : Type*} [Group G]
    {T : Subgroup G} {E : S →* G} (hE : Function.Injective E) (hr : E.range = T)
    (hR : RealizedBy F E) : FusionIso F (ofGroup G T) where
  toMulEquiv := (MonoidHom.ofInjective hE).trans (MulEquiv.subgroupCongr hr)
  hom_iff P Q φ := by
    have he : ∀ x, ((((MonoidHom.ofInjective hE).trans (MulEquiv.subgroupCongr hr)) x : T) : G) =
        E x := fun x => by
      change ((MonoidHom.ofInjective hE x : E.range) : G) = E x
      rw [MonoidHom.ofInjective_apply]
    rw [iso_ofGroup_iff, hR]
    simp only [he]

lemma isoOfRealized_apply {S : Type*} [Group S] {F : FusionSystem S} {G : Type*} [Group G]
    {T : Subgroup G} {E : S →* G} (hE : Function.Injective E) (hr : E.range = T)
    (hR : RealizedBy F E) (x : S) : (((isoOfRealized hE hr hR).toMulEquiv x : T) : G) = E x := by
  change ((MonoidHom.ofInjective hE x : E.range) : G) = E x
  rw [MonoidHom.ofInjective_apply]

section Curry
variable {m : ℕ} {ι : Fin m → Type} [∀ i, DecidableEq (ι i)] {H : Fin m → Type}
  [∀ i, Group (H i)]

/-- `∏_{(i,x)} H_i ≃ ∏_i H_i^{ι_i}`. -/
def curryMul : (∀ j : (Σ i, ι i), H j.1) ≃* ∀ i, ι i → H i where
  toFun f i x := f ⟨i, x⟩
  invFun g j := g j.1 j.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

lemma curryMul_single (i : Fin m) (x : ι i) (v : H i) :
    curryMul (Pi.mulSingle (⟨i, x⟩ : Σ i, ι i) v : ∀ j : (Σ i, ι i), H j.1) =
      Pi.mulSingle i (Pi.mulSingle x v) := by
  funext i' x'
  change (Pi.mulSingle (⟨i, x⟩ : Σ i, ι i) v : ∀ j : (Σ i, ι i), H j.1) ⟨i', x'⟩ = _
  by_cases hi : i' = i
  · subst hi
    by_cases hx : x' = x
    · subst hx; simp
    · have : (⟨i', x'⟩ : Σ i, ι i) ≠ ⟨i', x⟩ := fun h => hx (eq_of_heq (Sigma.mk.inj h).2)
      rw [Pi.mulSingle_eq_of_ne this, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hx]
  · have : (⟨i', x'⟩ : Σ i, ι i) ≠ ⟨i, x⟩ := fun h => hi (Sigma.mk.inj h).1
    rw [Pi.mulSingle_eq_of_ne this, Pi.mulSingle_eq_of_ne hi]
    rfl

end Curry

section Assemble
variable [GoldschmidtTheoremA] [AlperinFusion] {G : Type} [Group G] [Finite G] {T : Sylow 2 G}
  (hG : Good T)

/-- Isomorphism of the fusion systems of two minimal factors. -/
def minSetoid (T : Sylow 2 G) : Setoid (MinF T) where
  r X Y := Nonempty (FusionIso (ofGroup G (X : Subgroup G)) (ofGroup G (Y : Subgroup G)))
  iseqv := ⟨fun X => fusionIso_of_realizedBy (subtype_injective _) (range_subtype _)
      (realizedBy_subtype' _),
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

include hG

open Classical in
/-- **AOV Theorem 3.7 (group form), with a property `Pr` of the realizing groups** closed under
products of powers. -/
theorem tamelyRealizes_of_minFactors' (Pr : ∀ (H : Type) [Group H], Prop)
    (hPr : ∀ (m : ℕ) (bs : Fin m → Blk), (∀ i, Pr (bs i).H) → Pr (PG bs))
    (htame : ∀ X : MinF T, ∃ (H : Type) (_ : Group H) (_ : Finite H) (S : Sylow 2 H),
      Pr H ∧ TamelyRealizes 2 (ofGroup G (X : Subgroup G)) H S) :
    ∃ (G' : Type) (_ : Group G') (_ : Finite G') (T' : Sylow 2 G'),
      Pr G' ∧ TamelyRealizes 2 (ofGroup G (T : Subgroup G)) G' T' := by
  -- the classes
  let Q := Quotient (minSetoid T)
  let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  set m := Fintype.card Q
  let cls : MinF T → Fin m := fun X => eQ (Quotient.mk _ X)
  let X₀ : Fin m → MinF T := fun i => (eQ.symm i).out
  have hX₀ : ∀ i, cls (X₀ i) = i := fun i => by simp [cls, X₀]
  choose H hgH hfH S hPH htr using fun i => htame (X₀ i)
  let ι : Fin m → Type := fun i => {X : MinF T // cls X = i}
  let bs : Fin m → Blk := fun i => ⟨ι i, H i, S i⟩
  -- realization of `F_T(G)` by `∏_{(i,X)} H_i`
  let J := Σ i, ι i
  let eJ : J ≃ MinF T := Equiv.sigmaFiberEquiv cls
  have hdec := (minDec_minF hG).reindex eJ
  let Xj : J → Subgroup G := fun j => ((j.2 : MinF T) : Subgroup G)
  have hcls : ∀ j : J, Nonempty (FusionIso (ofGroup G (Xj j)) (ofGroup G ((X₀ j.1 : MinF T) :
      Subgroup G))) := by
    intro j
    have : Quotient.mk (minSetoid T) (j.2 : MinF T) = Quotient.mk _ (X₀ j.1) := by
      apply eQ.injective
      change cls j.2 = cls (X₀ j.1)
      rw [hX₀, j.2.2]
    exact Quotient.exact this
  let fj : ∀ j : J, FusionIso (ofGroup G (Xj j)) (ofGroup (H j.1) (S j.1 : Subgroup (H j.1))) :=
    fun j => (Classical.choice (hcls j)).trans (Classical.choice (htr j.1).1)
  let E : ∀ j : J, Xj j →* H j.1 := fun j =>
    (S j.1 : Subgroup (H j.1)).subtype.comp (fj j).toMulEquiv.toMonoidHom
  have hE : ∀ j, Function.Injective (E j) := fun j =>
    (subtype_injective _).comp (fj j).toMulEquiv.injective
  have hEr : ∀ j, (E j).range = S j.1 := fun j => (realizedBy_of_fusionIso (fj j)).2.1
  have hER : ∀ j, RealizedBy (ofGroup G (Xj j)) (E j) := fun j =>
    (realizedBy_of_fusionIso (fj j)).2.2
  have hR := hdec.realizedBy_piE hG E hE hER
  -- transport to `∏_i H_i^{ι_i}`
  let E' : (T : Subgroup G) →* PG bs := (curryMul (H := H)).toMonoidHom.comp (hdec.piE E)
  have hE'i : Function.Injective E' := curryMul.injective.comp (hdec.piE_injective E hE)
  have hE'r : E'.range = PT bs := by
    rw [MonoidHom.range_comp, hdec.piE_range E hEr]
    ext g
    rw [mem_PT]
    constructor
    · rintro ⟨f, hf, rfl⟩ i x
      exact (mem_pi _).1 hf ⟨i, x⟩ (Set.mem_univ _)
    · intro hg
      refine ⟨curryMul.symm g, (mem_pi _).2 fun j _ => hg j.1 j.2, ?_⟩
      simp
  have hR' : RealizedBy (ofGroup G (T : Subgroup G)) E' := realizedBy_mulEquiv hR _
  let ψ := isoOfRealized hE'i hE'r hR'
  -- `κ_{G'}` splits
  have hSne : ∀ i, ((bs i).S : Subgroup (bs i).H) ≠ ⊥ := by
    intro i h
    apply (X₀ i).2.2.1
    obtain ⟨f⟩ := (htr i).1
    have hc := Nat.card_congr f.toMulEquiv.toEquiv
    have h1 : Nat.card (S i : Subgroup (H i)) = 1 := by
      change Nat.card ((bs i).S : Subgroup (bs i).H) = 1
      rw [h]; exact Subgroup.card_bot
    rw [h1] at hc
    exact Subgroup.eq_bot_of_card_eq _ hc
  have hsp : ∀ i, ∃ s : OutTyp 2 ((bs i).S : Subgroup (bs i).H) →* Out (bs i).H,
      (kappa 2 (bs i).S).comp s = MonoidHom.id _ := fun i => (htr i).2
  have hst : StableAll bs := by
    intro α hα i x
    let Φ := ψ.trans ((betaIso hα).trans ψ.symm)
    have hXT : ((x : MinF T) : Subgroup G) ≤ T := (x.1.2.1).le
    have hmin := IsMinFactor.emap Φ x.1.2
    let X'' : MinF T := ⟨_, hmin⟩
    have hcl : cls X'' = i := by
      rw [← x.2]
      change eQ _ = eQ _
      congr 1
      exact (Quotient.sound (fusionIso_restrict Φ hXT) : _).symm
    refine ⟨⟨X'', hcl⟩, fun s hs => ?_⟩
    let j : J := ⟨i, x⟩
    have hsr : s ∈ (E j).range := by rw [hEr]; exact hs
    obtain ⟨t₀, ht₀⟩ := hsr
    let t : (T : Subgroup G) := ⟨t₀, hdec.le j t₀.2⟩
    have hEt : E' t = Pi.mulSingle i (Pi.mulSingle x s) := by
      change curryMul (hdec.piE E ⟨(t₀ : G), hdec.le j t₀.2⟩) = _
      rw [hdec.piE_single E t₀.2]
      change curryMul (Pi.mulSingle j (E j t₀)) = _
      rw [ht₀]
      exact curryMul_single (ι := ι) (H := H) i x s
    have hψt : ψ.toMulEquiv t = ⟨_, single_mem bs i x hs⟩ :=
      Subtype.ext ((isoOfRealized_apply hE'i hE'r hR' t).trans hEt)
    set t₁ := Φ.toMulEquiv t with ht₁def
    have ht₁ : (t₁ : G) ∈ ((X'' : MinF T) : Subgroup G) := mem_emap_self t t₀.2
    let j' : J := ⟨i, ⟨X'', hcl⟩⟩
    refine ⟨E j' ⟨(t₁ : G), ht₁⟩, ?_⟩
    have hb : beta hα (ψ.toMulEquiv t) = ψ.toMulEquiv t₁ := by
      rw [ht₁def]
      change beta hα (ψ.toMulEquiv t) =
        ψ.toMulEquiv (ψ.toMulEquiv.symm (beta hα (ψ.toMulEquiv t)))
      rw [MulEquiv.apply_symm_apply]
    have hE't₁ : E' t₁ = Pi.mulSingle i (Pi.mulSingle (⟨X'', hcl⟩ : ι i) (E j' ⟨(t₁ : G), ht₁⟩)) := by
      change curryMul (hdec.piE E ⟨(t₁ : G), hdec.le j' ht₁⟩) = _
      rw [hdec.piE_single E (i := j') ht₁]
      exact curryMul_single (ι := ι) (H := H) i _ _
    rw [← hψt]
    change ((beta hα (ψ.toMulEquiv t) : _) : PG bs) = _
    rw [hb, isoOfRealized_apply hE'i hE'r hR', hE't₁]
  obtain ⟨s', hs'⟩ := pi_split m bs hSne hsp hst
  exact ⟨PG bs, inferInstance, inferInstance, PT bs, hPr m bs hPH, ⟨ψ⟩, s', hs'⟩

/-- **AOV Theorem 3.7 (group form).** If every minimal direct factor of `T` has a tame fusion
system, then `F_T(G)` is tamely realized. -/
theorem tamelyRealizes_of_minFactors
    (htame : ∀ X : MinF T, ∃ (H : Type) (_ : Group H) (_ : Finite H) (S : Sylow 2 H),
      TamelyRealizes 2 (ofGroup G (X : Subgroup G)) H S) :
    ∃ (G' : Type) (_ : Group G') (_ : Finite G') (T' : Sylow 2 G'),
      TamelyRealizes 2 (ofGroup G (T : Subgroup G)) G' T' := by
  obtain ⟨G', i1, i2, T', -, ht⟩ := tamelyRealizes_of_minFactors' hG (fun _ _ => True)
    (fun _ _ _ => trivial) (fun X => by
      obtain ⟨H, j1, j2, S, h⟩ := htame X
      exact ⟨H, j1, j2, S, trivial, h⟩)
  exact ⟨G', i1, i2, T', ht⟩

end Assemble

end AndersenOliverVentura.Tame
