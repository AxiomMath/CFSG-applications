import CFSGOutside.AOVTame.WreathMain
import CFSGOutside.AOVTame.KappaCompat

/-!
# AOV tameness: tools for products of blocks

* `β(Φ(α, Id))(a, b) = (β(α)(a), b)` and `β(Φ(Id, γ))(a, b) = (a, β(γ)(b))`;
* a splitting of `κ_G` transports along group isomorphisms;
* `κ_G` splits for the trivial group;
* the Sylow subgroup `∏ S_i` of a dependent product `∏ K_i`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

section PhiBeta
variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

/-- `β(Φ(α, Id))(a, b) = (β(α)(a), b)`. -/
lemma betaFun_phiAut {α : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))
    {a : A} (ha : a ∈ (SA : Subgroup A)) {b : B} (hb : b ∈ (SB : Subgroup B)) :
    ((betaFun (phiAut_mem (SB := SB) hα) ⟨(a, b), mem_prodSylow ha hb⟩ : _) : A × B) =
      ((betaFun hα ⟨a, ha⟩ : A), b) := by
  have hα' := phiAut_mem (SB := SB) hα
  set P := proj₁ (SB := SB) (topObj (prodSylow SA SB))
  have haP : a ∈ P.val := ⟨(a, b), mem_prodSylow ha hb, rfl⟩
  obtain ⟨hb', e1⟩ := map_mk_delta hα P haP
  have hg : ((a, b) : A × B) ∈ transporter (topObj (prodSylow SA SB)).val
      (topObj (prodSylow SA SB)).val := mem_transporter_self (mem_prodSylow ha hb)
  have e2 := phiMor_mk hα hg (mem_transporter_self hb') e1
  have e3 := (map_mk_top hα' ⟨(a, b), mem_prodSylow ha hb⟩).symm.trans e2
  have hyT : (((betaFun hα ⟨a, P.2.1 haP⟩ : A), b) : A × B) ∈
      ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
    mem_prodSylow (betaFun hα _).2 hb
  have := beta_unique hα' (betaFun hα' _).2 hyT e3
  exact this

/-- `β(Φ(Id, γ))(a, b) = (a, β(γ)(b))`. -/
lemma betaFun_phiBAut {γ : LAut p (SB : Subgroup B)} (hγ : γ ∈ autTypI p (SB : Subgroup B))
    {a : A} (ha : a ∈ (SA : Subgroup A)) {b : B} (hb : b ∈ (SB : Subgroup B)) :
    ((betaFun (phiBAut_mem (SA := SA) hγ) ⟨(a, b), mem_prodSylow ha hb⟩ : _) : A × B) =
      (a, (betaFun hγ ⟨b, hb⟩ : B)) := by
  have h1 := betaFun_conjIso (MulEquiv.prodComm : B × A ≃* A × B) (map_prodComm_prodSylow SB SA)
    (phiAut_mem (SB := SA) hγ) ⟨(b, a), mem_prodSylow hb ha⟩ (mem_prodSylow ha hb)
  have h2 := betaFun_phiAut (SB := SA) hγ hb ha
  refine h1.trans ?_
  change MulEquiv.prodComm ((betaFun (phiAut_mem (SB := SA) hγ) ⟨(b, a), _⟩ : _) : B × A) = _
  rw [h2]; rfl

end PhiBeta

section Transport
variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]

/-- A group isomorphism carrying `T` to `T'` is fusion-preserving. -/
lemma fusionHom_mulEquiv {T : Sylow p G} {T' : Sylow p G'} (e : G ≃* G')
    (hT : (T : Subgroup G).map e.toMonoidHom = T') : FusionHom p T T' e.toMonoidHom where
  map_eq := hT
  inj x _ y _ h := e.injective h
  fus P _ k hk := by
    refine ⟨e.symm k, fun x hx => ?_, fun x _ => by simp⟩
    have h1 := hk x hx
    rw [← hT] at h1
    obtain ⟨y, hy, hye⟩ := h1
    have hye' : e y = k * e x * k⁻¹ := hye
    have : e.symm k * x * (e.symm k)⁻¹ = y := e.injective (by rw [hye']; simp)
    rw [this]; exact hy

/-- `β ↦ e β e⁻¹ : Aut(G) → Aut(G')`. -/
def autConj (e : G ≃* G') : MulAut G →* MulAut G' where
  toFun β := e.symm.trans (β.trans e)
  map_one' := by ext; simp
  map_mul' β β' := by ext; simp

lemma autConj_conj (e : G ≃* G') (g : G) : autConj e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x; simp [autConj]

/-- `Out(G) → Out(G')` induced by `e`. -/
noncomputable def outConj (e : G ≃* G') : Out G →* Out G' :=
  QuotientGroup.map _ _ (autConj e) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨e g, (autConj_conj e g).symm⟩)

/-- **A splitting of `κ` transports along isomorphisms.** -/
theorem kappa_split_mulEquiv {T : Sylow p G} {T' : Sylow p G'} (e : G ≃* G')
    (hT : (T : Subgroup G).map e.toMonoidHom = T') {s : OutTyp p (T : Subgroup G) →* Out G}
    (hs : (kappa p T).comp s = MonoidHom.id _) :
    ∃ s' : OutTyp p (T' : Subgroup G') →* Out G', (kappa p T').comp s' = MonoidHom.id _ := by
  have hf := fusionHom_mulEquiv e hT
  refine ⟨(outConj e).comp (s.comp hf.typIso.symm.outTyp), MonoidHom.ext fun z => ?_⟩
  set z₀ := hf.typIso.symm.outTyp z
  obtain ⟨β, hβ, hβe⟩ := exists_rep_normalizing T (s z₀)
  have hκ : kappaElt p β hβ = z₀ := by
    rw [← kappa_mk, hβe]; exact DFunLike.congr_fun hs z₀
  have hβ' : (T' : Subgroup G').map (autConj e β).toMonoidHom = T' := by
    rw [← hT, map_map, show (autConj e β).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp β.toMonoidHom from by ext x; simp [autConj], ← map_map, hβ]
  change kappa p T' (outConj e (s z₀)) = z
  rw [← hβe]
  change kappa p T' (QuotientGroup.mk (autConj e β)) = z
  rw [kappa_mk p T' _ hβ', ← hf.outTyp_kappaElt β hβ (autConj e β) hβ' (fun x => by simp [autConj]),
    hκ]
  exact hf.typIso.outTyp_outTyp_symm z

end Transport

section Trivial
variable {G : Type} [Group G] [Finite G] [Subsingleton G] {p : ℕ} [Fact p.Prime]

instance subsingleton_subgroup : Subsingleton (Subgroup G) :=
  ⟨fun H K => by
    ext x
    rw [Subsingleton.elim x 1]
    exact ⟨fun _ => one_mem _, fun _ => one_mem _⟩⟩

lemma hom_eq_of_subsingleton {S : Subgroup G} {P Q : Obj p S} (f g : P ⟶ Q) : f = g := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep (f : Mor p P.val Q.val)
  obtain ⟨g, rfl⟩ := Quotient.exists_rep (g : Mor p P.val Q.val)
  congr 1
  exact Subtype.ext (Subsingleton.elim _ _)

lemma outTyp_subsingleton (S : Subgroup G) : Subsingleton (OutTyp p S) :=
  ⟨fun x y => by
    obtain ⟨x, rfl⟩ := Con.mk'_surjective x
    obtain ⟨y, rfl⟩ := Con.mk'_surjective y
    apply (natIsoCon p S).eq.2
    exact ⟨NatIso.ofComponents (fun P => eqToIso (Obj.ext (Subsingleton.elim (α := Subgroup G) _ _)))
      (fun _ => hom_eq_of_subsingleton _ _)⟩⟩

/-- `κ` splits for the trivial group. -/
theorem kappa_split_subsingleton (T : Sylow p G) :
    ∃ s : OutTyp p (T : Subgroup G) →* Out G, (kappa p T).comp s = MonoidHom.id _ :=
  ⟨1, MonoidHom.ext fun z => (outTyp_subsingleton (p := p) (T : Subgroup G)).elim _ _⟩

end Trivial

section PiSylow
variable {p : ℕ} [hp : Fact p.Prime] {J : Type} [Fintype J] {K : J → Type} [∀ j, Group (K j)]
  [∀ j, Finite (K j)]

/-- `∏ S_j ≃ ∏ ↥S_j`. -/
def piSubEquiv (S : ∀ j, Subgroup (K j)) : Subgroup.pi Set.univ S ≃ ∀ j, S j where
  toFun x j := ⟨(x : ∀ j, K j) j, (mem_pi _).1 x.2 j (Set.mem_univ j)⟩
  invFun y := ⟨fun j => y j, (mem_pi _).2 fun j _ => (y j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma index_piD (S : ∀ j, Subgroup (K j)) :
    (Subgroup.pi Set.univ S).index = ∏ j, (S j).index := by
  have h1 := (Subgroup.pi Set.univ S).card_mul_index
  have h2 : Nat.card (Subgroup.pi Set.univ S) = ∏ j, Nat.card (S j) := by
    rw [← Nat.card_pi]; exact Nat.card_congr (piSubEquiv S)
  have h3 : ∏ j, Nat.card (K j) = ∏ j, (Nat.card (S j) * (S j).index) :=
    Finset.prod_congr rfl (fun j _ => ((S j).card_mul_index).symm)
  rw [Nat.card_pi, h2, h3, Finset.prod_mul_distrib] at h1
  exact Nat.eq_of_mul_eq_mul_left (Finset.prod_pos fun j _ => Nat.card_pos) h1

/-- The Sylow subgroup `∏_j S_j` of `∏_j K_j`. -/
noncomputable def piSylowD (S : ∀ j, Sylow p (K j)) : Sylow p (∀ j, K j) :=
  IsPGroup.toSylow (P := Subgroup.pi Set.univ (fun j => (S j : Subgroup (K j))))
    (by
      intro x
      have hx : ∀ j, ∃ k : ℕ, (x : ∀ j, K j) j ^ (p ^ k) = 1 := fun j => by
        obtain ⟨k, hk⟩ := (S j).isPGroup' ⟨(x : ∀ j, K j) j, (mem_pi _).1 x.2 j (Set.mem_univ j)⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      choose k hk using hx
      refine ⟨∑ j, k j, Subtype.ext (funext fun j => ?_)⟩
      have hdvd : p ^ k j ∣ p ^ (∑ i, k i) :=
        pow_dvd_pow p (Finset.single_le_sum (fun i _ => Nat.zero_le (k i)) (Finset.mem_univ j))
      obtain ⟨c, hc⟩ := hdvd
      change ((x : ∀ j, K j) ^ p ^ (∑ i, k i)) j = 1
      rw [Pi.pow_apply, hc, pow_mul, hk j, one_pow])
    (by
      rw [index_piD]
      intro h
      obtain ⟨j, -, hj⟩ := (Prime.dvd_finset_prod_iff (Nat.Prime.prime hp.out) _).1 h
      exact (S j).not_dvd_index hj)

lemma mem_piSylowD {S : ∀ j, Sylow p (K j)} {x : ∀ j, K j} :
    x ∈ (piSylowD S : Subgroup (∀ j, K j)) ↔ ∀ j, x j ∈ (S j : Subgroup (K j)) := by
  change x ∈ Subgroup.pi Set.univ _ ↔ _
  simp [mem_pi]

end PiSylow

end AndersenOliverVentura.Tame
