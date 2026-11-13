import CFSGOutside.AOVTame.Phi

/-!
# AOV tameness: `Φ(-, Id)` on `Out_typ`
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

lemma Functor.map_heq' {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') {m : X ⟶ Y} {m' : X' ⟶ Y'} (h : HEq m m') :
    HEq (F.map m) (F.map m') := by
  subst hX hY; cases h; rfl

lemma mk_rel_of_heq {G : Type*} [Group G] {p : ℕ} {A A' B B' : Subgroup G} (hA : A = A')
    (hB : B = B') {g g' : G} {hg : g ∈ transporter A B} {hg' : g' ∈ transporter A' B'}
    (h : HEq (mk p g hg) (mk p g' hg')) : g⁻¹ * g' ∈ opCent p A := by
  subst hA hB
  exact (mk_eq_mk p).1 (eq_of_heq h)

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

/-- The automorphism `c_n` of `L(A)` for `n ∈ N_A(S_A)`. -/
noncomputable def conjAut (n : A) (hn : (SA : Subgroup A).map (MulAut.conj n).toMonoidHom = SA) :
    LAut p (SA : Subgroup A) := mapIso p (MulAut.conj n) hn

lemma conjAut_mem (n : A) (hn : (SA : Subgroup A).map (MulAut.conj n).toMonoidHom = SA) :
    conjAut n hn ∈ autTypI p (SA : Subgroup A) := by
  refine ⟨isIsotypical_mapFunctor p _ hn, fun P Q hPQ => ⟨?_, ?_⟩⟩
  · exact map_mono hPQ
  · exact mk_congr p (map_one _) _ _

section Mul
variable {α α' : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))
  (hα' : α' ∈ autTypI p (SA : Subgroup A))
include hα hα'

lemma phiObj_mul (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    phiObj SB (mul_mem hα hα') P = phiObj SB hα (phiObj SB hα' P) := by
  apply Obj.ext
  ext z
  change z ∈ bmap _ P.val ↔ z ∈ bmap _ (bmap _ P.val)
  rw [mem_bmap_bX_iff, mem_bmap_bX_iff]
  constructor
  · rintro ⟨x, hx, h1, h2, rfl⟩
    refine ⟨_, (mem_bmap_bX_iff hα').2 ⟨x, hx, h1, h2, rfl⟩, (betaFun hα' ⟨x.1, h1⟩).2, h2, ?_⟩
    rw [betaFun_mul_aut hα hα']
  · rintro ⟨w, hw, h1, h2, rfl⟩
    obtain ⟨x, hx, h1', h2', rfl⟩ := (mem_bmap_bX_iff hα').1 hw
    refine ⟨x, hx, h1', h2', ?_⟩
    rw [betaFun_mul_aut hα hα']

lemma phiFunctor_mul :
    phiFunctor SB (mul_mem hα hα') = phiFunctor SB hα' ⋙ phiFunctor SB hα := by
  apply Functor.hext (fun P => phiObj_mul hα hα' P)
  rintro P Q ⟨⟨g, hg⟩⟩
  -- representatives
  obtain ⟨⟨h', hh'⟩, eh'⟩ := Quotient.exists_rep (α'.fn.map (show proj₁ P ⟶ proj₁ Q from
    mk p g.1 (mem_transporter_fst hg)) : Mor p (α'.fn.obj (proj₁ P)).val (α'.fn.obj (proj₁ Q)).val)
  obtain ⟨⟨h'', hh''⟩, eh''⟩ := Quotient.exists_rep ((α * α').fn.map (show proj₁ P ⟶ proj₁ Q from
    mk p g.1 (mem_transporter_fst hg)) :
      Mor p ((α * α').fn.obj (proj₁ P)).val ((α * α').fn.obj (proj₁ Q)).val)
  have e1 := phiMor_mk (mul_mem hα hα') hg hh'' eh''.symm
  have e2 := phiMor_mk hα' hg hh' eh'.symm
  have hg' := phi_transporter hα' hg hh' eh'.symm
  have hP' : proj₁ (phiObj SB hα' P) = α'.fn.obj (proj₁ P) := Obj.ext (phiObj_fst hα' P)
  have hQ' : proj₁ (phiObj SB hα' Q) = α'.fn.obj (proj₁ Q) := Obj.ext (phiObj_fst hα' Q)
  obtain ⟨⟨h, hh⟩, eh⟩ := Quotient.exists_rep (α.fn.map (show proj₁ (phiObj SB hα' P) ⟶
    proj₁ (phiObj SB hα' Q) from mk p (h', g.2).1 (mem_transporter_fst hg')) :
      Mor p (α.fn.obj (proj₁ (phiObj SB hα' P))).val (α.fn.obj (proj₁ (phiObj SB hα' Q))).val)
  have e3 := phiMor_mk hα hg' hh eh.symm
  change HEq (phiMor SB (mul_mem hα hα') (mk p g hg))
    (phiMor SB hα (phiMor SB hα' (mk p g hg)))
  rw [e1, e2, e3]
  -- compare `h''` and `h`
  have hheq : HEq ((α * α').fn.map (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)))
      (α.fn.map (show proj₁ (phiObj SB hα' P) ⟶ proj₁ (phiObj SB hα' Q) from
        mk p (h', g.2).1 (mem_transporter_fst hg'))) := by
    change HEq (α.fn.map (α'.fn.map _)) _
    apply Functor.map_heq' α.fn hP'.symm hQ'.symm
    rw [← eh']
    exact mk_heq p (congrArg Obj.val hP'.symm) (congrArg Obj.val hQ'.symm) rfl _ _
  rw [← eh'', ← eh] at hheq
  have hc := mk_rel_of_heq (congrArg Obj.val (congrArg α.fn.obj hP'.symm))
    (congrArg Obj.val (congrArg α.fn.obj hQ'.symm)) hheq
  apply mk_heq_of_mem p (congrArg Obj.val (phiObj_mul hα hα' P))
    (congrArg Obj.val (phiObj_mul hα hα' Q))
  have hc1 : h''⁻¹ * h ∈ opCent p ((phiObj SB (mul_mem hα hα') P).val.map (MonoidHom.fst A B)) := by
    rw [phiObj_fst (mul_mem hα hα')]; exact hc
  have hc2 : (g.2)⁻¹ * g.2 ∈ opCent p ((phiObj SB (mul_mem hα hα') P).val.map (MonoidHom.snd A B)) := by
    rw [inv_mul_cancel]; exact one_mem _
  have := opCent_pair hc1 hc2
  convert this using 1

end Mul

section Conj
variable (n : A) (hn : (SA : Subgroup A).map (MulAut.conj n).toMonoidHom = SA)

lemma betaFun_conjAut (x : (SA : Subgroup A)) :
    (betaFun (conjAut_mem n hn) x : A) = n * x * n⁻¹ := by
  obtain ⟨hb, e⟩ := map_mk_delta (conjAut_mem n hn) (topObj SA) (x := (x : A)) x.2
  have e' : (conjAut n hn).fn.map (show topObj SA ⟶ topObj SA from mk p x (mem_transporter_self x.2)) =
      mk p (MulAut.conj n x) (mem_transporter_map _ (mem_transporter_self x.2)) := rfl
  rw [e'] at e
  have h1 := (mk_eq_mk p).1 e
  have hxS : (MulAut.conj n x : A) ∈ ((conjAut n hn).fn.obj (topObj SA)).val := ⟨x, x.2, rfl⟩
  have h2 := eq_one_of_mem_opCent SA ((conjAut n hn).fn.obj (topObj SA)).2 h1
    (mul_mem (inv_mem (((conjAut n hn).fn.obj (topObj SA)).2.1 hxS)) (betaFun _ x).2)
  have : (betaFun (conjAut_mem n hn) x : A) = MulAut.conj n x := by
    rw [← mul_inv_cancel_left (MulAut.conj n (x : A)) (betaFun _ x : A), h2, mul_one]
  rw [this]; rfl

include hn in
lemma conj_pair_mem :
    ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map
      (MulAut.conj ((n, 1) : A × B)).toMonoidHom = (prodSylow SA SB : Sylow p (A × B)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : n * x.1 * n⁻¹ ∈ (SA : Subgroup A).map (MulAut.conj n).toMonoidHom := ⟨x.1, hx1, rfl⟩
      rw [hn] at this; exact this
    · simpa using hx2
  · rintro ⟨hz1, hz2⟩
    have : z.1 ∈ (SA : Subgroup A).map (MulAut.conj n).toMonoidHom := by rw [hn]; exact hz1
    obtain ⟨y, hy, ey⟩ := this
    refine ⟨(y, z.2), ⟨hy, hz2⟩, Prod.ext ?_ (by simp)⟩
    simpa using ey

lemma phiFunctor_conjAut :
    phiFunctor SB (conjAut_mem n hn) = mapFunctor p (MulAut.conj ((n, 1) : A × B)) (conj_pair_mem (SB := SB) n hn) := by
  have hobj : ∀ P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)),
      (phiObj SB (conjAut_mem n hn) P).val = P.val.map (MulAut.conj ((n, 1) : A × B)).toMonoidHom := by
    intro P
    ext z
    change z ∈ bmap _ P.val ↔ _
    rw [mem_bmap_bX_iff]
    constructor
    · rintro ⟨x, hx, h1, h2, rfl⟩
      refine ⟨x, hx, Prod.ext ?_ (by simp)⟩
      simp [betaFun_conjAut]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, (P.2.1 hx).1, (P.2.1 hx).2, Prod.ext ?_ (by simp)⟩
      simp [betaFun_conjAut]
  apply Functor.hext (fun P => Obj.ext (hobj P))
  rintro P Q ⟨⟨g, hg⟩⟩
  have e : (conjAut n hn).fn.map (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) =
      mk p (MulAut.conj n g.1) (mem_transporter_map _ (mem_transporter_fst hg)) := rfl
  change HEq (phiMor SB (conjAut_mem n hn) (mk p g hg)) _
  rw [phiMor_mk (conjAut_mem n hn) hg _ e]
  exact mk_heq p (hobj P) (hobj Q) (Prod.ext (by simp) (by simp)) _ _

end Conj

lemma phiFunctor_one :
    phiFunctor SB (one_mem (autTypI p (SA : Subgroup A))) = 𝟭 _ := by
  have hobj : ∀ P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)),
      (phiObj SB (one_mem (autTypI p (SA : Subgroup A))) P).val = P.val := by
    intro P
    ext z
    change z ∈ bmap _ P.val ↔ _
    rw [mem_bmap_bX_iff]
    constructor
    · rintro ⟨x, hx, h1, h2, rfl⟩
      rw [betaFun_one_aut]; exact hx
    · intro hz
      exact ⟨z, hz, (P.2.1 hz).1, (P.2.1 hz).2, by rw [betaFun_one_aut]⟩
  apply Functor.hext (fun P => Obj.ext (hobj P))
  rintro P Q ⟨⟨g, hg⟩⟩
  have e : (1 : LAut p (SA : Subgroup A)).fn.map
      (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) =
      mk p g.1 (mem_transporter_fst hg) := rfl
  change HEq (phiMor SB (one_mem (autTypI p (SA : Subgroup A))) (mk p g hg)) _
  rw [phiMor_mk (one_mem _) hg _ e]
  exact mk_heq p (hobj P) (hobj Q) rfl _ _

lemma phiFunctor_congr {α α' : LAut p (SA : Subgroup A)} (e : α = α')
    (hα : α ∈ autTypI p (SA : Subgroup A)) (hα' : α' ∈ autTypI p (SA : Subgroup A)) :
    phiFunctor SB hα = phiFunctor SB hα' := by
  subst e; rfl

variable (SB) in
/-- The class of `Φ(α, Id)` in `Out_typ(L(A × B))`. -/
noncomputable def phiClass {α : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A)) :
    OutTyp p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  (natIsoCon p _).mk' ⟨(phiAut SB hα).hom, by
    haveI := phiFunctor_isIso (SB := SB) hα
    exact ⟨(inferInstance : (phiFunctor SB hα).IsEquivalence), phiFunctor_isIsotypical hα⟩⟩

lemma phiClass_mul {α α' : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))
    (hα' : α' ∈ autTypI p (SA : Subgroup A)) :
    phiClass SB (mul_mem hα hα') = phiClass SB hα * phiClass SB hα' := by
  rw [phiClass, phiClass, phiClass, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Cat.ext
  exact phiFunctor_mul hα hα'

lemma phiClass_one : phiClass SB (one_mem (autTypI p (SA : Subgroup A))) = 1 := by
  rw [phiClass, ← map_one ((natIsoCon p _).mk')]
  congr 1
  apply Subtype.ext
  apply Cat.ext
  exact phiFunctor_one

lemma phiClass_eq_of_iso {α α' : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))
    (hα' : α' ∈ autTypI p (SA : Subgroup A)) (ω : α.fn ≅ α'.fn) :
    phiClass SB hα = phiClass SB hα' := by
  obtain ⟨n, hn, e⟩ := eq_conj_of_iso hα hα' ω
  have he : α' = conjAut n hn * α := LAut.ext_fn p _ e
  have h1 : phiClass SB hα' = phiClass SB (mul_mem (conjAut_mem n hn) hα) := by
    rw [phiClass, phiClass]
    congr 2
    apply Cat.ext
    exact phiFunctor_congr he hα' _
  rw [h1, phiClass_mul (conjAut_mem n hn) hα]
  have h2 : phiClass SB (conjAut_mem n hn) = 1 := by
    rw [← phiClass_one (SB := SB) (SA := SA)]
    apply (natIsoCon p _).eq.2
    refine ⟨eqToIso (phiFunctor_conjAut n hn) ≪≫ (conjNatIso p ((n, 1) : A × B) _).symm ≪≫
      eqToIso phiFunctor_one.symm⟩
  rw [h2, one_mul]

/-- An element of `Aut_typ^I` naturally isomorphic to a given isotypical self-equivalence. -/
noncomputable def repAut (x : typEquivs p (SA : Subgroup A)) : LAut p (SA : Subgroup A) :=
  haveI := x.2.1
  (exists_autTypI_iso x.1.toFunctor x.2.2).choose

lemma repAut_mem (x : typEquivs p (SA : Subgroup A)) : repAut x ∈ autTypI p (SA : Subgroup A) :=
  haveI := x.2.1
  (exists_autTypI_iso x.1.toFunctor x.2.2).choose_spec.1

lemma repAut_iso (x : typEquivs p (SA : Subgroup A)) : Nonempty (x.1.toFunctor ≅ (repAut x).fn) :=
  haveI := x.2.1
  (exists_autTypI_iso x.1.toFunctor x.2.2).choose_spec.2

variable (SB) in
/-- `Φ(-, Id)` on isotypical self-equivalences, landing in `Out_typ(L(A × B))`. -/
noncomputable def phiBarAux : typEquivs p (SA : Subgroup A) →*
    OutTyp p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) where
  toFun x := phiClass SB (repAut_mem x)
  map_one' := by
    obtain ⟨ω⟩ := repAut_iso (1 : typEquivs p (SA : Subgroup A))
    rw [phiClass_eq_of_iso (repAut_mem 1) (one_mem _) (ω.symm ≪≫ Iso.refl _), phiClass_one]
  map_mul' x y := by
    obtain ⟨ωx⟩ := repAut_iso x
    obtain ⟨ωy⟩ := repAut_iso y
    obtain ⟨ωxy⟩ := repAut_iso (x * y)
    have ω : (repAut (x * y)).fn ≅ (repAut x * repAut y).fn :=
      ωxy.symm ≪≫ Functor.isoWhiskerLeft y.1.toFunctor ωx ≪≫
        Functor.isoWhiskerRight ωy (repAut x).fn
    rw [phiClass_eq_of_iso (repAut_mem (x * y)) (mul_mem (repAut_mem x) (repAut_mem y)) ω,
      phiClass_mul]

variable (SB) in
/-- `Φ̄ : Out_typ(L(A)) → Out_typ(L(A × B))`, `[α] ↦ [Φ(α, Id)]`. -/
noncomputable def phiBar : OutTyp p (SA : Subgroup A) →*
    OutTyp p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  (natIsoCon p (SA : Subgroup A)).lift (phiBarAux SB) (by
    rintro x y ⟨e⟩
    obtain ⟨ωx⟩ := repAut_iso x
    obtain ⟨ωy⟩ := repAut_iso y
    exact phiClass_eq_of_iso (repAut_mem x) (repAut_mem y) (ωx.symm ≪≫ e ≪≫ ωy))

lemma phiBar_mk {α : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))
    (x : typEquivs p (SA : Subgroup A)) (ω : x.1.toFunctor ≅ α.fn) :
    phiBar SB ((natIsoCon p (SA : Subgroup A)).mk' x) = phiClass SB hα := by
  change phiClass SB (repAut_mem x) = _
  obtain ⟨ωx⟩ := repAut_iso x
  exact phiClass_eq_of_iso _ hα (ωx.symm ≪≫ ω)

end AndersenOliverVentura.Tame
