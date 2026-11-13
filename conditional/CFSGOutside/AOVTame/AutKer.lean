import CFSGOutside.AOVTame.AutI
import CFSGOutside.AOVTame.Kappa
import CFSGOutside.AOVTame.SatGroup

/-!
# AOV tameness: naturally isomorphic elements of `Aut_typ^I` (AOV Lemma 1.14(a), kernel)

If `α, α' ∈ Aut_typ^I(L^c_S(G))` are naturally isomorphic, then `α' = c_n ∘ α` for some
`n ∈ N_G(S)`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}

lemma conj_mem_opCent_conjSub {R : Subgroup G} {x : G} (hx : x ∈ opCent p R) (n : G) :
    n * x * n⁻¹ ∈ opCent p (conjSub n R) := by
  have := map_opCent_le p (MulAut.conj n) R ⟨x, hx, rfl⟩
  simpa [conjSub] using this

lemma transporter_self_conj {n : G} (hn : n ∈ transporter (T : Subgroup G) (T : Subgroup G)) :
    conjSub n (T : Subgroup G) = T :=
  Subgroup.eq_of_le_of_card_ge (fun _ ⟨x, hx, e⟩ => e ▸ hn x hx)
    (Nat.card_congr (equivMapOfInjective _ _ (MulAut.conj n).injective).toEquiv.symm).ge

/-- AOV Lemma 1.14(a), kernel: naturally isomorphic elements of `Aut_typ^I` differ by `c_n`,
`n ∈ N_G(S)`. -/
theorem eq_conj_of_iso {α α' : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (hα' : α' ∈ autTypI p (T : Subgroup G)) (ω : α.fn ≅ α'.fn) :
    ∃ (n : G) (hn : (T : Subgroup G).map (MulAut.conj n).toMonoidHom = T),
      α'.fn = α.fn ⋙ mapFunctor p (MulAut.conj n) hn := by
  obtain ⟨⟨n, hn₀⟩, en⟩ := Quotient.exists_rep (ω.hom.app (topObj T))
  have hnT : n ∈ transporter (T : Subgroup G) (T : Subgroup G) := by
    have := hn₀; rwa [val_obj_top hα, val_obj_top hα'] at this
  have hn : (T : Subgroup G).map (MulAut.conj n).toMonoidHom = T := transporter_self_conj hnT
  -- the components of `ω`
  have comp : ∀ P : Obj p (T : Subgroup G), ∃ (m : G) (hm : m ∈ transporter (α.fn.obj P).val
      (α'.fn.obj P).val), ω.hom.app P = mk p m hm ∧ n⁻¹ * m ∈ opCent p (α.fn.obj P).val := by
    intro P
    obtain ⟨⟨m, hm⟩, em⟩ := Quotient.exists_rep (ω.hom.app P)
    refine ⟨m, hm, em.symm, ?_⟩
    obtain ⟨hle, hι⟩ := hα.2 P (topObj T) P.2.1
    obtain ⟨hle', hι'⟩ := hα'.2 P (topObj T) P.2.1
    have nat := ω.hom.naturality (incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1)
    rw [hι, hι', ← en, ← em] at nat
    have h1 := (mk_eq_mk p).1 nat
    simpa using h1
  have hobj : ∀ P : Obj p (T : Subgroup G),
      (α'.fn.obj P).val = (α.fn.obj P).val.map (MulAut.conj n).toMonoidHom := by
    intro P
    obtain ⟨m, hm, -, hc⟩ := comp P
    have hcC := opCent_le_centralizer p _ hc
    have hle : conjSub n (α.fn.obj P).val ≤ (α'.fn.obj P).val := by
      rintro _ ⟨y, hy, rfl⟩
      have := hm y hy
      have e : m * y * m⁻¹ = n * y * n⁻¹ := by
        have hcy := mem_centralizer_iff.1 hcC y hy
        calc m * y * m⁻¹ = n * ((n⁻¹ * m) * y) * (n⁻¹ * m)⁻¹ * n⁻¹ := by group
          _ = n * (y * (n⁻¹ * m)) * (n⁻¹ * m)⁻¹ * n⁻¹ := by rw [hcy]
          _ = n * y * n⁻¹ := by group
      rw [e] at this; simpa using this
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [obj_val_eq hα' P, obj_val_eq hα P, card_bmap _ P.2.1]
    change _ ≤ Nat.card (conjSub n _)
    rw [card_conjSub, card_bmap _ P.2.1]
  refine ⟨n, hn, Functor.hext (fun P => Obj.ext (hobj P)) ?_⟩
  rintro P Q ⟨⟨g, hg⟩⟩
  obtain ⟨mP, hmP, eP, hcP⟩ := comp P
  obtain ⟨mQ, hmQ, eQ, hcQ⟩ := comp Q
  obtain ⟨⟨h, hh⟩, eh⟩ := Quotient.exists_rep (α.fn.map (show P ⟶ Q from mk p g hg))
  obtain ⟨⟨h', hh'⟩, eh'⟩ := Quotient.exists_rep (α'.fn.map (show P ⟶ Q from mk p g hg))
  have nat := ω.hom.naturality (show P ⟶ Q from mk p g hg)
  rw [eP, eQ, ← eh, ← eh'] at nat
  have hD := (mk_eq_mk p).1 nat
  change HEq (α'.fn.map (show P ⟶ Q from mk p g hg))
    (Mor.map p (MulAut.conj n) (α.fn.map (show P ⟶ Q from mk p g hg)))
  rw [← eh, ← eh']
  change HEq (mk p h' hh') (Mor.map p (MulAut.conj n) (mk p h hh))
  rw [Mor.map_mk]
  apply mk_heq_of_mem p (hobj P) (hobj Q)
  have hD' : (mQ * h)⁻¹ * (h' * mP) ∈ opCent p (α.fn.obj P).val := hD
  have hX : (n⁻¹ * mP) * ((mQ * h)⁻¹ * (h' * mP))⁻¹ * (h⁻¹ * (n⁻¹ * mQ)⁻¹ * h) ∈
      opCent p (α.fn.obj P).val :=
    mul_mem (mul_mem hcP (inv_mem hD')) (conj_mem_opCent p hh (inv_mem hcQ))
  have := conj_mem_opCent_conjSub hX n
  rw [hobj P]
  convert this using 1
  · rfl
  · simp only [MulAut.conj_apply]
    group

end AndersenOliverVentura.Tame
