import CFSGOutside.HallPaige.Sporadic.M.Triangles
import CFSGOutside.HallPaige.Sporadic.M.Count
import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Transport

/-!
# The Monster `M`

`M` acts on its `2A` involutions with point stabiliser `C(a) ≅ 2.B` and nine orbitals, given by the
class `c i` of `a β` (corpus milestone `cl_lit_monster_existence_griess_conway`, the `IsTwoAGraphData`
clauses; `c i` of orders `1, 2, 2, 3, 3, 4, 4, 5, 6`, i.e. `1A, 2A, 2B, 3A, 3C, 4A/4B, 5A, 6A`). The
Wilcox criterion for `H = C(a)` needs a triangle of `2A` involutions in each orbital
(`Sporadic/M/Glue.lean`, `Sporadic/M/Assembly.lean`):

* `1A, 2A, 3A, 3C, 5A`: dihedral triangles;
* `6A`: counting, `|M| · |2.Fi22| < 2 · |2.B|²` (`Sporadic/M/Count.lean`);
* `2B, 4A, 4B`: explicit triangles in the Griess–Conway model (`Sporadic/M/Triangles.lean`).

The milestone's `a` and `z` are conjugate to `tGriess` and `xGriess` (centralizer orders and
`not_isConj_xGriess_tGriess`). The Griess–Conway model is `TauCeti.M` by the corpus isomorphisms.
-/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M CFSGOutside.Corpus.M.Monster.Existence CFSGOutside.Corpus.M.Open
  CFSGOutside.Corpus.M.GriessModel CFSGOutside.Corpus.M.Monster.B

section

variable {G : Type} [Group G]

theorem card_cent_of_twoA {d : GriessModel} [d.Facts] {x : G} (hx : orderOf x = 2) (h : IsTwoACentralizer x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * monsterBabyOrder := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have hc : Nat.card ↥((Subgroup.center ↥(cent x)).map (cent x).subtype) =
      Nat.card ↥(Subgroup.center ↥(cent x)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [hZ, Nat.card_zpowers, hx] at hc
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(cent x))
  rw [Nat.card_congr e.toEquiv, Facts.card_nativeB (d := d), ← hc] at this
  rw [show Subgroup.centralizer ({x} : Set G) = cent x from rfl, this, mul_comm]

end

variable {d : GriessModel} [d.Facts]

theorem orderOf_R0 : orderOf (R d (false, 0, 191)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (R_ne_one (isShortCoord_of_key (p := 0) (by norm_num) keyAt_0))
  rw [sq, R_mul, show Model.Pauli.mul (false, 0, 191) (false, 0, 191) = (false, 0, 0) by decide, R_zero]

theorem orderOf_tGriess : orderOf d.tGriess = 2 :=
  (orderOf_eq_of_isConj tA_0).trans orderOf_R0

/-- The Wilcox criterion for the Griess–Conway model. -/
theorem wilcoxCriterion_MGriess : Finite d.MGriess ∧ WilcoxCriterion d.MGriess := by
  obtain ⟨⟨hfin, hsimple, hnc, hcard⟩, a, z, ha, hz, haz, hinv, hA, hB, hgraph⟩ :=
    Facts.cl_lit_monster_existence_griess_conway (d := d)
  obtain ⟨-, -, htA⟩ := Facts.monster_clauses_MGriess (d := d)
  refine ⟨hfin, ?_⟩
  -- identify `a` and `z`
  have hat : IsConj a d.tGriess := by
    rcases hinv d.tGriess orderOf_tGriess with h | h
    · exact h
    · exfalso
      have h1 := card_cent_of_twoA (d := d) orderOf_tGriess htA
      have h2 := (hB d.tGriess h).2.2.2.2.1
      rw [h1] at h2
      revert h2; norm_num [monsterBabyOrder, twoBCentralizerOrder]
  have hzx : IsConj z d.xGriess := by
    rcases hinv d.xGriess (Facts.orderOf_xGriess (d := d)) with h | h
    · exact absurd (h.symm.trans hat) Facts.not_isConj_xGriess_tGriess
    · exact h
  obtain ⟨h31, c, hcinj, hc0, hc1, hc2, hcord, hcover, hocc, hshape, -⟩ := hgraph
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have horb : OrbitClause a := fun β β' hβ hβ' h => h31 a β β' (IsConj.refl a) hβ hβ' h
  -- the transferred triangles
  have tr : ∀ {P Q : d.MGriess → Prop}, (∀ p, P p → Q p) → TriP d.tGriess P → TriP a Q :=
    fun hPQ ⟨α, β, γ, h1, h2, h3, p1, p2, p3⟩ =>
      ⟨α, β, γ, hat.trans h1, hat.trans h2, hat.trans h3, hPQ _ p1, hPQ _ p2, hPQ _ p3⟩
  have h2B : TriP a (IsConj z) := tr (fun p hp => hzx.trans hp) tri2B
  have h4A : TriP a (SqClass z) := tr (fun p ⟨h1, h2⟩ => ⟨h1, hzx.trans h2⟩) tri4A
  have h4B : TriP a (SqClass a) := tr (fun p ⟨h1, h2⟩ => ⟨h1, hat.trans h2⟩) tri4B
  -- the 6A orbital by counting
  have h8 : Tri a (c 8) := by
    obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc 8
    obtain ⟨k, rfl⟩ := isConj_iff.1 hα
    set β₀ := k⁻¹ * β * k
    have hβ₀ : IsConj a β₀ := hβ.trans (isConj_conj_inv k β)
    have hc8 : IsConj (a * β₀) (c 8) := by
      have : a * β₀ = k⁻¹ * (k * a * k⁻¹ * β) * k := by simp only [β₀]; group
      rw [this]; exact (isConj_conj_inv k _).symm.trans hαβ
    obtain ⟨N, hNn, hN, he⟩ := hshape a β₀ 8 (IsConj.refl a) hβ₀ hc8
    haveI := hNn
    have he' : Nonempty (↥(cent2 a β₀) ⧸ N ≃* CFSGOutside.Corpus.M.Blueprint.NativeSporadic.Fi22) := he
    obtain ⟨e⟩ := he'
    have hK : Nat.card ↥(Subgroup.centralizer ({a} : Set d.MGriess) ⊓
        Subgroup.centralizer ({β₀} : Set d.MGriess)) = 2 * 64561751654400 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [Nat.card_congr e.toEquiv, Facts.card_Fi22 (d := d), hN] at this
      rw [show Subgroup.centralizer ({a} : Set d.MGriess) ⊓ Subgroup.centralizer ({β₀} : Set d.MGriess) =
        cent2 a β₀ from rfl, this]; ring
    refine tri_of_orders horb hβ₀ hc8 hcard (card_cent_of_twoA (d := d) ha (hA a (IsConj.refl a))) hK
      (by norm_num) ?_
    norm_num [monsterOrder, monsterBabyOrder]
  exact wilcoxCriterion_of_orbitals hsimple hnc ha haz h31 hcinj hc0 hc1 hc2
    (fun i => (hcord i).trans (by fin_cases i <;> rfl)) hcover hocc h8 h2B h4A h4B

theorem nonempty_mulEquiv_tauCeti : Nonempty (d.MGriess ≃* TauCeti.SporadicName.M.Group) := by
  obtain ⟨e₁⟩ := Facts.iso_griess_y443Derived (d := d)
  obtain ⟨e₂⟩ := Facts.iso_y443Derived_tauCeti (d := d)
  exact ⟨e₁.trans e₂⟩

theorem hasCompleteMapping_MGriess (hP : ProperSubgroupsAdmissible d.MGriess) :
    HasCompleteMapping d.MGriess := by
  obtain ⟨hfin, hW⟩ := wilcoxCriterion_MGriess (d := d)
  exact @hasCompleteMapping_of_wilcoxCriterion d.MGriess _ hfin cosetStatement hW hP

end CFSGOutside.HallPaige.M

namespace CFSGOutside.HallPaige

open CFSGOutside.Corpus.M CFSGOutside.HallPaige.M

/-- **The catalogue case of the Monster.** -/
theorem catalogueCase_M [Theorems] : CatalogueCase (.sporadic .M) := by
  intro _ hP
  obtain ⟨d, hd⟩ := Theorems.exists_griessModel
  obtain ⟨e⟩ := nonempty_mulEquiv_tauCeti (d := d)
  exact HasCompleteMapping.of_mulEquiv e
    (hasCompleteMapping_MGriess (ProperSubgroupsAdmissible.of_mulEquiv e.symm hP))

end CFSGOutside.HallPaige
