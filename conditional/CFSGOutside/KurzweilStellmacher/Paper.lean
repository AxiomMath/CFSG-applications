import CFSGOutside.Corpus.CoprimeHyperplaneGeneration
import CFSGOutside.Corpus.SolvableSignalizerDatumComplete

/-!
# Kurzweil–Stellmacher, Corollary 11.3.3

H. Kurzweil, B. Stellmacher, *The Theory of Finite Groups: An Introduction*, Universitext, Springer, 2004,
Corollary 11.3.3 (p. 333): *Let `A` be an elementary abelian `p`-group with `r(A) ≥ 3` that acts on the
`p'`-group `G`. Suppose that `C_G(a)` is solvable for all `a ∈ A#`. Then `G` is solvable.*

The book applies Glauberman's Completeness Theorem 11.3.2 to the solvable `A`-signalizer functor
`a ↦ C_G(a)` and then uses generation by centralizers (8.3.4). Here the signalizer functor is the datum
`CFSGOutside.Corpus.GroupTheory.SteinbergBS.IsSolvableSignalizerDatum` on `A` acting on `G`, so no
semidirect product is needed, and generation by the centralizers of the nontrivial elements follows from
generation by the centralizers of the hyperplanes of `A`. Conditional on the corpus inputs stated as classes
in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.KurzweilStellmacher

open CFSGOutside.Corpus CFSGOutside.Corpus.GroupTheory.SteinbergBS

section

variable {G A : Type} [Group G] [Group A] [MulDistribMulAction A G]

lemma mem_fixedPoints_zpowers_iff (a : A) (x : G) :
    x ∈ FixedPoints.subgroup (Subgroup.zpowers a) G ↔ a • x = x := by
  constructor
  · intro h
    exact h ⟨a, Subgroup.mem_zpowers a⟩
  · intro h ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    change a ^ k • x = x
    clear hb
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, mul_smul, h, ih]
    | pred n ih =>
      rw [zpow_sub_one, mul_smul]
      have : a⁻¹ • x = x := by rw [inv_smul_eq_iff, h]
      rw [this, ih]

/-- The fixed points of a subgroup `B` of `A` lie in the fixed points of `⟨b⟩` for each `b ∈ B`. -/
lemma fixedPointSubgroup_le (B : Subgroup A) {b : A} (hb : b ∈ B) :
    fixedPointSubgroup B G ≤ FixedPoints.subgroup (Subgroup.zpowers b) G := fun x hx =>
  (mem_fixedPoints_zpowers_iff b x).2 (hx ⟨b, hb⟩)

end

/-- **Solubility from fixed points.** Let A be an elementary abelian p-group of order at least p³ acting on a finite
group G of order prime to p. If the fixed points of every non-identity element of A form a soluble subgroup, then G
is soluble.

Source: H. Kurzweil and B. Stellmacher, The Theory of Finite Groups, Universitext (2004), Corollary 11.3.3.
https://doi.org/10.1007/b97433

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem solvable_of_solvable_centralizers
    [CoprimeHyperplaneGeneration.{0, 0}] [SolvableSignalizerDatumComplete.{0, 0}]
    {p : ℕ} (hp : p.Prime) {G A : Type} [Group G] [Finite G] [CommGroup A] [Finite A]
    [MulDistribMulAction A G]
    (hexp : ∀ a : A, a ^ p = 1) (hrank : p ^ 3 ≤ Nat.card A)
    (hG : Nat.Coprime p (Nat.card G))
    (hC : ∀ a : A, a ≠ 1 → Group.IsSolvable (FixedPoints.subgroup (Subgroup.zpowers a) G)) :
    Group.IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hElem : IsElementaryAbelian p A :=
    { toIsMulCommutative := ⟨⟨mul_comm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  have hp2 : p ^ 2 ≤ Nat.card A := le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hrank
  have hcard : 1 < Nat.card A := lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) hp.one_lt) hp2
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 hcard
  let θ : A → Subgroup G := fun a => FixedPoints.subgroup (Subgroup.zpowers a) G
  have hfix : ∀ a b : A, ∀ x : G, x ∈ θ a → b • x ∈ θ a := fun a b x hx => by
    rw [mem_fixedPoints_zpowers_iff] at hx ⊢
    rw [← mul_smul, mul_comm, mul_smul, hx]
  have hd : IsSolvableSignalizerDatum p A G (MulDistribMulAction.toMulAut A G) θ :=
    { prime := hp
      finite_actor := inferInstance
      elementary := hElem
      card_actor := hp2
      finite := inferInstance
      invariant := fun a _ b => by
        ext x
        simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
        refine ⟨?_, fun hx => ⟨b⁻¹ • x, ?_, ?_⟩⟩
        · rintro ⟨y, hy, rfl⟩
          exact hfix a b y hy
        · simpa using hfix a b⁻¹ x hx
        · simp [MulDistribMulAction.toMulAut_apply]
      solvable := hC
      coprime := fun a _ =>
        Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) hG
      le_fixed := fun a _ g hg => (mem_fixedPoints_zpowers_iff a g).1 hg
      balance := fun a b _ _ g _ hbg => (mem_fixedPoints_zpowers_iff b g).2 hbg }
  obtain ⟨-, hsol, -, -⟩ :=
    SolvableSignalizerDatumComplete.solvable_signalizer_datum_complete hd
      (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hrank)
  have htop : (⨆ (a : A) (_ : a ≠ 1), θ a) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← CoprimeHyperplaneGeneration.coprime_hyperplane_generation (p := p) (A := A) (H := G)
      (fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp hG h)]
    refine iSup_le fun B => iSup_le fun hB => ?_
    have hB1 : B ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.index_bot] at hB
      have : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    exact (fixedPointSubgroup_le B hbB).trans
      (le_iSup_of_le b (le_iSup_of_le (fun h => hb1 (Subtype.ext h)) le_rfl))
  rw [htop] at hsol
  exact solvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
    Subgroup.topEquiv.surjective

end CFSGOutside.KurzweilStellmacher
