import CFSGOutside.HallPaige.Lie.TwoTransitive
import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.Corpus.HallPaige.LieSuzuki
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The Suzuki groups

`Sz(q)`, `q = 2^{2a+1}`, acts 2-transitively on its ovoid of `q² + 1` points
(`CFSGOutside.Corpus.Lie.suzuki_ovoid_double_transitivity`). The number of points is odd, so the
point stabilizer is good, and the 2-transitive criterion applies.
-/

namespace CFSGOutside.HallPaige

open MulAction Corpus.Lie
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiLine_injective : Function.Injective fun p : K × K => suzukiLine a K p.1 p.2 := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [suzukiLine, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Units.smul_def] at h0 h1 h2
  simp only [h0, Units.val_one, one_mul] at h1 h2
  rw [← h1, ← h2]

theorem suzukiLine_ne_suzukiInfty (u v : K) : suzukiLine a K u v ≠ suzukiInfty K := by
  simp only [suzukiLine, suzukiInfty, Ne, Projectivization.mk_eq_mk_iff]
  rintro ⟨c, hc⟩
  have := congrFun hc 0
  simp at this

/-- The ovoid has `q² + 1` points. -/
theorem card_suzukiOmega [Finite K] :
    Nat.card (suzukiOmega a K) = Nat.card K ^ 2 + 1 := by
  have hdisj : Disjoint (Set.range fun p : K × K => suzukiLine a K p.1 p.2) {suzukiInfty K} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨p, hp⟩
    exact suzukiLine_ne_suzukiInfty p.1 p.2 hp
  rw [suzukiOmega, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _)
    (Set.toFinite _), Set.ncard_singleton, Set.ncard_range_of_injective suzukiLine_injective,
    Nat.card_prod, sq]

section
variable [h0 : Corpus.Lie.SuzukiOmega] [h1 : Corpus.Lie.SuzukiOvoid]
include h0 h1

/-- **Hall–Paige for the Suzuki groups `Sz(2^{2a+1})`.** -/
theorem hasCompleteMapping_suzukiGroup [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hG : IsGood (suzukiGroup a K)) (hP : ProperSubgroupsAdmissible (suzukiGroup a K)) :
    HasCompleteMapping (suzukiGroup a K) := by
  obtain ⟨-, -, htrans, ⟨x₀⟩, -⟩ := Corpus.Lie.SuzukiOvoid.suzuki_ovoid_double_transitivity hK
  have hcard : Nat.card (suzukiOmegaSub hK) = Nat.card K ^ 2 + 1 := card_suzukiOmega
  have : Finite (suzukiOmegaSub hK) := by
    have : Finite (ℙ K (Fin 4 → K)) := inferInstance
    exact Subtype.finite
  refine hasCompleteMapping_of_two_transitive_of_odd x₀
    (fun x y x' y' hxy hxy' => (is_two_pretransitive_iff.1 htrans) hxy hxy') ?_ ?_ hG hP
  · rw [hcard, hK]
    have : 2 ≤ 2 ^ (2 * a + 1) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  · rw [hcard, hK]
    exact Even.add_one ((Nat.even_pow' two_ne_zero).2 ((Nat.even_pow' (by omega)).2 even_two))

/-- **Hall–Paige for `²B₂(q)`**: the minimal-counterexample step. -/
theorem catalogueCase_suzuki (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    CatalogueCase (.lie ⟨.suzuki m, hv⟩) := by
  intro hG hP
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := Corpus.Lie.SuzukiOvoid.suzukiModel_of_index m hv
  rw [hf] at hK
  exact HasCompleteMapping.of_mulEquiv e.symm (hasCompleteMapping_suzukiGroup hK
    (IsGood.of_mulEquiv e hG) (ProperSubgroupsAdmissible.of_mulEquiv e hP))

end

end CFSGOutside.HallPaige
