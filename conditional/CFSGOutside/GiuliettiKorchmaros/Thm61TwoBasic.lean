import CFSGOutside.Corpus.ThompsonTransferLemma
import CFSGOutside.GiuliettiKorchmaros.Thm61Four
import CFSGOutside.GiuliettiKorchmaros.LinearTwo

/-!
# Theorem 6.1, central involution case: tools

Index-2 subgroups from Thompson transfer, and the center of `A₇`.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

/-- An element outside the 2-residual gives a (normal) subgroup of index 2. -/
theorem exists_index_two_of_not_mem_pResidual {b : G} (hb : b ∉ Quasithin.pResidual 2 G) :
    ∃ M : Subgroup G, M.index = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [Quasithin.pResidual, Subgroup.mem_iInf, not_forall] at hb
  obtain ⟨N, hN, hcond, hbN⟩ := hb
  -- `G ⧸ N` is a nontrivial 2-group
  have h2 : IsPGroup 2 (G ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hcond g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hsub : Subsingleton (G ⧸ N) := by
      rw [pow_zero] at hn
      exact (Nat.card_eq_one_iff_unique.mp hn).1
    apply hbN
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 (show 2 ^ (n - 1) ∣ Nat.card (G ⧸ N) from by
    rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
  refine ⟨H.comap (QuotientGroup.mk' N), ?_⟩
  rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective N)]
  have := Subgroup.card_mul_index H
  rw [hH, hn] at this
  have h' : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h'] at this
  exact Nat.eq_of_mul_eq_mul_left (by positivity) this

end CFSGOutside.GiuliettiKorchmaros
