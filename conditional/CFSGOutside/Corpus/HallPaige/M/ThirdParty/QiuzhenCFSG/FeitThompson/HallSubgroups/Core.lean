import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Copied corpus declarations from `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/HallSubgroups/Core.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/HallSubgroups/Core.lean` -/

namespace CFSGOutside.Corpus.M
end CFSGOutside.Corpus.M
open CFSGOutside.Corpus.M

/-- A Hall `π`-subgroup: a subgroup whose order involves only primes in `π` and whose index involves only primes not in `π`. -/
class CFSGOutside.Corpus.M.IsHallSubgroup {G : Type*} [Group G] (π : Set Nat.Primes) (H : Subgroup G) : Prop where
  p_in_pi_of_p_dvd_card (p : Nat.Primes) : p.val ∣ Nat.card H → p ∈ π
  p_in_pi_of_p_dvd_index (p : Nat.Primes) : p.val ∣ H.index → p ∉ π

section HallInfrastructure

variable {G : Type*} [Group G]

/-- A convenient constructor for `IsHallSubgroup`: it suffices to control prime divisors of
`Nat.card H` and to exclude primes in `π` from dividing the index `H.index`. -/
lemma CFSGOutside.Corpus.M.isHallSubgroup_of
    (π : Set Nat.Primes) (H : Subgroup G)
    (hcard : ∀ p : Nat.Primes, p.val ∣ Nat.card H → p ∈ π)
    (hindex : ∀ p : Nat.Primes, p ∈ π → ¬ p.val ∣ H.index) :
    IsHallSubgroup π H := by
  refine ⟨hcard, ?_⟩
  intro p hp_dvd_index
  by_contra hp_in
  exact hindex p hp_in hp_dvd_index

end HallInfrastructure

section PiInfrastructure

variable {G : Type*} [Group G]

section HallCardinality

variable {π : Set Nat.Primes} {H H₁ H₂ K : Subgroup G}

/-- Corpus: `CFSG.IsHallSubgroup.subgroupOf`, CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/HallSubgroups/Core.lean:171. -/
lemma CFSGOutside.Corpus.M.IsHallSubgroup.subgroupOf
    (hH : IsHallSubgroup π H) {K : Subgroup G} (hHK : H ≤ K) :
    IsHallSubgroup π (H.subgroupOf K) := by
  refine isHallSubgroup_of (G := K) (π := π) (H := H.subgroupOf K) (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    have hcard_eq : Nat.card (H.subgroupOf K) = Nat.card H := by
      simpa using Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK).toEquiv
    exact hH.p_in_pi_of_p_dvd_card q (hcard_eq ▸ hq_dvd)
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.subgroupOf K).index ∣ H.index := by
      have hmap : (H.subgroupOf K).map K.subtype = H := by
        ext x
        simp [hHK]
      have hidx_map : ((H.subgroupOf K).map K.subtype).index =
          (H.subgroupOf K).index * K.index :=
        Subgroup.index_map_subtype (K := H.subgroupOf K)
      exact ⟨K.index, by simpa [hmap] using hidx_map⟩
    have hq_dvd_Hidx : q.val ∣ H.index := hq_dvd_idx.trans hidx_dvd
    exact (hH.p_in_pi_of_p_dvd_index q hq_dvd_Hidx) hq_mem

end HallCardinality

end PiInfrastructure
