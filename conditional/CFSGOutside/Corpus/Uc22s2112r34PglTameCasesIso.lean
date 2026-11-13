import Mathlib

/-!
# Corpus input: tame subgroups of `PGL₂(k)`

Statement of `CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s2112r34_pgl_tame_cases_iso`, copied verbatim from
`CFSG/LocalAnalysis/UniquenessCase/UC22S2112aR34F2Even2PGL.lean` (line 78) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962.

A subgroup of `PGL₂(k)`, for `k` a finite field of characteristic `p`, of order prime to `p` is cyclic, dihedral,
or isomorphic to `A₄`, `S₄` or `A₅` (Dickson). The corpus theorem is universe polymorphic, so the class takes the
universe of `k` as a parameter. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/Uc22s2112r34PglTameCasesIso.lean`.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- Dickson's list of the `p'`-subgroups of `PGL₂(k)`, as `uc22s2112r34_pgl_tame_cases_iso` states it. -/
class Uc22s2112r34PglTameCasesIso.{u} : Prop where
  uc22s2112r34_pgl_tame_cases_iso : ∀ {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [Finite k] [CharP k p]
    (J : Subgroup PGL(Fin 2, k)) (_hJ : ¬ p ∣ Nat.card J),
    IsCyclic J ∨ (∃ z : ℕ, Nonempty (J ≃* DihedralGroup z)) ∨
      Nonempty (J ≃* alternatingGroup (Fin 4)) ∨ Nonempty (J ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (J ≃* alternatingGroup (Fin 5))

end CFSGOutside.Corpus
