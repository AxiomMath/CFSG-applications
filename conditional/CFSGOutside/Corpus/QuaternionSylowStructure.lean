import CFSGOutside.Corpus.Defs.OddCore

/-!
# Corpus input: groups with generalized quaternion Sylow 2-subgroups

Statement of `CFSG.ClassicalInvolution.quaternion_sylow_structure`, copied verbatim from
`CFSG/ClassicalInvolution/QuaternionStructure.lean` (line 34) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `oddCore` and
`Open.IsQuasisimple` are the copies in `CFSGOutside.Corpus.Defs.OddCore`. The corpus proof combines Brauer–Suzuki
(`CFSG.BrauerSuzuki.brauer_suzuki`) with the vendored Gorenstein–Walter theorem. The class takes the universe as a
parameter.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- Structure of a finite group with generalized quaternion Sylow 2-subgroups, modulo its odd core, as
`CFSG.ClassicalInvolution.quaternion_sylow_structure` states it. -/
class QuaternionSylowStructure.{u} : Prop where
  quaternion_sylow_structure : ∀ {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    (_hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))),
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      (∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z) ∧
      (IsPGroup 2 (X ⧸ oddCore X) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* SL(2, F))) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧
            (∃ φ : L →* Matrix.ProjGenLinGroup (Fin 2) F, Function.Surjective φ ∧
              φ.ker.map L.subtype = Subgroup.zpowers z) ∧
            (∀ P : Sylow 2 L, ∃ k : ℕ, 1 ≤ k ∧
              Nonempty ((P : Subgroup L) ≃* QuaternionGroup (2 ^ k))) ∧
            ∃ M : Subgroup (X ⧸ oddCore X), M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* SL(2, F))) ∨
        (Open.IsQuasisimple (X ⧸ oddCore X) ∧
          Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
          Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
            alternatingGroup (Fin 7))))

end CFSGOutside.Corpus
