import CFSGOutside.Corpus.Defs.HallSubgroups

/-!
# Corpus input: Hall subgroups of solvable groups

* Existence: statement of `CFSG.FeitThompson.exists_isHallSubgroup`, copied verbatim from
  `CFSG/FeitThompson/Foundations/SolvableHallExistence.lean` (line 90), corpus-own.
* Conjugacy: statement of `CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable`, copied verbatim from the vendored
  Qiuzhen-CFSG file `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/HallSubgroups/Conjugacy.lean` (line 502).

Both at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with the Hall subgroup notions copied in
`CFSGOutside.Corpus.Defs.HallSubgroups`. The corpus theorems are universe polymorphic; the classes take the universe
of the group as a parameter.
-/

namespace CFSGOutside.Corpus

/-- A solvable group has Hall `π`-subgroups, as `CFSG.FeitThompson.exists_isHallSubgroup` states it. -/
class SolvableHallExistence.{u} : Prop where
  exists_isHallSubgroup : ∀ {X : Type u} [Group X] [Finite X] [Group.IsSolvable X] (π : Set ℕ),
    ∃ H : Subgroup X, FeitThompson.IsHallSubgroup π H

/-- Hall `π`-subgroups of a solvable group are conjugate, as `CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable`
states it. -/
class SolvableHallConjugacy.{u} : Prop where
  exists_conj_eq_of_isHallSubgroup_of_solvable : ∀ {G : Type u} [Group G] [Finite G]
    (_hsolv : Group.IsSolvable G) {π : Set Nat.Primes} {H₁ H₂ : Subgroup G}
    (_hHall₁ : IsHallSubgroup π H₁) (_hHall₂ : IsHallSubgroup π H₂),
    ∃ g : G, H₂ = H₁.map (MulAut.conj g).toMonoidHom

end CFSGOutside.Corpus
