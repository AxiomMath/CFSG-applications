import CFSGOutside.Corpus.Defs.FrobeniusFrattini
import CFSGOutside.Corpus.Defs.ElementaryAbelian

/-!
# Corpus input: the Frattini quotient of a `p`-group (Burnside)

Statements of `CFSG.GroupTheory.frattini_elementary_quotient` and `CFSG.GroupTheory.frattini_automorphism_kernel`,
copied verbatim from `CFSG/GroupTheory/FrattiniQuotient.lean` (lines 15 and 37) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `IsElementaryAbelian` and `quotientAutomorphism` are the copies in
`CFSGOutside.Corpus.Defs`. The corpus theorems are universe polymorphic; the classes take the universe of `P` as a
parameter.

The Frattini quotient of a finite `p`-group is elementary abelian, and the automorphisms acting trivially on it form a
`p`-group.
-/

namespace CFSGOutside.Corpus

open OrderReductions.FrattiniAutomorphisms

/-- `P/Φ(P)` is elementary abelian, as `CFSG.GroupTheory.frattini_elementary_quotient` states it. -/
class FrattiniElementaryQuotient.{u} : Prop where
  frattini_elementary_quotient : ∀ {p : ℕ} [Fact p.Prime] {P : Type u} [Group P] [Finite P]
    (_hP : IsPGroup p P),
    (frattini P).Characteristic ∧ IsMulCommutative (P ⧸ frattini P) ∧
      (∀ x : P ⧸ frattini P, x ^ p = 1) ∧ IsElementaryAbelian p (P ⧸ frattini P) ∧
      ∃ d : ℕ, Nat.card (P ⧸ frattini P) = p ^ d ∧
        Nonempty (Additive (P ⧸ frattini P) ≃+ (Fin d → ZMod p))

/-- The kernel of `Aut(P) → Aut(P/Φ(P))` is a `p`-group, as `CFSG.GroupTheory.frattini_automorphism_kernel` states
it. -/
class FrattiniAutomorphismKernel.{u} : Prop where
  frattini_automorphism_kernel : ∀ {p : ℕ} [Fact p.Prime] {P : Type u} [Group P] [Finite P]
    (_hP : IsPGroup p P),
    (∀ (σ : MulAut P) (x : P), quotientAutomorphism (frattini P) σ (x : P ⧸ frattini P) =
      (σ x : P ⧸ frattini P)) ∧ IsPGroup p (quotientAutomorphism (frattini P)).ker

end CFSGOutside.Corpus
