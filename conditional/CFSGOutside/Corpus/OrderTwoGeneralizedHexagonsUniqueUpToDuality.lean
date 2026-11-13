import Mathlib

/-!
# Corpus input: uniqueness of the generalized hexagon of order two

Statement of `CFSG.Combinatorics.HexagonUniqueDuality.order_two_generalized_hexagons_unique_up_to_duality`,
copied verbatim from `CFSG/Combinatorics/HexagonUniqueDuality.lean` (line 62, with `universe u u'` of line 17) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.

Cohen-Tits: the generalized hexagons of order `(2,2)` are unique up to duality. Phrased through their
incidence graphs: two connected cubic bipartite graphs on `126` vertices with all cycles of length at least `12`
are isomorphic by an isomorphism matching the colour classes. The corpus theorem is universe polymorphic, so
the class takes the universes of the two vertex types as parameters. The clean build provides every instance,
in `clean/CFSGOutsideClean/Corpus/OrderTwoGeneralizedHexagonsUniqueUpToDuality.lean`.
-/

namespace CFSGOutside.Corpus

/-- The generalized hexagon of order two is unique up to duality, as
`CFSG.Combinatorics.HexagonUniqueDuality.order_two_generalized_hexagons_unique_up_to_duality` states it. -/
class OrderTwoGeneralizedHexagonsUniqueUpToDuality.{u, u'} : Prop where
  order_two_generalized_hexagons_unique_up_to_duality : ∀ {V : Type u} {V' : Type u'}
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hcard : Fintype.card V = 126)
    (_hconn : G.Connected) (_hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (_hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    [Fintype V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (_hcard' : Fintype.card V' = 126)
    (_hconn' : G'.Connected) (_hdeg' : ∀ v, G'.degree v = 3) (col' : G'.Coloring Bool)
    (_hcyc' : ∀ (v : V') (c : G'.Walk v v), c.IsCycle → 12 ≤ c.length),
    ∃ (ε₁ ε₂ : Bool) (f : G ≃g G'), f '' {v | col v = ε₁} = {v | col' v = ε₂} ∧
      f '' {v | col v = !ε₁} = {v | col' v = !ε₂}

end CFSGOutside.Corpus
