import CFSGOutside.ChillagSonn.Defs

/-!
# Chillag–Sonn (1981), Theorem 1 (unconditional)

D. Chillag and J. Sonn, Israel J. Math. 40 (1981) 307–323, Theorem 1: a finite Sylow-metacyclic group `G` is
`G = N A` with `N ⊴ G` of odd order with a Sylow tower and `N ∩ A = 1`, and either (i) `G` is solvable and `A` is a
Hall `{2, 3}`-subgroup, or (ii) `N = O(G)` and `A` is one of `M₁₁`, `A₇`, `Ã₇`, `PSL(2, pⁱ)`, `SL(2, pⁱ)`,
`PGL(2, pⁱ)`, `PGL(2, pⁱ)^±`, `PGL*(2, p²)` with the paper's additional clauses. `SylowMetacyclic` and
`Theorem1Conclusion` are defined in `CFSGOutside.ChillagSonn.Defs`.
-/

namespace CFSGOutsideClean.ChillagSonn

open CFSGOutside.ChillagSonn

theorem theorem_1 {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) : Theorem1Conclusion G := sorry

end CFSGOutsideClean.ChillagSonn
