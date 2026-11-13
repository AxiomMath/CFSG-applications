import CFSGOutside.Arad.Defs

/-!
# Arad, Theorem B(iii)

Z. Arad, *π-homogeneity and π′-closure of finite groups*, Pacific J. Math. 51 (1974), 1–9, Theorem B(iii),
unconditionally. The notions `IsPiHomogeneous`, `IsPiPrimeClosed` and `SylowTwoDihedralOrAbelian` are in
`CFSGOutside.Arad.Defs`.
-/

namespace CFSGOutsideClean.Arad

open CFSGOutside.Arad

theorem theorem_B_iii {π : Set ℕ} (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G]
    (hG : IsPiHomogeneous π G) (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G := sorry

theorem theorem_B_iii' {π : Set ℕ} (h2 : 2 ∉ π) {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G)
    (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G := sorry

theorem theorem_B_iii_abelian {π : Set ℕ} (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G]
    (hG : IsPiHomogeneous π G) (hS : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) :
    IsPiPrimeClosed π G := sorry

end CFSGOutsideClean.Arad
