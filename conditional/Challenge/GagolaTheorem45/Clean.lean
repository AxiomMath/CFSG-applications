import CFSGOutside.Gagola.FullyRamified

/-!
# Gagola, Theorem 4.5 (clean path, no corpus hypotheses)

S. M. Gagola, *Characters fully ramified over a normal subgroup*, Pacific J. Math. 55 (1974), 107–126,
Theorem 4.5: *Let `G` be a group of type f.r. Assume that `G` has an abelian Sylow `p`-subgroup for every
prime `p` satisfying `p⁶ ∣ |G|`. Then `G` is solvable.* `FullyRamified` and `IsTypeFR` are in
`CFSGOutside.Gagola.FullyRamified`.
-/

namespace CFSGOutsideClean.Gagola

open CFSGOutside.Gagola

theorem theorem_4_5 {G : Type} [Group G] (hG : IsTypeFR G)
    (hS : ∀ p : ℕ, p.Prime → p ^ 6 ∣ Nat.card G → ∃ P : Sylow p G, IsMulCommutative (P : Subgroup G)) :
    Group.IsSolvable G := sorry

end CFSGOutsideClean.Gagola
