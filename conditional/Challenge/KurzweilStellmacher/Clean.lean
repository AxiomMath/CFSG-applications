import Mathlib

/-!
# Kurzweil–Stellmacher, Corollary 11.3.3

H. Kurzweil, B. Stellmacher, *The Theory of Finite Groups: An Introduction*, Universitext, Springer, 2004,
Corollary 11.3.3 (p. 333): if an elementary abelian `p`-group `A` with `r(A) ≥ 3` acts on the `p'`-group `G`
and `C_G(a)` is solvable for all `a ∈ A#`, then `G` is solvable. Here `A` is elementary abelian
(`a ^ p = 1` for all `a`), `r(A) ≥ 3` is `p ^ 3 ≤ |A|`, `G` is a `p'`-group (`p` coprime to `|G|`), and
`C_G(a)` is the fixed-point subgroup of `⟨a⟩` on `G`.
-/

theorem CFSGOutsideClean.KurzweilStellmacher.solvable_of_solvable_centralizers
    {p : ℕ} (hp : p.Prime) {G A : Type} [Group G] [Finite G] [CommGroup A] [Finite A]
    [MulDistribMulAction A G]
    (hexp : ∀ a : A, a ^ p = 1) (hrank : p ^ 3 ≤ Nat.card A)
    (hG : Nat.Coprime p (Nat.card G))
    (hC : ∀ a : A, a ≠ 1 → Group.IsSolvable (FixedPoints.subgroup (Subgroup.zpowers a) G)) :
    Group.IsSolvable G := sorry
