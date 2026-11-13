import CFSGOutside.Gagola.TwoPrimes
import CFSGOutside.Gagola.PSL2

/-!
# Statement: `PSL(2, q)`, `q` odd, with Sylow 2-subgroups of order 8

For `q` odd, `q ≥ 5`, such that the Sylow 2-subgroups of `PSL(2, q)` have order 8, either two distinct
primes have nontrivial cyclic Sylow subgroups, or `q = 9` (and then `|PSL(2,9)| = 360` and the Sylow
5-subgroups are cyclic of order 5).
-/

namespace CFSGOutside.Gagola

open scoped MatrixGroups

/-- The statement proved in `Gagola/PSL2Dihedral.lean` as `psl2OddSylow8`. -/
def Psl2OddSylow8 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], Odd (Fintype.card F) → 5 ≤ Fintype.card F →
    (Nat.card PSL(2, F)).factorization 2 = 3 →
    TwoCyclicPrimes PSL(2, F) ∨
      (Fintype.card F = 9 ∧ Nat.card PSL(2, F) = 360 ∧
        ∀ P : Sylow 5 PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P = 5)

end CFSGOutside.Gagola
