import CFSGOutside.MaWallsWangZhou.Defs
import CFSGOutside.Corpus.Defs.J1Models
import CFSGOutside.Corpus.Defs.ReeModel

/-!
# Ma-Walls-Wang-Zhou, Theorem 1.1 and Corollary 1.4 (clean path, no corpus hypotheses)

X. Ma, G. L. Walls, K. Wang, S. Zhou, *Subgroup perfect codes in Cayley graphs*, SIAM J. Discrete Math. 34
(2020) 1909-1921, DOI 10.1137/19m1258013. A finite group is code-perfect iff it has no element of order `4`; a
finite simple group is code-perfect iff it is cyclic of prime order, `PSL(2, 2^e)` (`e ≥ 2`), `PSL(2, q)`
(`q ≡ ±3 mod 8`, `q ≥ 5`), a Ree group `²G₂(3^f)` or `J₁`. The Ree group and `J₁` are the copies of the corpus
models in `CFSGOutside.Corpus`.
-/

namespace CFSGOutsideClean.MaWallsWangZhou

open CFSGOutside.MaWallsWangZhou
open CFSGOutside.Corpus.Open CFSGOutside.Corpus.Blueprint
open scoped MatrixGroups

/-- **Theorem 1.1.** *A group is code-perfect if and only if it has no elements of order 4.* -/
theorem codePerfect_iff (G : Type*) [Group G] [Finite G] :
    CodePerfect G ↔ ∀ g : G, orderOf g ≠ 4 := sorry

/-- **Corollary 1.4.** *A (finite) simple group is code-perfect if and only if it is isomorphic to
(a) a cyclic group of prime order; (b) `PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`,
`q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group `²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

As in the corpus's statement of Walter's theorem, (d) is expressed by the order
`|G| = |²G₂(3^(2n+1))|`, and `J₁` is the copy of the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem simple_codePerfect_iff (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nat.card G = ordRee (3 ^ (2 * n + 1))) ∨
      Nonempty (G ≃* walterJ1) := sorry

/-- **Corollary 1.4**, with clause (d) as an isomorphism. *A (finite) simple group is
code-perfect if and only if it is isomorphic to (a) a cyclic group of prime order; (b)
`PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`, `q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group
`²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

Clause (d) is `ReeTitsModel G .twistedG2 3 f` with `f = 2n+1` odd and `f ≥ 3`, which means `G`
is isomorphic to the copy of the corpus's model of the small Ree group `²G₂(3^f)`. `J₁` is the copy of
the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem simple_codePerfect_iff_ree (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel G .twistedG2 3 f) ∨
      Nonempty (G ≃* walterJ1) := sorry

end CFSGOutsideClean.MaWallsWangZhou
