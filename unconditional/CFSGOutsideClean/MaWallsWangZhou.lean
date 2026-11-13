import CFSGOutside.MaWallsWangZhou.Paper
import CFSGOutsideClean.Corpus.Defs.J1Models
import CFSGOutsideClean.Corpus.Defs.ReeModel
import CFSGOutsideClean.Corpus.WalterSplit
import CFSGOutsideClean.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutsideClean.Corpus.ElementaryOfClauses

/-! Ma-Walls-Wang-Zhou, Theorem 1.1 and Corollary 1.4, with Walter's theorem, the order of the Ree groups and
the Sylow 2-subgroups of the groups in Walter's list supplied by the corpus. `ordRee`, `walterJ1` and
`ReeTitsModel` are the copies in `CFSGOutside.Corpus`, equal to the corpus definitions by
`CFSGOutsideClean.Corpus.ordRee_eq`, `walterJ1_eq` and `reeTitsModel_twistedG2_iff`. -/

open CFSGOutside.MaWallsWangZhou
open CFSGOutside.Corpus.Open CFSGOutside.Corpus.Blueprint
open scoped MatrixGroups

/-- **Perfect codes in Cayley graphs.** Call a finite group G code-perfect if every subgroup H is a perfect code in some
Cayley graph Cay(G, S) with S inverse-closed and 1 ∉ S, that is, H is independent and every vertex outside H is
adjacent to exactly one vertex of H. A finite group is code-perfect if and only if it has no element of order 4. A
finite simple group is code-perfect if and only if it is cyclic of prime order, PSL(2, 2^e) with e ≥ 2, PSL(2, q)
with q ≡ ±3 (mod 8) and q ≥ 5, the Ree group ²G₂(3^f) with f odd and f ≥ 3, or J₁.

Source: X. Ma, G. L. Walls, K. Wang, S. Zhou, Subgroup perfect codes in Cayley graphs, SIAM J. Discrete Math. 34
(2020), 1909–1921, Theorem 1.1 and Corollary 1.4. https://doi.org/10.1137/19m1258013 -/
theorem CFSGOutsideClean.MaWallsWangZhou.codePerfect_iff (G : Type*) [Group G] [Finite G] :
    CodePerfect G ↔ ∀ g : G, orderOf g ≠ 4 :=
  CFSGOutside.MaWallsWangZhou.codePerfect_iff G

/-- **Corollary 1.4.** *A (finite) simple group is code-perfect if and only if it is isomorphic to
(a) a cyclic group of prime order; (b) `PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`,
`q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group `²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

As in the corpus's statement of Walter's theorem, (d) is expressed by the order
`|G| = |²G₂(3^(2n+1))|`, and `J₁` is the copy of the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem CFSGOutsideClean.MaWallsWangZhou.simple_codePerfect_iff
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nat.card G = ordRee (3 ^ (2 * n + 1))) ∨
      Nonempty (G ≃* walterJ1) :=
  CFSGOutside.MaWallsWangZhou.simple_codePerfect_iff G

/-- **Corollary 1.4**, with clause (d) as an isomorphism. *A (finite) simple group is
code-perfect if and only if it is isomorphic to (a) a cyclic group of prime order; (b)
`PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`, `q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group
`²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

Clause (d) is `ReeTitsModel G .twistedG2 3 f` with `f = 2n+1` odd and `f ≥ 3`, which means `G`
is isomorphic to the copy of the corpus's model of the small Ree group `²G₂(3^f)`. `J₁` is the copy of
the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem CFSGOutsideClean.MaWallsWangZhou.simple_codePerfect_iff_ree
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel G .twistedG2 3 f) ∨
      Nonempty (G ≃* walterJ1) :=
  CFSGOutside.MaWallsWangZhou.simple_codePerfect_iff_ree G

/-- Corollary 1.4 with clause (d) as an isomorphism, stated with the corpus definitions of the small Ree group
model `CFSG.Blueprint.ReeTitsModel` and of the matrix group `CFSG.Open.walterJ1`. -/
theorem CFSGOutsideClean.MaWallsWangZhou.simple_codePerfect_iff_ree_corpus
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel G .twistedG2 3 f) ∨
      Nonempty (G ≃* CFSG.Open.walterJ1) := by
  rw [CFSGOutside.MaWallsWangZhou.simple_codePerfect_iff_ree]
  simp only [CFSGOutsideClean.Corpus.reeTitsModel_twistedG2_iff]
  rfl
