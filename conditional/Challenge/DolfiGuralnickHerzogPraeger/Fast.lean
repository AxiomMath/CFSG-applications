import CFSGOutside.Corpus.ClLitBorelTitsLocalParabolicAllModels
import CFSGOutside.DolfiGuralnickHerzogPraeger.Defs

/-!
# Dolfi–Guralnick–Herzog–Praeger, Lemma 4.3 (fast path)

S. Dolfi, R. M. Guralnick, M. Herzog, C. E. Praeger, *A new solvability criterion for finite groups*,
J. London Math. Soc. (2) 85 (2012) 269–281, arXiv:1105.0475, Lemma 4.3 (`lem:parabolic`): for a finite simple
group `X` of Lie type in characteristic `p` (a model `Blueprint.LieModel X t n p f`, other than the Tits group), a
prime `r` with cyclic Sylow `r`-subgroups, `r` dividing the order of no proper parabolic subgroup (a proper
subgroup containing the normalizer of a Sylow `p`-subgroup), and `p` not dividing the order of the automizer of
some subgroup of order `r`, the subgroup `⟨x, y⟩` is nonsolvable whenever `|x| = p` and `|y| = r`.
Conditional on the Borel–Tits theorem, stated as a class in `CFSGOutside.Corpus`.
-/

open CFSGOutside.Corpus CFSGOutside.DolfiGuralnickHerzogPraeger

theorem CFSGOutside.DolfiGuralnickHerzogPraeger.lemma_4_3 [ClLitBorelTitsLocalParabolicAllModels]
    (X : Type) [Group X] [Finite X] (t : Open.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f) (ht : t ≠ .Tits) (r : ℕ) [Fact r.Prime]
    (hcyc : ∃ R : Sylow r X, IsCyclic R)
    (hpar : ∀ P : Subgroup X, P ≠ ⊤ →
      (∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) →
      ¬ r ∣ Nat.card P)
    (haut : ∃ R : Subgroup X, Nat.card R = r ∧ ¬ p ∣ automizerOrder R)
    (x y : X) (hx : orderOf x = p) (hy : orderOf y = r) :
    ¬ Group.IsSolvable (Subgroup.closure {x, y}) := sorry
