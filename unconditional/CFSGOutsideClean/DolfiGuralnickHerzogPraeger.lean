import CFSGOutside.DolfiGuralnickHerzogPraeger.Paper
import CFSGOutsideClean.Corpus.ClLitBorelTitsLocalParabolicAllModels

/-!
# Dolfi–Guralnick–Herzog–Praeger, Lemma 4.3, with Borel–Tits supplied by the corpus

S. Dolfi, R. M. Guralnick, M. Herzog, C. E. Praeger, *A new solvability criterion for finite groups*,
J. London Math. Soc. (2) 85 (2012) 269–281, arXiv:1105.0475, Lemma 4.3 (`lem:parabolic`).

`lemma_4_3` is stated for the copied models `CFSGOutside.Corpus.Blueprint.LieModel`;
`lemma_4_3_corpus` is the same statement for the corpus model `CFSG.Blueprint.LieModel`.
-/

open CFSGOutside.Corpus CFSGOutside.DolfiGuralnickHerzogPraeger

/-- **A solvability criterion.** Let X be a finite simple group of Lie type in characteristic p, other than the Tits
group, and r a prime such that the Sylow r-subgroups of X are cyclic, r divides the order of no proper parabolic
subgroup of X, and some subgroup R of order r has N_X(R)/C_X(R) of order prime to p. Then for any x of order p and y
of order r in X, the subgroup ⟨x, y⟩ is not soluble.

Source: S. Dolfi, R. M. Guralnick, M. Herzog, C. E. Praeger, A new solvability criterion for finite groups, J.
London Math. Soc. (2) 85 (2012), 269–281, Lemma 4.3. https://arxiv.org/abs/1105.0475 -/
theorem CFSGOutsideClean.DolfiGuralnickHerzogPraeger.lemma_4_3
    (X : Type) [Group X] [Finite X] (t : Open.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f) (ht : t ≠ .Tits) (r : ℕ) [Fact r.Prime]
    (hcyc : ∃ R : Sylow r X, IsCyclic R)
    (hpar : ∀ P : Subgroup X, P ≠ ⊤ →
      (∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) →
      ¬ r ∣ Nat.card P)
    (haut : ∃ R : Subgroup X, Nat.card R = r ∧ ¬ p ∣ automizerOrder R)
    (x y : X) (hx : orderOf x = p) (hy : orderOf y = r) :
    ¬ Group.IsSolvable (Subgroup.closure {x, y}) :=
  CFSGOutside.DolfiGuralnickHerzogPraeger.lemma_4_3 X t n p f hmodel ht r hcyc hpar haut x y hx hy

/-- **Lemma 4.3** for the corpus model `CFSG.Blueprint.LieModel` of the finite simple groups of Lie type. -/
theorem CFSGOutsideClean.DolfiGuralnickHerzogPraeger.lemma_4_3_corpus
    (X : Type) [Group X] [Finite X] (t : CFSG.Open.StatedLieTag) (n p f : ℕ)
    (hmodel : CFSG.Blueprint.LieModel X t n p f) (ht : t ≠ .Tits) (r : ℕ) [Fact r.Prime]
    (hcyc : ∃ R : Sylow r X, IsCyclic R)
    (hpar : ∀ P : Subgroup X, P ≠ ⊤ →
      (∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) →
      ¬ r ∣ Nat.card P)
    (haut : ∃ R : Subgroup X, Nat.card R = r ∧ ¬ p ∣ automizerOrder R)
    (x y : X) (hx : orderOf x = p) (hy : orderOf y = r) :
    ¬ Group.IsSolvable (Subgroup.closure {x, y}) :=
  CFSGOutside.DolfiGuralnickHerzogPraeger.lemma_4_3 X
    (CFSGOutsideClean.Corpus.Open.statedLieTagOfCorpus t) n p f
    ((CFSGOutsideClean.Corpus.lieModel_iff X _ n p f).2
      (by rwa [CFSGOutsideClean.Corpus.Open.statedLieTagToCorpus_ofCorpus]))
    (fun h => ht (by
      simpa [CFSGOutsideClean.Corpus.Open.statedLieTagToCorpus_ofCorpus] using
        (CFSGOutsideClean.Corpus.Open.statedLieTagToCorpus_eq_tits_iff _).2 h))
    r hcyc hpar haut x y hx hy
