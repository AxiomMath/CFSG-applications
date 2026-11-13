import CFSGOutside.Corpus.ClLitBorelTitsLocalParabolicAllModels
import CFSGOutside.DolfiGuralnickHerzogPraeger.Abstract
import CFSGOutside.DolfiGuralnickHerzogPraeger.Bridge

/-!
# Dolfi–Guralnick–Herzog–Praeger, *A new solvability criterion for finite groups*, Lemma 4.3

S. Dolfi, R. M. Guralnick, M. Herzog, C. E. Praeger, *A new solvability criterion for finite groups*,
J. London Math. Soc. (2) 85 (2012) 269–281, arXiv:1105.0475, Lemma 4.3 (`lem:parabolic`).

The finite simple groups of Lie type are the corpus models `Blueprint.LieModel X t n p f` (`p` the
characteristic) other than the Tits group `²F₄(2)'` (tag `.Tits`), which the paper treats together with the
sporadic groups (its Proposition 3.3). Following the paper, a *parabolic subgroup* of `X` is any subgroup
containing the normalizer of a Sylow `p`-subgroup.

Conditional on the Borel–Tits theorem, stated as a class in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.DolfiGuralnickHerzogPraeger

open CFSGOutside.Corpus Corpus.Open Corpus.Blueprint

/-- The characteristic of a model of a simple group of Lie type is prime. -/
theorem LieModel.prime {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : p.Prime := by
  rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact h.1.1
  · exact h.1.1
  · exact h.1.1
  · exact h.1 ▸ Nat.prime_two

/-- Borel–Tits, in the form used by the paper: if `r` divides the order of no proper parabolic subgroup,
then `r` divides the order of the normalizer of no nontrivial `p`-subgroup. -/
theorem not_dvd_card_normalizer [ClLitBorelTitsLocalParabolicAllModels]
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p f : ℕ}
    (hmodel : LieModel X t n p f) (ht : t ≠ .Tits) {r : ℕ}
    (hpar : ∀ P : Subgroup X, P ≠ ⊤ →
      (∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) →
      ¬ r ∣ Nat.card P)
    (U : Subgroup X) (hU : U ≠ ⊥) (hUp : IsPGroup p U) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (U : Set X)) := by
  obtain ⟨S, P, hP, hNU, -, -, hS, -⟩ :=
    ClLitBorelTitsLocalParabolicAllModels.cl_lit_borel_tits_local_parabolic_all_models
      X t n p f hmodel U hU hUp
  exact fun hr => hpar P hP ⟨S, hS ht⟩ (hr.trans (Subgroup.card_dvd_of_le hNU))

/-- **A solvability criterion.** Let X be a finite simple group of Lie type in characteristic p, other than the Tits
group, and r a prime such that the Sylow r-subgroups of X are cyclic, r divides the order of no proper parabolic
subgroup of X, and some subgroup R of order r has N_X(R)/C_X(R) of order prime to p. Then for any x of order p and y
of order r in X, the subgroup ⟨x, y⟩ is not soluble.

Source: S. Dolfi, R. M. Guralnick, M. Herzog, C. E. Praeger, A new solvability criterion for finite groups, J.
London Math. Soc. (2) 85 (2012), 269–281, Lemma 4.3. https://arxiv.org/abs/1105.0475

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem lemma_4_3 [ClLitBorelTitsLocalParabolicAllModels]
    (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ)
    (hmodel : LieModel X t n p f) (ht : t ≠ .Tits) (r : ℕ) [Fact r.Prime]
    (hcyc : ∃ R : Sylow r X, IsCyclic R)
    (hpar : ∀ P : Subgroup X, P ≠ ⊤ →
      (∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) →
      ¬ r ∣ Nat.card P)
    (haut : ∃ R : Subgroup X, Nat.card R = r ∧ ¬ p ∣ automizerOrder R)
    (x y : X) (hx : orderOf x = p) (hy : orderOf y = r) :
    ¬ Group.IsSolvable (Subgroup.closure {x, y}) := by
  haveI : Fact p.Prime := ⟨LieModel.prime hmodel⟩
  exact not_isSolvable_closure
    ⟨not_dvd_card_normalizer hmodel ht hpar, isCyclic_of_isPGroup hcyc,
      mem_centralizer_of_automizer hcyc haut⟩ x y hx hy

end CFSGOutside.DolfiGuralnickHerzogPraeger
