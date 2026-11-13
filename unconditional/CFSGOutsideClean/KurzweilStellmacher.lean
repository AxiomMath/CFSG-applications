import CFSGOutside.KurzweilStellmacher.Paper
import CFSGOutsideClean.Corpus.CoprimeHyperplaneGeneration
import CFSGOutsideClean.Corpus.SolvableSignalizerDatumComplete

/-! Kurzweil–Stellmacher, Corollary 11.3.3, with Glauberman's signalizer functor theorem and generation by
hyperplane centralizers supplied by the corpus. -/

/-- **Solubility from fixed points.** Let A be an elementary abelian p-group of order at least p³ acting on a finite
group G of order prime to p. If the fixed points of every non-identity element of A form a soluble subgroup, then G
is soluble.

Source: H. Kurzweil and B. Stellmacher, The Theory of Finite Groups, Universitext (2004), Corollary 11.3.3.
https://doi.org/10.1007/b97433 -/
theorem CFSGOutsideClean.KurzweilStellmacher.solvable_of_solvable_centralizers
    {p : ℕ} (hp : p.Prime) {G A : Type} [Group G] [Finite G] [CommGroup A] [Finite A]
    [MulDistribMulAction A G]
    (hexp : ∀ a : A, a ^ p = 1) (hrank : p ^ 3 ≤ Nat.card A)
    (hG : Nat.Coprime p (Nat.card G))
    (hC : ∀ a : A, a ≠ 1 → Group.IsSolvable (FixedPoints.subgroup (Subgroup.zpowers a) G)) :
    Group.IsSolvable G :=
  CFSGOutside.KurzweilStellmacher.solvable_of_solvable_centralizers hp hexp hrank hG hC
