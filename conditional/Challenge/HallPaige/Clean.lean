import CFSGOutside.HallPaige.CatalogueDefs

/-!
# The Hall–Paige theorem

P. Hall and L. J. Paige, *Complete mappings of finite groups*, Pacific J. Math. 5 (1955), 541–549, proved the
necessity (their Theorem 5) and conjectured the converse: a finite group has a complete mapping if and only if its
Sylow `2`-subgroups are trivial or non-cyclic. The conjecture was proved by S. Wilcox (2009), A. B. Evans (2009) and
J. N. Bray et al. (2020).
-/

namespace CFSGOutsideClean.HallPaige

open CFSGOutside.HallPaige

universe u

/-- **Hall–Paige (1955), Theorem 5.** A finite group with a complete mapping satisfies the Hall–Paige condition:
its Sylow `2`-subgroups are trivial or non-cyclic. -/
theorem isGood_of_hasCompleteMapping {G : Type*} [Group G] [Finite G] (h : HasCompleteMapping G) : IsGood G := sorry

/-- **Hall–Paige theorem**: a finite group has a complete mapping iff its Sylow `2`-subgroups are trivial or non-cyclic. -/
theorem hall_paige (G : Type u) [Group G] [Finite G] :
    HasCompleteMapping G ↔ IsGood G := sorry

end CFSGOutsideClean.HallPaige
