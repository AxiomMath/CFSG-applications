import CFSGOutside.GiuliettiKorchmaros.Thm61Defs

/-!
# Giulietti–Korchmáros (2019), Theorem 6.1, odd core-free case (unconditional)

M. Giulietti, G. Korchmáros, Adv. Math. 349 (2019) 162–211, Theorem 6.1 for `O(G) = 1`, group-theoretic form: the
curve hypothesis is replaced by the conclusion of Lemma 6.2 (`CyclicIndexTwo G`). The conclusion lists the paper's
cases (i)–(xi) and, as case (xii), `SL(2,3)`, which the printed list omits. `CyclicIndexTwo`, `OddCoreFree` and
`Theorem61Conclusion` are defined in `CFSGOutside.GiuliettiKorchmaros.Defs` and `.Thm61Defs`.
-/

namespace CFSGOutsideClean.GiuliettiKorchmaros

open CFSGOutside.GiuliettiKorchmaros

theorem theorem_6_1 {G : Type} [Group G] [Finite G] (hP : CyclicIndexTwo G) (hO : OddCoreFree G) :
    Theorem61Conclusion G := sorry

end CFSGOutsideClean.GiuliettiKorchmaros
