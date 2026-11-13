import CFSGOutside.Baddeley.Definitions

/-!
# Baddeley, Lemmas 6.1 and 6.2

R. W. Baddeley, *Two-arc transitive graphs and twisted wreath products*, J. Algebraic Combin. 2 (1993), 215–237,
DOI 10.1023/A:1022447514654. Lemmas 6.2 (p. 232) and 6.1 (p. 229) on special pairs, unconditionally. The
definitions are in `CFSGOutside.Baddeley`.
-/

namespace CFSGOutsideClean.Baddeley

open CFSGOutside.Baddeley

variable {V : Type} [Finite V] {Γ : SimpleGraph V}

theorem lemma_6_2 {G H M : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G)
    (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M) (hMreg : IsRegular V M) (hHG : H ≤ G)
    (hH : IsSpecialPair Γ H) : M ≤ H ∧ IsMinimalNormalIn M H := sorry

theorem eq_of_isSpecialPair {G H M M' : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G)
    (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M) (hMreg : IsRegular V M) (hHG : H ≤ G)
    (hM' : IsMinimalNormalIn M' H) (hM'na : IsNonabelian M') (hM'reg : IsRegular V M') : M' = M := sorry

theorem lemma_6_1 {G : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G) :
    ∃! M : Subgroup (Equiv.Perm V), IsMinimalNormalIn M G ∧ IsNonabelian M ∧ IsRegular V M := sorry

end CFSGOutsideClean.Baddeley
