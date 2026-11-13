import Mathlib

/-!
# The automizer order

Definition used in the statement of Dolfi–Guralnick–Herzog–Praeger, *A new solvability criterion for finite
groups*, J. London Math. Soc. (2) 85 (2012) 269–281, Lemma 4.3.
-/

namespace CFSGOutside.DolfiGuralnickHerzogPraeger

/-- The order of the automizer `N_G(R)/C_G(R)` of a subgroup `R`, i.e. the index of
`C_G(R)` in `N_G(R)`. Used in Lemma 4.3 of Dolfi–Guralnick–Herzog–Praeger, *A new solvability criterion for
finite groups*, J. London Math. Soc. (2) 85 (2012), arXiv:1105.0475. -/
noncomputable def automizerOrder {G : Type*} [Group G] (R : Subgroup G) : ℕ :=
  (Subgroup.centralizer (R : Set G)).relIndex (Subgroup.normalizer (R : Set G))

end CFSGOutside.DolfiGuralnickHerzogPraeger
