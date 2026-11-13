import CFSGOutside.MilnorK2.Fidelity
import CFSGOutsideClean.Corpus.ExistsSteinbergSLRelsEquiv

/-! Milnor (1971), `K₂(F) = 1` for every finite field `F`, in Milnor's matrix form: `St(F)` is the
direct limit of the `St(n, F)` (`CFSGOutside.MilnorK2.exists_unique_lift`), and the kernel of
`St(F) → GL(F)` is computed in the matrix groups `GL(n, F)` (`CFSGOutside.MilnorK2.incl_mem_K₂_iff`).
The Steinberg presentation of `SL_{m+1}(F)` is supplied by the corpus. -/

namespace CFSGOutsideClean.MilnorK2

open CFSGOutside.MilnorK2

variable {F : Type} [Field F]

/-- **`K₂(F) = 1` for a finite field `F`, matrix form** (Milnor, *Introduction to Algebraic
K-theory*, 1971, Cor. 9.13; Steinberg): an element of `St(n, F)` whose image in `GL(n, F)` is the
identity matrix is trivial in `St(F)`. -/
theorem incl_eq_one_of_stToMatrix_eq_one [Finite F] {n : ℕ} (t : Steinberg (Fin n) F)
    (ht : stToMatrix n t = 1) : incl n t = 1 :=
  CFSGOutside.MilnorK2.incl_eq_one_of_stToMatrix_eq_one t ht

/-- The unstable form (Steinberg): `St(n, F) → GL(n, F)` is injective for `n ≥ 3`. -/
theorem stToMatrix_injective [Finite F] {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (stToMatrix (R := F) n) :=
  CFSGOutside.MilnorK2.stToMatrix_injective hn

end CFSGOutsideClean.MilnorK2
