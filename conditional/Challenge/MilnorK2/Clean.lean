import CFSGOutside.MilnorK2.Defs

/-!
# Milnor, `K₂` of a finite field

J. Milnor, *Introduction to Algebraic K-theory*, Annals of Mathematics Studies 72, Princeton University
Press, 1971, DOI 10.1515/9781400881796 (Steinberg's theorem `K₂(F_q) = 1`). Here `St(F)` is the Steinberg
group on generators `x_ij(a)`, `i ≠ j` in `ℕ`, with Steinberg's relations, and `K₂ F` is the kernel of
`St(F) → GL(F)` (see `CFSGOutside.MilnorK2.Defs`).
-/

namespace CFSGOutsideClean.MilnorK2

open CFSGOutside.MilnorK2

variable {F : Type} [Field F]

/-- **`K₂(F) = 1` for every finite field `F`** (Milnor, *Introduction to Algebraic K-theory*,
1971, §9; theorem of Steinberg): `K₂ F = ker (St(F) → GL(F))` is trivial. -/
theorem K₂_eq_bot [Finite F] : K₂ F = ⊥ := sorry

/-- Equivalently (Milnor 1971, §9; Steinberg), `St(F) → GL(F)` is injective for a finite field `F`. -/
theorem stToGL_injective [Finite F] : Function.Injective (stToGL ℕ F) := sorry

end CFSGOutsideClean.MilnorK2
