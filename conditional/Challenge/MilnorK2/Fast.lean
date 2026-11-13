import CFSGOutside.MilnorK2.Defs
import CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv

/-!
# Milnor, `K₂` of a finite field (fast path)

J. Milnor, *Introduction to Algebraic K-theory*, Annals of Mathematics Studies 72, Princeton University
Press, 1971, DOI 10.1515/9781400881796 (Steinberg's theorem `K₂(F_q) = 1`). Conditional on the Steinberg
presentation of `SL_{m+1}(F)`, stated as a class in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.MilnorK2

variable {F : Type} [Field F]

/-- **`K₂(F) = 1` for every finite field `F`** (Milnor, *Introduction to Algebraic K-theory*,
1971, §9; theorem of Steinberg): `K₂ F = ker (St(F) → GL(F))` is trivial. -/
theorem K₂_eq_bot [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] : K₂ F = ⊥ := sorry

/-- Equivalently (Milnor 1971, §9; Steinberg), `St(F) → GL(F)` is injective for a finite field `F`. -/
theorem stToGL_injective [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] :
    Function.Injective (stToGL ℕ F) := sorry

end CFSGOutside.MilnorK2
