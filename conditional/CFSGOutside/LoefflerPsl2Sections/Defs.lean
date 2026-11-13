import Mathlib

/-! `PSL₂` as used in the statement of Loeffler's lemma, kept apart from the proof so that the challenge can import it. -/

namespace CFSGOutside.LoefflerPsl2Sections

/-- `PSL₂(F) = SL₂(F) / {±1}`. -/
abbrev PSL2 (F : Type) [Field F] := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

end CFSGOutside.LoefflerPsl2Sections
