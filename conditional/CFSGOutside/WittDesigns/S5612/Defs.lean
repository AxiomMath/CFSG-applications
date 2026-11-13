import Mathlib

/-! The Steiner systems `S(5,6,12)`, kept apart from their proofs so that challenge statements can import them. -/

namespace CFSGOutside.WittDesigns.Witt5612

/-- A Steiner system `S(5,6,12)` on a 12-element type: blocks of size 6, every 5-set in exactly one block. -/
def IsSteiner {Ω : Type*} [DecidableEq Ω] (𝒯 : Finset (Finset Ω)) : Prop :=
  (∀ B ∈ 𝒯, B.card = 6) ∧ ∀ s : Finset Ω, s.card = 5 → ∃! B, B ∈ 𝒯 ∧ s ⊆ B

end CFSGOutside.WittDesigns.Witt5612
