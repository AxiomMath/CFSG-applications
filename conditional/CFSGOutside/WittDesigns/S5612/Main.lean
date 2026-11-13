import Mathlib
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty
import CFSGOutside.WittDesigns.S5612.Final
import CFSGOutside.WittDesigns.S5612.Count123

/-!
# Witt (1938): the Steiner system `S(5,6,12)` is unique

Any two Steiner systems `S(5,6,12)` are isomorphic.  The hexads of the explicit system (with
`Aut = M12` of order 95040, sharply 5-transitive) show that the stabilizer of a block has order 720, so
the translates of the hexads under the stabilizer of a 6-set number 720.  An exhaustive search, checked
by kernel evaluation, completes a fixed block to a Steiner system in exactly 720 ways, so every
`S(5,6,12)` is such a translate.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

/-- **Witt (1938).** Any two Steiner systems `S(5,6,12)` are isomorphic. -/
theorem witt_S5612_unique {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] (hΩ : Fintype.card Ω = 12) (hΩ' : Fintype.card Ω' = 12)
    {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : IsSteiner 𝒯) (h' : IsSteiner 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' :=
  witt_S5612_unique_of_count go_length_123 hΩ hΩ' h h'

end CFSGOutside.WittDesigns.Witt5612
