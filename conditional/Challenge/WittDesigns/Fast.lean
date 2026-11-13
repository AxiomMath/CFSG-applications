import CFSGOutside.WittDesigns.S5824.Design
import CFSGOutside.WittDesigns.S4723.Design
import CFSGOutside.WittDesigns.S5612.Defs
import CFSGOutside.WittDesigns.AutS5612.Hexads
import CFSGOutside.WittDesigns.AutS5612.Transitive
import CFSGOutside.Corpus.Defs.WittDesign
import CFSGOutside.Corpus.SteinerTripleIso
import CFSGOutside.Corpus.IsSteinerTripleHexads
import CFSGOutside.Corpus.IsSteinerTripleCardInter
import CFSGOutside.Corpus.CardHexads
import CFSGOutside.Corpus.CardHexadAut
import CFSGOutside.Corpus.M22LeHexadAut
import CFSGOutside.Corpus.IsMultiplyPretransitiveM22
import CFSGOutside.Corpus.M22Simple
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-!
# Witt's designs (fast path)

E. Witt, *Über Steinersche Systeme* and *Die 5-fach transitiven Gruppen von Mathieu*, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–275: the Steiner systems `S(5,8,24)`, `S(4,7,23)` and `S(5,6,12)` are unique, and their automorphism groups have the orders of `M24`, `M23` and `M12` and are multiply transitive. Conditional on the corpus inputs stated as classes in `CFSGOutside.Corpus`.
-/

universe u v

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- **Witt (1938).** Any two Steiner systems `S(5,8,24)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem witt_S5824_unique {Ω : Type u} {Ω' : Type v} [SteinerTripleIso.{u, 0}] [SteinerTripleIso.{v, 0}]
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝒮 : Finset (Finset Ω)} {𝒮' : Finset (Finset Ω')} (h : IsSteiner5 𝒮)
    (h' : IsSteiner5 𝒮') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒮 ↔ B.map f.toEmbedding ∈ 𝒮' :=
  sorry

end CFSGOutside.WittDesigns.Witt5824

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

/-- **Witt (1938).** Any two Steiner systems `S(4,7,23)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem witt_S4723_unique {Ω : Type u} {Ω' : Type v} [SteinerTripleIso.{u, 0}] [SteinerTripleIso.{v, 0}]
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : IsSteiner4 𝒯)
    (h' : IsSteiner4 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' :=
  sorry

end CFSGOutside.WittDesigns.Witt4723

namespace CFSGOutside.WittDesigns.Witt5612

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

/-- **Witt (1938).** Any two Steiner systems `S(5,6,12)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem witt_S5612_unique {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] (hΩ : Fintype.card Ω = 12) (hΩ' : Fintype.card Ω' = 12)
    {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : IsSteiner 𝒯) (h' : IsSteiner 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' :=
  sorry

end CFSGOutside.WittDesigns.Witt5612

namespace CFSGOutside.WittDesigns.Aut5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt5824

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

/-- The automorphism group of `S(5,8,24)` has order `|M24|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem card_aut_S5824 {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒮 : Finset (Finset Ω)}
    (h : IsSteiner5 𝒮) : Nat.card (blockAut 𝒮) = 244823040 :=
  sorry

end CFSGOutside.WittDesigns.Aut5824

namespace CFSGOutside.WittDesigns.Aut4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt4723

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

/-- The automorphism group of `S(4,7,23)` has order `|M23|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem card_aut_S4723 {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner4 𝒯) : Nat.card (blockAut 𝒯) = 10200960 :=
  sorry

end CFSGOutside.WittDesigns.Aut4723

namespace CFSGOutside.WittDesigns.M24Five

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt5824

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple]

/-- The automorphism group of `S(5,8,24)` is 5-transitive of order `|M24|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem aut_S5824_five_transitive {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒮 : Finset (Finset Ω)}
    (h : IsSteiner5 𝒮) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒮) Ω 5 ∧ Nat.card (blockAut 𝒮) = 244823040 :=
  sorry

end CFSGOutside.WittDesigns.M24Five

namespace CFSGOutside.WittDesigns.M24Four

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt4723

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] [M22LeHexadAut] [IsMultiplyPretransitiveM22] [M22Simple]

/-- The automorphism group of `S(4,7,23)` is 4-transitive of order `|M23|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem aut_S4723_four_transitive {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner4 𝒯) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒯) Ω 4 ∧ Nat.card (blockAut 𝒯) = 10200960 :=
  sorry

end CFSGOutside.WittDesigns.M24Four

namespace CFSGOutside.WittDesigns.Witt5612

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

/-- The permutations of 12 points preserving the hexads of `S(5,6,12)` form `M12`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem autHexads_eq_m12 : autHexads = M12 :=
  sorry

end CFSGOutside.WittDesigns.Witt5612

namespace CFSGOutside.WittDesigns.Witt5612

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

/-- `Aut S(5,6,12) = M12` is sharply 5-transitive of order 95040.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem aut_hexads_sharply_five_transitive :
    IsSteiner56 hexads ∧ MulAction.IsMultiplyPretransitive autHexads (Fin 12) 5 ∧
      Nat.card autHexads = (12).descFactorial 5 :=
  sorry

end CFSGOutside.WittDesigns.Witt5612
