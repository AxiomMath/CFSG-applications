import CFSGOutside.WittDesigns.S5824.Design
import CFSGOutside.WittDesigns.S4723.Design
import CFSGOutside.WittDesigns.S5612.Final
import CFSGOutside.WittDesigns.AutS5612.Hexads
import CFSGOutside.WittDesigns.AutS5612.Transitive
import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Witt's designs, with the corpus supplying its inputs

The uniqueness of the Steiner systems `S(5,8,24)`, `S(4,7,23)` and `S(5,6,12)`, the orders of their automorphism
groups (`|M24|`, `|M23|`, `|M12|`) and their 5-, 4- and 5-fold transitivity, with the uniqueness of `S(3,6,22)`, the
hexads of `S(3,6,22)`, the action of `M22` on them, the simplicity of `M22` and the classification of 5-transitive
groups of degree at most 80 supplied by the corpus.
-/

universe u v

open CFSGOutside.WittDesigns CFSGOutside.Corpus.WittDesign

/-- **Witt (1938).** Any two Steiner systems `S(5,8,24)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.witt_S5824_unique {Ω : Type u} {Ω' : Type v} [Fintype Ω]
    [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] {𝒮 : Finset (Finset Ω)} {𝒮' : Finset (Finset Ω')}
    (h : Witt5824.IsSteiner5 𝒮) (h' : Witt5824.IsSteiner5 𝒮') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒮 ↔ B.map f.toEmbedding ∈ 𝒮' :=
  sorry

/-- **Witt (1938).** Any two Steiner systems `S(4,7,23)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.witt_S4723_unique {Ω : Type u} {Ω' : Type v} [Fintype Ω]
    [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')}
    (h : Witt4723.IsSteiner4 𝒯) (h' : Witt4723.IsSteiner4 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' :=
  sorry

/-- **Witt (1938).** Any two Steiner systems `S(5,6,12)` are isomorphic.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.witt_S5612_unique {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ω'] [DecidableEq Ω'] (hΩ : Fintype.card Ω = 12) (hΩ' : Fintype.card Ω' = 12)
    {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : Witt5612.IsSteiner 𝒯) (h' : Witt5612.IsSteiner 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' :=
  sorry

/-- The automorphism group of `S(5,8,24)` has order `|M24|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.card_aut_S5824 {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {𝒮 : Finset (Finset Ω)} (h : Witt5824.IsSteiner5 𝒮) :
    Nat.card (blockAut 𝒮) = 244823040 :=
  sorry

/-- The automorphism group of `S(4,7,23)` has order `|M23|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.card_aut_S4723 {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {𝒯 : Finset (Finset Ω)} (h : Witt4723.IsSteiner4 𝒯) :
    Nat.card (blockAut 𝒯) = 10200960 :=
  sorry

/-- The automorphism group of `S(5,8,24)` is 5-transitive of order `|M24|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.aut_S5824_five_transitive {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] {𝒮 : Finset (Finset Ω)} (h : Witt5824.IsSteiner5 𝒮) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒮) Ω 5 ∧ Nat.card (blockAut 𝒮) = 244823040 :=
  sorry

/-- The automorphism group of `S(4,7,23)` is 4-transitive of order `|M23|`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.aut_S4723_four_transitive {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] {𝒯 : Finset (Finset Ω)} (h : Witt4723.IsSteiner4 𝒯) :
    MulAction.IsMultiplyPretransitive (blockAut 𝒯) Ω 4 ∧ Nat.card (blockAut 𝒯) = 10200960 :=
  sorry

/-- The permutations of 12 points preserving the hexads of `S(5,6,12)` form `M12`.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.autHexads_eq_m12 : Witt5612.autHexads = Witt5612.M12 :=
  sorry

/-- `Aut S(5,6,12) = M12` is sharply 5-transitive of order 95040.

Source: E. Witt, Die 5-fach transitiven Gruppen von Mathieu, Abh. Math. Sem. Univ. Hamburg 12 (1938), 256–264, and Über Steinersche Systeme, Abh. Math. Sem. Univ. Hamburg 12 (1938), 265–275. https://doi.org/10.1007/BF02948948 -/
theorem CFSGOutsideClean.WittDesigns.aut_hexads_sharply_five_transitive :
    Witt5612.IsSteiner56 Witt5612.hexads ∧ MulAction.IsMultiplyPretransitive Witt5612.autHexads (Fin 12) 5 ∧
      Nat.card Witt5612.autHexads = (12).descFactorial 5 :=
  sorry
