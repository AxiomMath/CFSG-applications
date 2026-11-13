import Mathlib

/-!
# Copied corpus definitions: the Steiner system `S(3,6,22)` and `M22`

Definitions copied verbatim (only `@[expose]` dropped) from AxiomMath/CFSG at commit
69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus` so that the clean build, which imports the corpus
too, sees no clash:

* `NativeSporadic.M22` from `CFSG.Blueprint.NativeSporadic.M22`, `CFSG/Blueprint/NativeSporadic.lean` line 35;
* `WittDesign.IsSteinerTriple` from `CFSG.ComponentClassification.WittDesign.IsSteinerTriple`,
  `CFSG/LocalAnalysis/ComponentClassification/WittDesignSteiner3.lean` line 11;
* `WittDesign.hexadList` from `CFSG.ComponentClassification.WittDesign.hexadList`,
  `CFSG/LocalAnalysis/ComponentClassification/WittDesignM22HexadsInputs.lean` line 17;
* `WittDesign.hexads` from `CFSG.ComponentClassification.WittDesign.hexads`,
  `CFSG/LocalAnalysis/ComponentClassification/WittDesignM22HexadsBase.lean` line 21;
* `WittDesign.M22` from `CFSG.ComponentClassification.WittDesign.M22`,
  `CFSG/LocalAnalysis/ComponentClassification/WittDesignM22Count.lean` line 12.

The clean build proves each copy equal to its original in `results_unconditional/CFSGOutsideClean/Corpus/Defs/WittDesign.lean`.
-/

namespace CFSGOutside.Corpus

namespace NativeSporadic

/-- The Mathieu group `M22` as a permutation group on `Fin 22`. Copy of `CFSG.Blueprint.NativeSporadic.M22`. -/
noncomputable def M22 : Subgroup (Equiv.Perm (Fin 22)) :=
  Subgroup.closure {(List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]),
    (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])}

end NativeSporadic

namespace WittDesign

section
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A Steiner system `S(3,6,22)`: 22 points, blocks of size 6, every 3 points in exactly one block. Copy of
`CFSG.ComponentClassification.WittDesign.IsSteinerTriple`. -/
def IsSteinerTriple (𝓑 : Finset (Finset Ω)) : Prop :=
  Fintype.card Ω = 22 ∧ (∀ B ∈ 𝓑, B.card = 6) ∧
    ∀ T : Finset Ω, T.card = 3 → ∃! B, B ∈ 𝓑 ∧ T ⊆ B

end

/-- The 77 hexads of the Steiner system `S(3,6,22)`. Copy of `CFSG.ComponentClassification.WittDesign.hexadList`. -/
def hexadList : List (Finset (Fin 22)) :=
  [{0, 1, 2, 9, 17, 19}, {0, 1, 3, 6, 14, 20}, {0, 1, 4, 5, 13, 18}, {0, 1, 7, 8, 16, 21},
    {0, 1, 10, 11, 12, 15}, {0, 2, 3, 7, 12, 13}, {0, 2, 4, 11, 20, 21}, {0, 2, 5, 6, 8, 15},
    {0, 2, 10, 14, 16, 18}, {0, 3, 4, 8, 10, 17}, {0, 3, 5, 9, 11, 16}, {0, 3, 15, 18, 19, 21},
    {0, 4, 6, 12, 16, 19}, {0, 4, 7, 9, 14, 15}, {0, 5, 7, 10, 19, 20}, {0, 5, 12, 14, 17, 21},
    {0, 6, 7, 11, 17, 18}, {0, 6, 9, 10, 13, 21}, {0, 8, 9, 12, 18, 20}, {0, 8, 11, 13, 14, 19},
    {0, 13, 15, 16, 17, 20}, {1, 2, 3, 5, 10, 21}, {1, 2, 4, 8, 12, 14}, {1, 2, 6, 11, 13, 16},
    {1, 2, 7, 15, 18, 20}, {1, 3, 4, 7, 11, 19}, {1, 3, 8, 9, 13, 15}, {1, 3, 12, 16, 17, 18},
    {1, 4, 6, 15, 17, 21}, {1, 4, 9, 10, 16, 20}, {1, 5, 6, 7, 9, 12}, {1, 5, 8, 11, 17, 20},
    {1, 5, 14, 15, 16, 19}, {1, 6, 8, 10, 18, 19}, {1, 7, 10, 13, 14, 17}, {1, 9, 11, 14, 18, 21},
    {1, 12, 13, 19, 20, 21}, {2, 3, 4, 6, 9, 18}, {2, 3, 8, 16, 19, 20}, {2, 3, 11, 14, 15, 17},
    {2, 4, 5, 7, 16, 17}, {2, 4, 10, 13, 15, 19}, {2, 5, 9, 13, 14, 20}, {2, 5, 11, 12, 18, 19},
    {2, 6, 7, 14, 19, 21}, {2, 6, 10, 12, 17, 20}, {2, 7, 8, 9, 10, 11}, {2, 8, 13, 17, 18, 21},
    {2, 9, 12, 15, 16, 21}, {3, 4, 5, 12, 15, 20}, {3, 4, 13, 14, 16, 21}, {3, 5, 6, 13, 17, 19},
    {3, 5, 7, 8, 14, 18}, {3, 6, 7, 10, 15, 16}, {3, 6, 8, 11, 12, 21}, {3, 7, 9, 17, 20, 21},
    {3, 9, 10, 12, 14, 19}, {3, 10, 11, 13, 18, 20}, {4, 5, 6, 10, 11, 14}, {4, 5, 8, 9, 19, 21},
    {4, 6, 7, 8, 13, 20}, {4, 7, 10, 12, 18, 21}, {4, 8, 11, 15, 16, 18}, {4, 9, 11, 12, 13, 17},
    {4, 14, 17, 18, 19, 20}, {5, 6, 16, 18, 20, 21}, {5, 7, 11, 13, 15, 21},
    {5, 8, 10, 12, 13, 16}, {5, 9, 10, 15, 17, 18}, {6, 8, 9, 14, 16, 17}, {6, 9, 11, 15, 19, 20},
    {6, 12, 13, 14, 15, 18}, {7, 8, 12, 15, 17, 19}, {7, 9, 13, 16, 18, 19},
    {7, 11, 12, 14, 16, 20}, {8, 10, 14, 15, 20, 21}, {10, 11, 16, 17, 19, 21}]

/-- The hexads as a finset. Copy of `CFSG.ComponentClassification.WittDesign.hexads`. -/
def hexads : Finset (Finset (Fin 22)) := hexadList.toFinset

/-- Copy of `CFSG.ComponentClassification.WittDesign.M22`. -/
noncomputable abbrev M22 : Subgroup (Equiv.Perm (Fin 22)) := NativeSporadic.M22


section BlockAut

variable {P : Type*}

theorem map_perm_mul' (σ τ : Equiv.Perm P) (B : Finset P) :
    B.map (σ * τ).toEmbedding = (B.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

/-- Copy of `CFSG.ComponentClassification.WittDesign.blockAut`
(`WittDesignPlaneAxioms.lean`, line 157). -/
def blockAut (𝓛 : Finset (Finset P)) : Subgroup (Equiv.Perm P) where
  carrier := {σ | ∀ B : Finset P, B.map σ.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛}
  mul_mem' {σ τ} hσ hτ B := by
    change B.map (σ * τ).toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [map_perm_mul', hσ, hτ]
  one_mem' B := by
    change B.map (1 : Equiv.Perm P).toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [show (1 : Equiv.Perm P).toEmbedding = Function.Embedding.refl P from rfl, Finset.map_refl]
  inv_mem' {σ} hσ B := by
    change B.map σ⁻¹.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [← hσ, ← map_perm_mul', mul_inv_cancel,
      show (1 : Equiv.Perm P).toEmbedding = Function.Embedding.refl P from rfl, Finset.map_refl]

theorem mem_blockAut {𝓛 : Finset (Finset P)} {σ : Equiv.Perm P} :
    σ ∈ blockAut 𝓛 ↔ ∀ B : Finset P, B.map σ.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛 := Iff.rfl

end BlockAut

theorem mem_hexads {B : Finset (Fin 22)} : B ∈ hexads ↔ B ∈ hexadList := List.mem_toFinset

/-- Copy of `CFSG.ComponentClassification.WittDesign.hexadAut` (`WittDesignWittAut.lean`, line 57). -/
abbrev hexadAut : Subgroup (Equiv.Perm (Fin 22)) := blockAut hexads

section SteinerTripleBasic

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝓑 : Finset (Finset Ω)}

theorem IsSteinerTriple.card_points (h : IsSteinerTriple 𝓑) : Fintype.card Ω = 22 := h.1

theorem IsSteinerTriple.card_block (h : IsSteinerTriple 𝓑) {B : Finset Ω} (hB : B ∈ 𝓑) :
    B.card = 6 := h.2.1 B hB

end SteinerTripleBasic

end WittDesign

end CFSGOutside.Corpus
