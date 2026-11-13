import Mathlib

/-!
# Copied corpus definitions: the order of a Ree group and the matrix models of `J₁`

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The clean build proves
each copy equal to its corpus original in `clean/CFSGOutsideClean/Corpus/Defs/J1Models.lean`.
`walterJ1` and `goldschmidtJ1` are two corpus copies of the same matrix group in `GL₇(𝔽₁₁)`.
-/

namespace CFSGOutside.Corpus.Open

open Matrix
open scoped MatrixGroups

/-- `|²G₂(q)| = q³(q³+1)(q-1)`. Copy of `CFSG.Open.ordRee`, `CFSG/Open/Defs.lean` line 56. -/
def ordRee (q : ℕ) : ℕ := q ^ 3 * (q ^ 3 + 1) * (q - 1)

/-- First generator of the matrix model of `J₁`. Copy of `CFSG.Open.walterJ1GenA`,
`CFSG/Open/WalterAbelianSylowTwoMilestoneDefs.lean` line 12. -/
def walterJ1GenA : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 7, 9, 9, 10, 7, 9;
     7, 0, 1, 4, 3, 3, 4;
     9, 1, 2, 8, 3, 6, 2;
     9, 4, 8, 10, 1, 6, 0;
     10, 3, 3, 1, 8, 9, 1;
     7, 3, 6, 6, 9, 1, 3;
     9, 4, 2, 0, 1, 3, 0]

/-- Second generator of the matrix model of `J₁`. Copy of `CFSG.Open.walterJ1GenB`,
`CFSG/Open/WalterAbelianSylowTwoMilestoneDefs.lean` line 21. -/
def walterJ1GenB : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 7, 1, 8, 5, 8, 2;
     10, 4, 10, 0, 3, 3, 8;
     5, 10, 8, 9, 1, 2, 1;
     2, 3, 3, 6, 1, 2, 9;
     7, 4, 7, 2, 10, 7, 3;
     3, 9, 0, 4, 2, 3, 5;
     3, 4, 3, 3, 9, 4, 9]

/-- The Janko group `J₁` as a subgroup of `GL₇(𝔽₁₁)`. Copy of `CFSG.Open.walterJ1`,
`CFSG/Open/WalterAbelianSylowTwoMilestoneDefs.lean` line 30. -/
def walterJ1 : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {g | (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = walterJ1GenA ∨
    (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = walterJ1GenB}

/-- First generator of the second matrix model of `J₁`. Copy of `CFSG.Open.goldschmidtJ1GenA`,
`CFSG/Open/GoldschmidtStronglyClosedAbelianMilestoneDefs.lean` line 30. -/
def goldschmidtJ1GenA : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 7, 9, 9, 10, 7, 9;
     7, 0, 1, 4, 3, 3, 4;
     9, 1, 2, 8, 3, 6, 2;
     9, 4, 8, 10, 1, 6, 0;
     10, 3, 3, 1, 8, 9, 1;
     7, 3, 6, 6, 9, 1, 3;
     9, 4, 2, 0, 1, 3, 0]

/-- Second generator of the second matrix model of `J₁`. Copy of `CFSG.Open.goldschmidtJ1GenB`,
`CFSG/Open/GoldschmidtStronglyClosedAbelianMilestoneDefs.lean` line 39. -/
def goldschmidtJ1GenB : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 7, 1, 8, 5, 8, 2;
     10, 4, 10, 0, 3, 3, 8;
     5, 10, 8, 9, 1, 2, 1;
     2, 3, 3, 6, 1, 2, 9;
     7, 4, 7, 2, 10, 7, 3;
     3, 9, 0, 4, 2, 3, 5;
     3, 4, 3, 3, 9, 4, 9]

/-- The Janko group `J₁` as a subgroup of `GL₇(𝔽₁₁)`, second corpus copy. Copy of
`CFSG.Open.goldschmidtJ1`, `CFSG/Open/GoldschmidtStronglyClosedAbelianMilestoneDefs.lean` line 48. -/
def goldschmidtJ1 : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {g | (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenA ∨
    (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenB}

end CFSGOutside.Corpus.Open
