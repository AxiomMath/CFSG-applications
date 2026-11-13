import CFSGOutside.Corpus.HallPaige.Ly.Data

/-!
# Copied corpus definitions: packed 111 × 111 matrices over `𝔽₅`

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 (each docstring names the corpus
declaration and file:line), in the namespace `CFSGOutside.Corpus.Ly`.
-/

namespace CFSGOutside.Corpus.Ly

/-- Corpus: `CFSG.KS.LyOm.ent`, CFSG/Certificates/Kernel/LyOmega/Defs.lean:45. -/
def ent (w S X i j : ℕ) : ZMod 5 := ((X / 2 ^ (S * i + w * j) % 2 ^ w : ℕ) : ZMod 5)

/-- Corpus: `CFSG.KS.LyOm.bigM`, CFSG/Certificates/Kernel/LyOmega/Defs.lean:49. -/
def bigM (X : ℕ) : Matrix (Fin 111) (Fin 111) (ZMod 5) := fun i j => ent 12 1332 X i j

/-- Corpus: `CFSG.KS.LyOm.LCanon`, CFSG/Certificates/Kernel/LyOmega/Defs.lean:57. -/
def LCanon (w r c X : ℕ) : Prop :=
  X < 2 ^ (w * c * r) ∧ ∀ i < r, ∀ j < c, X / 2 ^ (w * c * i + w * j) % 2 ^ w < 5

/-- Corpus: `CFSG.KC.Ord.mulU`, CFSG/Certificates/Kernel/Orders/Mat.lean:20. -/
noncomputable def mulU (w S d CM RM A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul w k)) CM)
      (Nat.land (Nat.shiftRight B (Nat.mul S k)) RM))) d

/-- Corpus: `CFSG.KC.Ord.csub`, CFSG/Certificates/Kernel/Orders/Mat.lean:25. -/
noncomputable def csub (w L H c x : Nat) : Nat :=
  Nat.sub x (Nat.mul (Nat.shiftRight (Nat.land (Nat.sub (Nat.lor x H) (Nat.mul c L)) H)
    (Nat.sub w (nat_lit 1))) c)

/-- Corpus: `CFSG.KC.Ord.redP`, CFSG/Certificates/Kernel/Orders/Mat.lean:29. -/
noncomputable def redP (w L H p T x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => csub w L H (Nat.shiftLeft p (Nat.sub T i)) acc) (Nat.succ T)

/-- Corpus: `CFSG.KC.Ord.mulR`, CFSG/Certificates/Kernel/Orders/Mat.lean:33. -/
noncomputable def mulR (p w S d T L H CM RM A B : Nat) : Nat :=
  redP w L H p T (mulU w S d CM RM A B)

/-- Corpus: `CFSG.KC.LyOm.BConsts`, Certificates/Data/Kernel/LyOmega/Chart.lean:11. -/
structure BConsts where
  L7 : Nat
  H7 : Nat
  CM7 : Nat
  ONE7 : Nat
  MASK7 : Nat
  LV : Nat
  HV : Nat
  LW : Nat
  HW : Nat
  LF : Nat
  HF : Nat
  CMF : Nat
  ONEF : Nat

/-- Corpus: `CFSG.KC.LyOm.rmB`, Certificates/Data/Kernel/LyOmega/Chart.lean:42. -/
noncomputable def rmB : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1332)) (nat_lit 1)

/-- Corpus: `CFSG.KC.LyOm.fMul`, Certificates/Data/Kernel/LyOmega/Chart.lean:123. -/
noncomputable def fMul (C : BConsts) (X Y : Nat) : Nat :=
  mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111) (nat_lit 8) C.LF C.HF C.CMF rmB X Y

/-- Corpus: `CFSG.KD.LyOm.BC`, Certificates/Kernel/Ly3085/Omega/Data.lean:21. -/
noncomputable def BC : BConsts :=
  ⟨bL7, bH7, bCM7, bONE7, bMASK7, bLV, bHV, bLW, bHW, fLF, fHF, fCMF, fONEF⟩

end CFSGOutside.Corpus.Ly
