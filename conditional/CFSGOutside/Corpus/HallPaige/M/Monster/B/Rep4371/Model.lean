
/-!
# Copied corpus declarations from `CFSG/Monster/B/Rep4371/Model.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Monster/B/Rep4371/Model.lean` -/

section

namespace CFSGOutside.Corpus.M.Monster.B.Model

/-- Corpus: `CFSG.Monster.B.Model.popcN`, CFSG/Monster/B/Rep4371/Model.lean:7. -/
def popcN : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 2 + popcN k (a / 2)

/-- Corpus: `CFSG.Monster.B.Model.parN`, CFSG/Monster/B/Rep4371/Model.lean:11. -/
def parN (k a : Nat) : Bool := popcN k a % 2 == 1

/-- Corpus: `CFSG.Monster.B.Model.xorSum`, CFSG/Monster/B/Rep4371/Model.lean:13. -/
def xorSum (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xorSum f n ^^ f n

/-- Corpus: `CFSG.Monster.B.Model.packN`, CFSG/Monster/B/Rep4371/Model.lean:17. -/
def packN (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => packN f n ||| (if f n then 2 ^ n else 0)

/-- Corpus: `CFSG.Monster.B.Model.combN`, CFSG/Monster/B/Rep4371/Model.lean:21. -/
def combN (m : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => combN m n a ^^^ (if a.testBit n then m n else 0)

/-- Corpus: `CFSG.Monster.B.Model.bmaskN`, CFSG/Monster/B/Rep4371/Model.lean:25. -/
def bmaskN (i : Nat) : Nat :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111, 0xa6c00c, 0x6ca00a, 0x6ac0c0,
    0xc6a0a0, 0xcccc00, 0xaaaa00].getD i 0

/-- Corpus: `CFSG.Monster.B.Model.umaskN`, CFSG/Monster/B/Rep4371/Model.lean:29. -/
def umaskN (k : Nat) : Nat :=
  [0xe, 0x1f, 0x10f, 0x100f, 0x1000f, 0x11111, 0xa, 0xc, 0x5f, 0x3f, 0x50f, 0x30f].getD k 0

/-- Corpus: `CFSG.Monster.B.Model.wordN`, CFSG/Monster/B/Rep4371/Model.lean:32. -/
def wordN (a : Nat) : Nat := combN bmaskN 12 a

/-- Corpus: `CFSG.Monster.B.Model.repN`, CFSG/Monster/B/Rep4371/Model.lean:34. -/
def repN (d : Nat) : Nat := combN umaskN 12 d

/-- Corpus: `CFSG.Monster.B.Model.dualN`, CFSG/Monster/B/Rep4371/Model.lean:38. -/
def dualN (v : Nat) : Nat := packN (fun j => parN 24 (v &&& bmaskN j)) 12

/-- Corpus: `CFSG.Monster.B.Model.pairN`, CFSG/Monster/B/Rep4371/Model.lean:40. -/
def pairN (a d : Nat) : Bool := parN 12 (a &&& d)

/-- Corpus: `CFSG.Monster.B.Model.pN`, CFSG/Monster/B/Rep4371/Model.lean:48. -/
def pN (a : Nat) : Bool := popcN 24 (wordN a) / 4 % 2 == 1

/-- Corpus: `CFSG.Monster.B.Model.acodeN`, CFSG/Monster/B/Rep4371/Model.lean:52. -/
def acodeN (a b : Nat) : Nat := dualN (wordN a &&& wordN b)

/-- Corpus: `CFSG.Monster.B.Model.betaN`, CFSG/Monster/B/Rep4371/Model.lean:54. -/
def betaN (j k : Nat) : Bool :=
  if j < k then false
  else if j = k then popcN 24 (bmaskN j) / 4 % 2 == 1
  else popcN 24 (bmaskN j &&& bmaskN k) / 2 % 2 == 1

/-- Corpus: `CFSG.Monster.B.Model.thetaRec`, CFSG/Monster/B/Rep4371/Model.lean:59. -/
def thetaRec : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a =>
    if a.testBit n then
      thetaRec n a ^^^ packN (betaN n) 12 ^^^ dualN (combN bmaskN n a &&& bmaskN n)
    else thetaRec n a

/-- Corpus: `CFSG.Monster.B.Model.thetaN`, CFSG/Monster/B/Rep4371/Model.lean:66. -/
def thetaN (a : Nat) : Nat := thetaRec 12 a

/-- Corpus: `CFSG.Monster.B.Model.thetaBit`, CFSG/Monster/B/Rep4371/Model.lean:68. -/
def thetaBit (a b : Nat) : Bool := pairN b (thetaN a)

/-- Corpus: `CFSG.Monster.B.Model.Pauli`, CFSG/Monster/B/Rep4371/Model.lean:70. -/
abbrev Pauli : Type := Bool × Nat × Nat

/-- Corpus: `CFSG.Monster.B.Model.Pauli.s`, CFSG/Monster/B/Rep4371/Model.lean:72. -/
@[reducible] def Pauli.s (x : Pauli) : Bool := x.1

/-- Corpus: `CFSG.Monster.B.Model.Pauli.a`, CFSG/Monster/B/Rep4371/Model.lean:74. -/
@[reducible] def Pauli.a (x : Pauli) : Nat := x.2.1

/-- Corpus: `CFSG.Monster.B.Model.Pauli.d`, CFSG/Monster/B/Rep4371/Model.lean:76. -/
@[reducible] def Pauli.d (x : Pauli) : Nat := x.2.2

/-- Corpus: `CFSG.Monster.B.Model.Pauli.mul`, CFSG/Monster/B/Rep4371/Model.lean:78. -/
def Pauli.mul (x y : Pauli) : Pauli :=
  (x.s ^^ y.s ^^ pairN y.a x.d, x.a ^^^ y.a, x.d ^^^ y.d)

/-- Corpus: `CFSG.Monster.B.Model.conjTN`, CFSG/Monster/B/Rep4371/Model.lean:112. -/
def conjTN (a b : Nat) : Pauli :=
  (thetaBit b a, b ^^^ (if thetaBit a b then 63 else 0), acodeN a b)

/-- Corpus: `CFSG.Monster.B.Model.conjDN`, CFSG/Monster/B/Rep4371/Model.lean:115. -/
def conjDN (a d : Nat) : Pauli :=
  (!pairN 63 d && pairN a d,
    (if pairN 63 d then a else 0) ^^^ (if (pairN 63 d && pN a) ^^ pairN a d then 63 else 0),
    (if pairN 63 d then thetaN a else 0) ^^^ d)

/-- Corpus: `CFSG.Monster.B.Model.conjYN`, CFSG/Monster/B/Rep4371/Model.lean:120. -/
def conjYN (a : Nat) (y : Pauli) : Pauli :=
  Pauli.mul (Pauli.mul (y.s, 0, 0) (conjTN a y.a)) (conjDN a y.d)

end CFSGOutside.Corpus.M.Monster.B.Model
