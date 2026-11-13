
/-!
# Copied corpus declarations from `Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean` -/

section

namespace CFSGOutside.Corpus.M.Monster.B.Rep4371.Native

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.popcN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:7. -/
def popcN : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 2 + popcN k (a / 2)

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.parN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:11. -/
def parN (k a : Nat) : Bool := popcN k a % 2 == 1

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.xorSum`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:13. -/
def xorSum (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xorSum f n ^^ f n

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.packN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:17. -/
def packN (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => packN f n ||| (if f n then 2 ^ n else 0)

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.combN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:21. -/
def combN (m : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => combN m n a ^^^ (if a.testBit n then m n else 0)

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.bmaskN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:25. -/
def bmaskN (i : Nat) : Nat :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111, 0xa6c00c, 0x6ca00a, 0x6ac0c0,
    0xc6a0a0, 0xcccc00, 0xaaaa00].getD i 0

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.wordN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:32. -/
def wordN (a : Nat) : Nat := combN bmaskN 12 a

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.dualN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:38. -/
def dualN (v : Nat) : Nat := packN (fun j => parN 24 (v &&& bmaskN j)) 12

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.pN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:48. -/
def pN (a : Nat) : Bool := popcN 24 (wordN a) / 4 % 2 == 1

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.betaN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:54. -/
def betaN (j k : Nat) : Bool :=
  if j < k then false
  else if j = k then popcN 24 (bmaskN j) / 4 % 2 == 1
  else popcN 24 (bmaskN j &&& bmaskN k) / 2 % 2 == 1

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.thetaRec`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:59. -/
def thetaRec : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a =>
    if a.testBit n then
      thetaRec n a ^^^ packN (betaN n) 12 ^^^ dualN (combN bmaskN n a &&& bmaskN n)
    else thetaRec n a

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.thetaN`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:66. -/
def thetaN (a : Nat) : Nat := thetaRec 12 a

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.sgnI`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:104. -/
def sgnI (b : Bool) : Int := if b then -1 else 1

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.oddCode`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:236. -/
def oddCode (c i : Nat) : Nat := c ^^^ (if (wordN c).testBit i ^^ pN c then 63 else 0)

/-- Corpus: `CFSG.Monster.B.Rep4371.Native.octSign`, Certificates/Data/CFSGNative/MonsterB/Rep4371Model.lean:314. -/
def octSign (x z : Nat) : Int := sgnI ((popcN 8 (x &&& z) + popcN 8 z / 2) % 2 == 1)

end CFSGOutside.Corpus.M.Monster.B.Rep4371.Native
