import Std.Data.HashMap
import CFSGOutside.Corpus.HallPaige.M.Certificates.Data.CFSGNative.MonsterB.Rep4371Model

/-!
# Copied corpus declarations from `Certificates/Data/CFSGNative/MonsterAxis/Basic.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `Certificates/Data/CFSGNative/MonsterAxis/Basic.lean` -/

section

namespace CFSGOutside.Corpus.M.Monster.AxisCount.Native

open CFSGOutside.Corpus.M.Monster.B.Rep4371.Native

set_option compiler.extract_closed false

/-- Corpus: `CFSG.Monster.AxisCount.Native.pairTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:25. -/
def pairTab (_ : Unit := ()) : Array (Nat × Nat) :=
  ((List.range 24).flatMap fun i => ((List.range 24).filter fun j => i < j).map fun j => (i, j)).toArray

/-- Corpus: `CFSG.Monster.AxisCount.Native.octTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:36. -/
def octTab (_ : Unit := ()) : Array Nat :=
  ((List.range 4096).filter fun a => popcN 24 (wordN a) == 8).toArray

/-- Corpus: `CFSG.Monster.AxisCount.Native.evenTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:39. -/
def evenTab (_ : Unit := ()) : Array Nat :=
  ((List.range 128).filter fun m => popcN 8 m % 2 == 0).toArray

/-- Corpus: `CFSG.Monster.AxisCount.Native.suppList`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:42. -/
def suppList (w : Nat) : List Nat := (List.range 24).filter fun i => w.testBit i

/-- Corpus: `CFSG.Monster.AxisCount.Native.spreadG`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:44. -/
def spreadG (w m : Nat) : Nat := combN (fun t => 2 ^ (suppList w).getD t 0) 8 m

/-- Corpus: `CFSG.Monster.AxisCount.Native.octCodeG`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:46. -/
def octCodeG (a m : Nat) : Nat :=
  a ^^^ (if popcN 24 (spreadG (wordN a) m) / 2 % 2 == 1 then 63 else 0)

/-- Corpus: `CFSG.Monster.AxisCount.Native.thetaTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:49. -/
def thetaTab (_ : Unit) : Array Nat := (Array.range 4096).map thetaN

/-- Corpus: `CFSG.Monster.AxisCount.Native.keyAt`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:51. -/
def keyAt (th : Array Nat) (p : Nat) : Nat × Nat :=
  if p < 552 then
    let t := pairTab[p / 2]!
    (if p % 2 = 0 then 0 else 63, dualN (2 ^ t.1 ||| 2 ^ t.2))
  else if p < 49704 then
    let q := p - 552
    let a := oddCode (2 * (q / 24)) (q % 24)
    (a, th[a]! ^^^ dualN (2 ^ (q % 24)))
  else
    let q := p - 49704
    let a := octTab[q / 64]!
    let m := evenTab[q % 64]!
    let b := octCodeG a m
    (b, th[b]! ^^^ dualN (spreadG (wordN a) m))

/-- Corpus: `CFSG.Monster.AxisCount.Native.keyCode`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:66. -/
def keyCode (a d : Nat) : Nat := a % 4096 * 4096 + d % 4096

/-- Corpus: `CFSG.Monster.AxisCount.Native.TauTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:68. -/
structure TauTab where
  S : Array Int
  w : Array Nat
  pb : Array Bool

/-- Corpus: `CFSG.Monster.AxisCount.Native.mkTauTab`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:73. -/
def mkTauTab (_ : Unit) : TauTab :=
  ⟨Array.ofFn (n := 4096) fun k => octSign evenTab[k.val / 64]! evenTab[k.val % 64]!,
    Array.ofFn (n := 2048) fun t => wordN (2 * t.val),
    Array.ofFn (n := 2048) fun t => pN (2 * t.val)⟩

/-- Corpus: `CFSG.Monster.AxisCount.Native.Ctx`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:78. -/
structure Ctx where
  keys : Array (Nat × Nat)
  pos : Std.HashMap Nat Nat
  tau : TauTab
  th : Array Nat

/-- Corpus: `CFSG.Monster.AxisCount.Native.mkKeys`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:84. -/
@[noinline] def mkKeys (th : Array Nat) : Array (Nat × Nat) :=
  (Array.range 98280).map (keyAt th)

/-- Corpus: `CFSG.Monster.AxisCount.Native.mkPos`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:87. -/
@[noinline] def mkPos (keys : Array (Nat × Nat)) : Std.HashMap Nat Nat :=
  (List.range 98280).foldl (fun m p => m.insert (keyCode keys[p]!.1 keys[p]!.2) p) ∅

/-- Corpus: `CFSG.Monster.AxisCount.Native.mkCtxOf`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:90. -/
@[noinline] def mkCtxOf (th : Array Nat) (tau : TauTab) : Ctx :=
  let keys := mkKeys th
  ⟨keys, mkPos keys, tau, th⟩

/-- Corpus: `CFSG.Monster.AxisCount.Native.mkCtx`, Certificates/Data/CFSGNative/MonsterAxis/Basic.lean:94. -/
def mkCtx (_ : Unit) : Ctx := mkCtxOf (thetaTab ()) (mkTauTab ())

end CFSGOutside.Corpus.M.Monster.AxisCount.Native
