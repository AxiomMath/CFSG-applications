import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs

/-!
# Copied corpus definitions: packed `𝔽₂` arithmetic and the Dempwolff checkers of `Th`

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 by
a generator script (each docstring names the corpus declaration and
file:line). The corpus namespaces `CFSG.X` are mapped to `CFSGOutside.Corpus.Th.X`.
-/

set_option autoImplicit false


namespace CFSGOutside.Corpus.Th.KC.Loop

/-- Corpus: `CFSG.KC.Loop.strictN`, CFSG/Certificates/Kernel/Common/Loop.lean:21. -/
noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

/-- Corpus: `CFSG.KC.Loop.allBelow`, CFSG/Certificates/Kernel/Common/Loop.lean:24 (the macros
`bAnd(a, b)` and `bIf(c, t, e)` of Loop.lean:8, :14 written out). -/
noncomputable def allBelow (m hi : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => Bool.rec (motive := fun _ => Bool) false ih (
    Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64)) hi

/-- Corpus: `CFSG.KC.Loop.sumBelow`, CFSG/Certificates/Kernel/Common/Loop.lean:29 (the macro
`nIf(c, t, e)` of Loop.lean:11 written out). -/
noncomputable def sumBelow (m hi : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) hi

end CFSGOutside.Corpus.Th.KC.Loop

namespace CFSGOutside.Corpus.Th.KC.Th

/-- Corpus: `CFSG.KC.Th.andB`, CFSG/Certificates/Kernel/Th/Mat.lean:20. -/
noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

/-- Corpus: `CFSG.KC.Th.mstep`, CFSG/Certificates/Kernel/Th/Mat.lean:22. -/
noncomputable def mstep (c rm A B acc k ks : Nat) : Nat :=
  Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) c) rm)
    (Nat.mul (Nat.land (Nat.shiftRight B ks) rm) c))

end CFSGOutside.Corpus.Th.KC.Th

namespace CFSGOutside.Corpus.Th.KC.Th

/-- Corpus: `CFSG.KC.Th.mulB`, CFSG/Certificates/Kernel/Th/Big.lean:9. -/
noncomputable def mulB (c rm A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => mstep c rm A B acc k (Nat.mul k (nat_lit 256))) (nat_lit 248)

/-- Corpus: `CFSG.KC.Th.vecB`, CFSG/Certificates/Kernel/Th/Big.lean:15. -/
noncomputable def vecB (rm v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight v k) (nat_lit 1))
      (Nat.land (Nat.shiftRight M (Nat.mul k (nat_lit 256))) rm))) (nat_lit 248)

end CFSGOutside.Corpus.Th.KC.Th

namespace CFSGOutside.Corpus.Th.KC.Th.BigS

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Loop

/-- Corpus: `CFSG.KC.Th.BigS.bitsN`, CFSG/Certificates/Kernel/Th/S/BigS.lean:13. -/
noncomputable def bitsN (J o x : Nat) : Nat :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

/-- Corpus: `CFSG.KC.Th.BigS.notB`, CFSG/Certificates/Kernel/Th/S/BigS.lean:16. -/
noncomputable def notB (b : Bool) : Bool := Bool.rec true false b

/-- Corpus: `CFSG.KC.Th.BigS.rep`, CFSG/Certificates/Kernel/Th/S/BigS.lean:18. -/
noncomputable def rep (x s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc (Nat.shiftLeft x (Nat.mul s i))) n

/-- Corpus: `CFSG.KC.Th.BigS.tmask`, CFSG/Certificates/Kernel/Th/S/BigS.lean:21. -/
noncomputable def tmask (k : Nat) : Nat :=
  (fun s => (fun row => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft row (Nat.mul (nat_lit 256) r)))
        (Nat.beq (Nat.land r s) (nat_lit 0))) (nat_lit 256))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Bool.rec (motive := fun _ => Nat) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) c)) acc
        (Nat.beq (Nat.land c s) (nat_lit 0))) (nat_lit 256)))
  (Nat.shiftLeft (nat_lit 1) k)

/-- Corpus: `CFSG.KC.Th.BigS.upper`, CFSG/Certificates/Kernel/Th/S/BigS.lean:30. -/
noncomputable def upper : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ i)) (nat_lit 1))) (Nat.mul (nat_lit 256) i))) (nat_lit 248)

/-- Corpus: `CFSG.KC.Th.BigS.constsOK`, CFSG/Certificates/Kernel/Th/S/BigS.lean:36. -/
noncomputable def constsOK (c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : Nat) : Bool :=
  andB (Nat.beq c (rep (nat_lit 1) (nat_lit 256) (nat_lit 248)))
  (andB (Nat.beq rm (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1)))
  (andB (Nat.beq tm0 (tmask (nat_lit 0))) (andB (Nat.beq tm1 (tmask (nat_lit 1)))
  (andB (Nat.beq tm2 (tmask (nat_lit 2))) (andB (Nat.beq tm3 (tmask (nat_lit 3)))
  (andB (Nat.beq tm4 (tmask (nat_lit 4))) (andB (Nat.beq tm5 (tmask (nat_lit 5)))
  (andB (Nat.beq tm6 (tmask (nat_lit 6))) (andB (Nat.beq tm7 (tmask (nat_lit 7)))
  (andB (Nat.beq up upper) (andB (Nat.beq dg (rep (nat_lit 1) (nat_lit 257) (nat_lit 248)))
    (Nat.beq ONE dg))))))))))))

/-- Corpus: `CFSG.KC.Th.BigS.powB`, CFSG/Certificates/Kernel/Th/S/BigS.lean:82. -/
noncomputable def powB (c rm ONE M e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => (fun sq => Bool.rec (motive := fun _ => Nat) sq (mulB c rm sq M)
        (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (Nat.sub nb (nat_lit 1)) i)) (nat_lit 1)) (nat_lit 1)))
      (mulB c rm acc acc)) nb

/-- Corpus: `CFSG.KC.Th.BigS.regBelow`, CFSG/Certificates/Kernel/Th/S/BigS.lean:88. -/
noncomputable def regBelow (a r : Nat) : Bool := andB (Nat.blt (nat_lit 0) a) (Nat.blt a r)

/-- Corpus: `CFSG.KC.Th.BigS.insOK`, CFSG/Certificates/Kernel/Th/S/BigS.lean:90. -/
noncomputable def insOK (RB : Nat → Nat) (c rm ONE r ins : Nat) : Bool :=
  (fun k a b e => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (regBelow a r) (Nat.beq (mulB c rm (RB a) (RB r)) ONE)) (Nat.beq k (nat_lit 2)))
        (andB (regBelow a r) (andB (Nat.blt (nat_lit 0) e) (Nat.beq (RB r) (powB c rm ONE (RB a) e (nat_lit 4)))))
        (Nat.beq k (nat_lit 1)))
      (andB (regBelow a r) (andB (regBelow b r) (Nat.beq (RB r) (mulB c rm (RB a) (RB b)))))
      (Nat.beq k (nat_lit 0)))
  (Nat.land ins (nat_lit 3)) (bitsN ins (nat_lit 2) (nat_lit 11)) (bitsN ins (nat_lit 13) (nat_lit 11))
  (bitsN ins (nat_lit 24) (nat_lit 4))

/-- Corpus: `CFSG.KC.Th.BigS.runSlp`, CFSG/Certificates/Kernel/Th/S/BigS.lean:102. -/
noncomputable def runSlp (RB : Nat → Nat) (c rm ONE : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (insOK RB c rm ONE S (bitsN J (nat_lit 0) (nat_lit 28)))))
          (ih2 (Nat.shiftRight J (nat_lit 28))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

/-- Corpus: `CFSG.KC.Th.BigS.marked`, CFSG/Certificates/Kernel/Th/S/BigS.lean:110. -/
noncomputable def marked (m r : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) r))

/-- Corpus: `CFSG.KC.Th.BigS.runMarked`, CFSG/Certificates/Kernel/Th/S/BigS.lean:112. -/
noncomputable def runMarked (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => (fun r m ins => (fun k a b => strictN
            (Nat.lor (Nat.succ r) (Nat.shiftLeft
              (Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft (nat_lit 1) r))
                (Bool.rec (motive := fun _ => Bool) (marked m a) (andB (marked m a) (marked m b)) (Nat.beq k (nat_lit 0))))
              (nat_lit 11)))
            (ih2 (Nat.shiftRight J (nat_lit 28))))
          (Nat.land ins (nat_lit 3)) (bitsN ins (nat_lit 2) (nat_lit 11)) (bitsN ins (nat_lit 13) (nat_lit 11)))
          (Nat.land S (nat_lit 2047)) (Nat.shiftRight S (nat_lit 11)) (bitsN J (nat_lit 0) (nat_lit 28)))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

/-- Corpus: `CFSG.KC.Th.BigS.regAt`, CFSG/Certificates/Kernel/Th/S/BigS.lean:125. -/
noncomputable def regAt (L k : Nat) : Nat := bitsN L (Nat.mul (nat_lit 11) k) (nat_lit 11)

/-- Corpus: `CFSG.KC.Th.BigS.regsIn`, CFSG/Certificates/Kernel/Th/S/BigS.lean:127. -/
noncomputable def regsIn (L n r : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (regBelow (regAt L k) r)) n

/-- Corpus: `CFSG.KC.Th.BigS.allMarked`, CFSG/Certificates/Kernel/Th/S/BigS.lean:130. -/
noncomputable def allMarked (L n m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (marked m (regAt L k))) n

end CFSGOutside.Corpus.Th.KC.Th.BigS

namespace CFSGOutside.Corpus.Th.KC.Th.Spec

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS

/-- Corpus: `CFSG.KC.Th.Spec.pkMat`, CFSG/Certificates/Kernel/Th/Spec/Big.lean:13. -/
def pkMat (N : ℕ) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Matrix.of fun i j => if N.testBit (256 * i.val + j.val) then 1 else 0

/-- Corpus: `CFSG.KC.Th.Spec.pkVec`, CFSG/Certificates/Kernel/Th/Spec/Big.lean:659. -/
def pkVec (v : ℕ) : Fin 248 → ZMod 2 := fun j => if v.testBit j.val then 1 else 0

end CFSGOutside.Corpus.Th.KC.Th.Spec

namespace CFSGOutside.Corpus.Th.KC.ThDemp

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Loop

/-- Corpus: `CFSG.KC.ThDemp.lget`, Certificates/Data/Kernel/ThDemp/Defs.lean:12. -/
noncomputable def lget (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun h _ ih i => Nat.rec (motive := fun _ => Nat) h (fun j _ => ih j) i) l i

/-- Corpus: `CFSG.KC.ThDemp.lgetL`, Certificates/Data/Kernel/ThDemp/Defs.lean:16. -/
noncomputable def lgetL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Nat) h (fun j _ => ih j) i) l i

/-- Corpus: `CFSG.KC.ThDemp.DempData`, Certificates/Data/Kernel/ThDemp/Defs.lean:20. -/
structure DempData where
  c : Nat
  rm : Nat
  tm0 : Nat
  tm1 : Nat
  tm2 : Nat
  tm3 : Nat
  tm4 : Nat
  tm5 : Nat
  tm6 : Nat
  tm7 : Nat
  up : Nat
  dg : Nat
  ONE : Nat
  SA : Nat
  SB : Nat
  regs : List Nat
  cs1 : List Nat
  cs2 : List Nat
  r1 : Nat
  nreg : Nat
  rd : Nat
  pr : Nat
  npr : Nat
  L : Nat
  fr : List Nat
  bv : List Nat
  osz : List Nat
  pts : List (List Nat)
  tr : List (List Nat)
  tree : List (List Nat)
  ord : List (List Nat)
  res : List (List Nat)

namespace DempData

variable (D : DempData)

/-- Corpus: `CFSG.KC.ThDemp.DempData.RB`, Certificates/Data/Kernel/ThDemp/Defs.lean:58. -/
noncomputable def RB (r : Nat) : Nat := lget D.regs r

/-- Corpus: `CFSG.KC.ThDemp.DempData.S`, Certificates/Data/Kernel/ThDemp/Defs.lean:60. -/
noncomputable def S (g : Nat) : Nat := D.RB (regAt D.pr g)

/-- Corpus: `CFSG.KC.ThDemp.DempData.trR`, Certificates/Data/Kernel/ThDemp/Defs.lean:62. -/
noncomputable def trR (l i : Nat) : Nat := lget (lgetL D.tr l) i

/-- Corpus: `CFSG.KC.ThDemp.DempData.T`, Certificates/Data/Kernel/ThDemp/Defs.lean:64. -/
noncomputable def T (l i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (D.RB (D.trR l i)) D.ONE (Nat.beq (D.trR l i) (nat_lit 0))

/-- Corpus: `CFSG.KC.ThDemp.DempData.P`, Certificates/Data/Kernel/ThDemp/Defs.lean:67. -/
noncomputable def P (l i : Nat) : Nat := lget (lgetL D.pts l) i

/-- Corpus: `CFSG.KC.ThDemp.DempData.frL`, Certificates/Data/Kernel/ThDemp/Defs.lean:69. -/
noncomputable def frL (l : Nat) : Nat := lget D.fr l

/-- Corpus: `CFSG.KC.ThDemp.DempData.oszL`, Certificates/Data/Kernel/ThDemp/Defs.lean:71. -/
noncomputable def oszL (l : Nat) : Nat := lget D.osz l

/-- Corpus: `CFSG.KC.ThDemp.DempData.bvL`, Certificates/Data/Kernel/ThDemp/Defs.lean:73. -/
noncomputable def bvL (l : Nat) : Nat := lget D.bv l

/-- Corpus: `CFSG.KC.ThDemp.DempData.mul`, Certificates/Data/Kernel/ThDemp/Defs.lean:75. -/
noncomputable def mul (A B : Nat) : Nat := mulB D.c D.rm A B

/-- Corpus: `CFSG.KC.ThDemp.DempData.stepY`, Certificates/Data/Kernel/ThDemp/Defs.lean:77. -/
noncomputable def stepY (k y X : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (D.mul (D.T k y) X) X (Nat.beq y (nat_lit 0))

/-- Corpus: `CFSG.KC.ThDemp.DempData.sift`, Certificates/Data/Kernel/ThDemp/Defs.lean:80. -/
noncomputable def sift (l e : Nat) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
      (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc)
    (Nat.sub (Nat.sub D.L l) (nat_lit 1))

end DempData

open DempData

/-- Corpus: `CFSG.KC.ThDemp.slpChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:90. -/
noncomputable def slpChk (D : DempData) : Bool :=
  andB (constsOK D.c D.rm D.tm0 D.tm1 D.tm2 D.tm3 D.tm4 D.tm5 D.tm6 D.tm7 D.up D.dg D.ONE)
  (andB (Nat.beq (D.RB 1) D.SA) (andB (Nat.beq (D.RB 2) D.SB)
  (andB (Nat.beq (runSlp D.RB D.c D.rm D.ONE D.cs1 (nat_lit 3)) D.r1)
    (Nat.beq (runSlp D.RB D.c D.rm D.ONE D.cs2 D.r1) D.nreg))))

/-- Corpus: `CFSG.KC.ThDemp.DempData.marks`, Certificates/Data/Kernel/ThDemp/Defs.lean:96. -/
noncomputable def DempData.marks (D : DempData) : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 1) (regAt D.rd 0)) (Nat.shiftLeft (nat_lit 1) (regAt D.rd 1))

/-- Corpus: `CFSG.KC.ThDemp.markChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:99. -/
noncomputable def markChk (D : DempData) : Bool :=
  andB (Nat.blt D.nreg (Nat.shiftLeft (nat_lit 1) (nat_lit 11)))
    (andB (regsIn D.rd (nat_lit 2) D.r1)
    (andB (regsIn D.pr D.npr D.nreg)
    (andB (Nat.ble (nat_lit 2) D.npr) (andB (Nat.ble D.npr (nat_lit 64))
    (andB (Nat.beq (regAt D.pr 0) (regAt D.rd 0)) (andB (Nat.beq (regAt D.pr 1) (regAt D.rd 1))
      (allMarked D.pr D.npr (Nat.shiftRight
        (runMarked D.cs2 (Nat.add D.r1 (Nat.mul (nat_lit 2048) D.marks))) (nat_lit 11)))))))))

/-- Corpus: `CFSG.KC.ThDemp.frChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:108. -/
noncomputable def frChk (D : DempData) : Bool :=
  andB (Nat.beq (D.frL 0) (nat_lit 0)) (andB (Nat.beq (D.frL D.L) D.npr)
    (allBelow D.L (nat_lit 1) (fun l => Nat.ble (D.frL l) (D.frL (Nat.succ l)))))

/-- Corpus: `CFSG.KC.ThDemp.levelChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:112. -/
noncomputable def levelChk (D : DempData) (l : Nat) : Bool :=
  (fun n => andB (Nat.blt (nat_lit 0) n) (andB (Nat.blt n (nat_lit 256))
  (andB (Nat.blt (D.bvL l) (Nat.shiftLeft (nat_lit 1) (nat_lit 248)))
  (andB (Nat.beq (D.P l 0) (D.bvL l)) (andB (Nat.beq (D.trR l 0) (nat_lit 0))
  (andB (allBelow n (nat_lit 4) (fun i => Bool.rec (motive := fun _ => Bool) true
      ((fun e => (fun par g => andB (Nat.blt par i) (andB (Nat.ble (D.frL l) g) (andB (Nat.blt g D.npr)
          (andB (Nat.blt (nat_lit 0) (D.trR l i)) (andB (Nat.blt (D.trR l i) D.nreg)
          (andB (Nat.beq (D.RB (D.trR l i)) (D.mul (D.T l par) (D.S g)))
            (Nat.beq (D.P l i) (vecB D.rm (D.P l par) (D.S g)))))))))
          (Nat.land e (nat_lit 8191)) (Nat.shiftRight e (nat_lit 13)))
        (lget (lgetL D.tree l) i))
      (Nat.blt (nat_lit 0) i)))
  (andB (allBelow n (nat_lit 4) (fun i => Nat.blt (lget (lgetL D.ord l) i) n))
  (andB (allBelow (Nat.sub n (nat_lit 1)) (nat_lit 4) (fun i =>
      Nat.blt (D.P l (lget (lgetL D.ord l) i)) (D.P l (lget (lgetL D.ord l) (Nat.succ i)))))
    (allBelow D.npr (nat_lit 1) (fun g => Bool.rec (motive := fun _ => Bool) true
      (Nat.beq (vecB D.rm (D.bvL l) (D.S g)) (D.bvL l)) (Nat.ble (D.frL (Nat.succ l)) g)))))))))))
  (D.oszL l)

/-- Corpus: `CFSG.KC.ThDemp.resChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:131. -/
noncomputable def resChk (D : DempData) (l : Nat) : Bool :=
  (fun n m => allBelow (Nat.mul n m) (Nat.add (Nat.shiftRight (Nat.mul n m) (nat_lit 6)) (nat_lit 1))
    (fun p => (fun i g e => (fun z => andB (Nat.blt z n)
        (andB (allBelow (Nat.sub (Nat.sub D.L l) (nat_lit 1)) (nat_lit 1) (fun q =>
            Nat.blt (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8))
              (D.oszL (Nat.add (Nat.add l (nat_lit 1)) q))))
          (Nat.beq (D.mul (D.T l i) (D.S g)) (D.sift l e (D.T l z)))))
        (Nat.land e (nat_lit 255)))
      (Nat.div p m) (Nat.add (D.frL l) (Nat.mod p m)) (lget (lgetL D.res l) p)))
  (D.oszL l) (Nat.sub D.npr (D.frL l))

/-- Corpus: `CFSG.KC.ThDemp.shapeChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:142. -/
noncomputable def shapeChk (D : DempData) : Bool :=
  andB (markChk D) (andB (frChk D) (andB (Nat.beq D.L (nat_lit 6))
  (andB (Nat.beq (D.oszL 0) (nat_lit 31)) (andB (Nat.beq (D.oszL 1) (nat_lit 30))
  (andB (Nat.beq (D.oszL 2) (nat_lit 28)) (andB (Nat.beq (D.oszL 3) (nat_lit 24))
  (andB (Nat.beq (D.oszL 4) (nat_lit 16)) (Nat.beq (D.oszL 5) (nat_lit 32)))))))))

/-- Corpus: `CFSG.KC.ThDemp.levelsChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:148. -/
noncomputable def levelsChk (D : DempData) : Bool :=
  andB (levelChk D 0) (andB (levelChk D 1) (andB (levelChk D 2) (andB (levelChk D 3)
    (andB (levelChk D 4) (levelChk D 5)))))

/-- Corpus: `CFSG.KC.ThDemp.dempChk`, Certificates/Data/Kernel/ThDemp/Defs.lean:152. -/
noncomputable def dempChk (D : DempData) : Bool :=
  andB (slpChk D) (andB (shapeChk D) (andB (levelsChk D)
  (andB (resChk D 0) (andB (resChk D 1) (andB (resChk D 2) (andB (resChk D 3)
    (andB (resChk D 4) (resChk D 5))))))))

end CFSGOutside.Corpus.Th.KC.ThDemp

namespace CFSGOutside.Corpus.Th.KC.ThDemp

open CFSGOutside.Corpus.Th.KC.Th CFSGOutside.Corpus.Th.KC.Th.BigS CFSGOutside.Corpus.Th.KC.Loop

/-- Corpus: `CFSG.KC.ThDemp.strictB`, Certificates/Data/Kernel/ThDemp/Orb.lean:11. -/
noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

/-- Corpus: `CFSG.KC.ThDemp.strictL`, Certificates/Data/Kernel/ThDemp/Orb.lean:14. -/
noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

/-- Corpus: `CFSG.KC.ThDemp.m1280`, Certificates/Data/Kernel/ThDemp/Orb.lean:17. -/
noncomputable def m1280 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1280)) (nat_lit 1)

/-- Corpus: `CFSG.KC.ThDemp.ptAt`, Certificates/Data/Kernel/ThDemp/Orb.lean:19. -/
noncomputable def ptAt (S m : Nat) : Nat := Nat.land (Nat.shiftRight S (Nat.mul (nat_lit 1280) m)) m1280

/-- Corpus: `CFSG.KC.ThDemp.repD`, Certificates/Data/Kernel/ThDemp/Orb.lean:21. -/
noncomputable def repD (x s d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun k acc => Nat.lor acc (Nat.shiftLeft acc (Nat.mul s (Nat.shiftLeft (nat_lit 1) k)))) d

/-- Corpus: `CFSG.KC.ThDemp.repN`, Certificates/Data/Kernel/ThDemp/Orb.lean:25. -/
noncomputable def repN (x s d n : Nat) : Nat :=
  Nat.land (repD x s d) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul s n)) (nat_lit 1))

/-- Corpus: `CFSG.KC.ThDemp.m63`, Certificates/Data/Kernel/ThDemp/Orb.lean:28. -/
noncomputable def m63 : Nat := nat_lit 9223372036854775807

/-- Corpus: `CFSG.KC.ThDemp.m64`, Certificates/Data/Kernel/ThDemp/Orb.lean:30. -/
noncomputable def m64 : Nat := nat_lit 18446744073709551615

/-- Corpus: `CFSG.KC.ThDemp.and5`, Certificates/Data/Kernel/ThDemp/Orb.lean:32. -/
noncomputable def and5 (v : Nat) : Nat :=
  Nat.land (Nat.land (Nat.land (Nat.land v (Nat.shiftRight v (nat_lit 1))) (Nat.shiftRight v (nat_lit 2)))
    (Nat.shiftRight v (nat_lit 3))) (Nat.shiftRight v (nat_lit 4))

/-- Corpus: `CFSG.KC.ThDemp.subX`, Certificates/Data/Kernel/ThDemp/Orb.lean:36. -/
noncomputable def subX (bs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun base => and5 base)
    (fun b _ ih base => Nat.xor (ih base) (ih (Nat.xor base b))) bs

/-- Corpus: `CFSG.KC.ThDemp.fold64`, Certificates/Data/Kernel/ThDemp/Orb.lean:40. -/
noncomputable def fold64 (m K : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.xor K (Nat.shiftRight K (nat_lit 64)))
    (Nat.xor (Nat.shiftRight K (nat_lit 128)) (Nat.shiftRight K (nat_lit 192)))) m

/-- Corpus: `CFSG.KC.ThDemp.rowsOf`, Certificates/Data/Kernel/ThDemp/Orb.lean:44. -/
noncomputable def rowsOf (rm P : Nat) : List Nat :=
  [Nat.land P rm, Nat.land (Nat.shiftRight P (nat_lit 256)) rm,
    Nat.land (Nat.shiftRight P (nat_lit 512)) rm, Nat.land (Nat.shiftRight P (nat_lit 768)) rm,
    Nat.land (Nat.shiftRight P (nat_lit 1024)) rm]

/-- Corpus: `CFSG.KC.ThDemp.keyL`, Certificates/Data/Kernel/ThDemp/Orb.lean:49. -/
noncomputable def keyL (rm P : Nat) : Nat := fold64 m63 (subX (rowsOf rm P) (nat_lit 0))

/-- Corpus: `CFSG.KC.ThDemp.combsL`, Certificates/Data/Kernel/ThDemp/Orb.lean:51. -/
noncomputable def combsL (bs : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun base => [base])
    (fun b _ ih base => List.append (ih base) (ih (Nat.xor base b))) bs

/-- Corpus: `CFSG.KC.ThDemp.notMemB`, Certificates/Data/Kernel/ThDemp/Orb.lean:55. -/
noncomputable def notMemB (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (BigS.notB (Nat.beq x y)) ih) l

/-- Corpus: `CFSG.KC.ThDemp.nodupB`, Certificates/Data/Kernel/ThDemp/Orb.lean:58. -/
noncomputable def nodupB (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y t ih => andB (notMemB y t) ih) l

/-- Corpus: `CFSG.KC.ThDemp.keyB`, Certificates/Data/Kernel/ThDemp/Orb.lean:61. -/
noncomputable def keyB (L248 L63 Z : Nat) : Nat :=
  strictN (Nat.land Z L248) fun b0 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 256)) L248) fun b1 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 512)) L248) fun b2 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 768)) L248) fun b3 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 1024)) L248) fun b4 =>
  fold64 L63 (subX [b0, b1, b2, b3, b4] (nat_lit 0))

/-- Corpus: `CFSG.KC.ThDemp.packD`, Certificates/Data/Kernel/ThDemp/Orb.lean:69. -/
noncomputable def packD (d : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun Z => Nat.land Z m64)
    (fun k ih Z => (fun h => Nat.lor (ih (Nat.land Z (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1280) h)) (nat_lit 1))))
      (Nat.shiftLeft (ih (Nat.shiftRight Z (Nat.mul (nat_lit 1280) h))) (Nat.mul (nat_lit 64) h)))
      (Nat.shiftLeft (nat_lit 1) k)) d

/-- Corpus: `CFSG.KC.ThDemp.stackN`, Certificates/Data/Kernel/ThDemp/Orb.lean:75. -/
noncomputable def stackN (s m : Nat) (F : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (F k) (Nat.mul s k))) m

/-- Corpus: `CFSG.KC.ThDemp.keyAt`, Certificates/Data/Kernel/ThDemp/Orb.lean:79. -/
noncomputable def keyAt (K j : Nat) : Nat := Nat.land (Nat.shiftRight K (Nat.mul (nat_lit 64) j)) m64

/-- Corpus: `CFSG.KC.ThDemp.bitB`, Certificates/Data/Kernel/ThDemp/Orb.lean:81. -/
noncomputable def bitB (F p : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight F p) (nat_lit 1)) (nat_lit 1)

/-- Corpus: `CFSG.KC.ThDemp.jz`, Certificates/Data/Kernel/ThDemp/Orb.lean:83. -/
noncomputable def jz (H C KY k : Nat) : Nat :=
  Nat.land (Nat.sub (Nat.lor (Nat.xor KY (Nat.mul k C)) H) C) H

/-- Corpus: `CFSG.KC.ThDemp.combRow`, Certificates/Data/Kernel/ThDemp/Orb.lean:86. -/
noncomputable def combRow (rm P G k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.mul (bitsN G (Nat.add (Nat.mul (nat_lit 5) k) j) (nat_lit 1))
      (Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 256) j)) rm))) (nat_lit 5)

/-- Corpus: `CFSG.KC.ThDemp.combChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:91. -/
noncomputable def combChk (rm P Q G : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (Nat.beq (Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 256) k)) rm) (combRow rm Q G k)) ih)
    (nat_lit 5)

/-- Corpus: `CFSG.KC.ThDemp.OrbData`, Certificates/Data/Kernel/ThDemp/Orb.lean:96. -/
structure OrbData where
  Ti : List (List Nat)
  words : List (List Nat)
  sb : List Nat
  grp : List (List (List (List Nat)))
  ky : List Nat
  par : List Nat
  edges : List Nat
  ord : List Nat
  fx5 : List Nat
  x5 : Nat
  x31 : Nat
  yb : Nat
  dm : Nat
  f5 : Nat
  v5 : Nat
  qm : Nat
  gs5 : Nat
  gs31 : Nat
  Ga : Nat
  Gb : Nat
  gd0 : Nat
  gd1 : Nat

/-- Corpus: `CFSG.KC.ThDemp.lgetLL`, Certificates/Data/Kernel/ThDemp/Orb.lean:120. -/
noncomputable def lgetLL (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List (List Nat)) h (fun j _ => ih j) i) l i

/-- Corpus: `CFSG.KC.ThDemp.lgetL3`, Certificates/Data/Kernel/ThDemp/Orb.lean:124. -/
noncomputable def lgetL3 (l : List (List (List (List Nat)))) (i : Nat) : List (List (List Nat)) :=
  List.rec (motive := fun _ => Nat → List (List (List Nat))) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List (List (List Nat))) h (fun j _ => ih j) i) l i

namespace OrbData

variable (O : OrbData)

/-- Corpus: `CFSG.KC.ThDemp.OrbData.TI`, Certificates/Data/Kernel/ThDemp/Orb.lean:132. -/
noncomputable def TI (l i : Nat) : Nat := lget (lgetL O.Ti l) i

/-- Corpus: `CFSG.KC.ThDemp.OrbData.grpOf`, Certificates/Data/Kernel/ThDemp/Orb.lean:134. -/
noncomputable def grpOf (i b : Nat) : List (List Nat) := lgetLL (lgetL3 O.grp i) b

end OrbData

open OrbData DempData

variable (D : DempData) (O : OrbData)

/-- Corpus: `CFSG.KC.ThDemp.cR`, Certificates/Data/Kernel/ThDemp/Orb.lean:142. -/
noncomputable def cR (n : Nat) : Nat := rep (nat_lit 1) (nat_lit 256) n

/-- Corpus: `CFSG.KC.ThDemp.U0`, Certificates/Data/Kernel/ThDemp/Orb.lean:144. -/
noncomputable def U0 : Nat :=
  stackN (nat_lit 256) (nat_lit 5) (fun k => D.bvL k)

/-- Corpus: `CFSG.KC.ThDemp.wordR`, Certificates/Data/Kernel/ThDemp/Orb.lean:147. -/
noncomputable def wordR (cn X : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun r _ ih S => strictN (mulB cn D.rm S (D.RB r)) ih) w X

/-- Corpus: `CFSG.KC.ThDemp.pt`, Certificates/Data/Kernel/ThDemp/Orb.lean:151. -/
noncomputable def pt (i : Nat) : Nat := wordR D (cR (nat_lit 5)) (U0 D) (lgetL O.words i)

/-- Corpus: `CFSG.KC.ThDemp.chainEl`, Certificates/Data/Kernel/ThDemp/Orb.lean:153. -/
noncomputable def chainEl (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) D.ONE
    (fun q acc => strictN (D.stepY (Nat.sub (nat_lit 5) q) (bitsN e (Nat.mul (nat_lit 8) (Nat.sub (nat_lit 5) q)) (nat_lit 8)) D.ONE)
      (fun t => D.mul acc t)) (nat_lit 6)

/-- Corpus: `CFSG.KC.ThDemp.invChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:158. -/
noncomputable def invChk : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun l ih => andB (allBelow (D.oszL l) (nat_lit 1) (fun i =>
      Nat.beq (D.mul (D.T l i) (O.TI l i)) D.ONE)) ih) (nat_lit 3)

/-- Corpus: `CFSG.KC.ThDemp.xS4`, Certificates/Data/Kernel/ThDemp/Orb.lean:163. -/
noncomputable def xS4 (P : Nat) : Nat :=
  strictN (stackN (nat_lit 1280) (nat_lit 32) (fun y5 => mulB (cR (nat_lit 5)) D.rm P (D.T 5 y5))) fun S5 =>
    stackN (nat_lit 40960) (nat_lit 16) (fun y4 => mulB (cR (nat_lit 160)) D.rm S5 (D.T 4 y4))

/-- Corpus: `CFSG.KC.ThDemp.xBat`, Certificates/Data/Kernel/ThDemp/Orb.lean:167. -/
noncomputable def xBat (P : Nat) : List Nat :=
  strictL (cR (nat_lit 2560)) fun c2560 => strictL (xS4 D P) fun S4 =>
    (List.range (nat_lit 24)).map (fun y3 => mulB c2560 D.rm S4 (D.T 3 y3))

/-- Corpus: `CFSG.KC.ThDemp.yBat`, Certificates/Data/Kernel/ThDemp/Orb.lean:171. -/
noncomputable def yBat (P : Nat) : List Nat :=
  strictL (cR (nat_lit 5)) fun c5 => strictL (cR (nat_lit 155)) fun c155 =>
  strictL (cR (nat_lit 4650)) fun c4650 =>
    strictL (stackN (nat_lit 1280) (nat_lit 31) (fun y0 => mulB c5 D.rm P (O.TI 0 y0))) fun S0 =>
    strictL (stackN (nat_lit 39680) (nat_lit 30) (fun y1 => mulB c155 D.rm S0 (O.TI 1 y1))) fun S1 =>
    (List.range (nat_lit 28)).map (fun y2 => mulB c4650 D.rm S1 (O.TI 2 y2))

/-- Corpus: `CFSG.KC.ThDemp.yKeys`, Certificates/Data/Kernel/ThDemp/Orb.lean:178. -/
noncomputable def yKeys (W : List Nat) : Nat :=
  strictN (repN D.rm (nat_lit 1280) (nat_lit 10) (nat_lit 930)) fun L248 =>
  strictN (repN m63 (nat_lit 1280) (nat_lit 10) (nat_lit 930)) fun L63 =>
  stackN (nat_lit 59520) (nat_lit 28) (fun y2 => packD (nat_lit 10) (keyB L248 L63 (lget W y2)))

/-- Corpus: `CFSG.KC.ThDemp.kyChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:183. -/
noncomputable def kyChk (i : Nat) : Bool := Nat.beq (yKeys D (yBat D O (pt D O i))) (lget O.ky i)

/-- Corpus: `CFSG.KC.ThDemp.xKeys`, Certificates/Data/Kernel/ThDemp/Orb.lean:185. -/
noncomputable def xKeys (P y3 : Nat) : Nat :=
  packD (nat_lit 9) (keyB (repN D.rm (nat_lit 1280) (nat_lit 9) (nat_lit 512)) (repN m63 (nat_lit 1280) (nat_lit 9) (nat_lit 512))
    (mulB (cR (nat_lit 2560)) D.rm (xS4 D P) (D.T 3 y3)))

/-- Corpus: `CFSG.KC.ThDemp.maskOf`, Certificates/Data/Kernel/ThDemp/Orb.lean:189. -/
noncomputable def maskOf (es : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 64) (Nat.shiftRight e (nat_lit 25))) (nat_lit 63)))) es

/-- Corpus: `CFSG.KC.ThDemp.flagsOf`, Certificates/Data/Kernel/ThDemp/Orb.lean:193. -/
noncomputable def flagsOf (gs : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.mod (lget g 0) (nat_lit 512)))) gs

/-- Corpus: `CFSG.KC.ThDemp.batchChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:197. -/
noncomputable def batchChk (i y3 : Nat) : Bool :=
  strictB (lget O.ky i) fun KY => strictB (xKeys D (pt D O i) y3) fun KX =>
  strictB (repN (Nat.shiftLeft (nat_lit 1) (nat_lit 63)) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun H =>
  strictB (repN (nat_lit 1) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun C =>
  (fun gs => strictB (flagsOf gs) fun F =>
    andB (allBelow (nat_lit 512) (nat_lit 8) (fun p =>
      Bool.rec (motive := fun _ => Bool) (Nat.beq (jz H C KY (keyAt KX p)) H) true (bitB F p)))
    (List.rec (motive := fun _ => Bool) true (fun g _ ih => andB
      (andB (Nat.beq (Nat.div (lget g 0) (nat_lit 512)) y3)
        (Nat.beq (Nat.xor (jz H C KY (keyAt KX (Nat.mod (lget g 0) (nat_lit 512)))) H) (maskOf g.tail))) ih) gs))
  (O.grpOf i y3)

/-- Corpus: `CFSG.KC.ThDemp.crossChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:209. -/
noncomputable def crossChk (i j y3 : Nat) : Bool :=
  strictB (lget O.ky j) fun KY => strictB (xKeys D (pt D O i) y3) fun KX =>
  strictB (repN (Nat.shiftLeft (nat_lit 1) (nat_lit 63)) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun H =>
  strictB (repN (nat_lit 1) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun C =>
    allBelow (nat_lit 512) (nat_lit 8) (fun p => Nat.beq (jz H C KY (keyAt KX p)) H)

/-- Corpus: `CFSG.KC.ThDemp.xPt`, Certificates/Data/Kernel/ThDemp/Orb.lean:215. -/
noncomputable def xPt (Z : List Nat) (x : Nat) : Nat :=
  ptAt (lget Z (Nat.div x (nat_lit 512))) (Nat.mod x (nat_lit 512))

/-- Corpus: `CFSG.KC.ThDemp.yPt`, Certificates/Data/Kernel/ThDemp/Orb.lean:218. -/
noncomputable def yPt (W : List Nat) (y : Nat) : Nat :=
  ptAt (lget W (Nat.div y (nat_lit 930))) (Nat.mod y (nat_lit 930))

/-- Corpus: `CFSG.KC.ThDemp.pairOK`, Certificates/Data/Kernel/ThDemp/Orb.lean:221. -/
noncomputable def pairOK (Z W : List Nat) (x e : Nat) : Bool :=
  (fun y G => andB (Nat.blt x (nat_lit 12288)) (andB (Nat.blt y (nat_lit 26040))
      (combChk D.rm (xPt Z x) (yPt W y) G)))
    (Nat.shiftRight e (nat_lit 25)) (bitsN e (nat_lit 0) (nat_lit 25))

/-- Corpus: `CFSG.KC.ThDemp.groupRun`, Certificates/Data/Kernel/ThDemp/Orb.lean:226. -/
noncomputable def groupRun (Z W : List Nat) (x : Nat) (es : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun e _ ih prev => (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih c)
      (andB (Nat.blt prev c) (pairOK D Z W x e)))
      (Nat.succ (Nat.add (Nat.shiftRight e (nat_lit 25)) (Nat.mul (nat_lit 32768) x)))) es

/-- Corpus: `CFSG.KC.ThDemp.groupsRun`, Certificates/Data/Kernel/ThDemp/Orb.lean:232. -/
noncomputable def groupsRun (Z W : List Nat) (gs : List (List Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun g _ ih prev => (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih r) (Nat.blt (nat_lit 0) r))
      (groupRun D Z W (lget g 0) g.tail prev)) gs

/-- Corpus: `CFSG.KC.ThDemp.batchesRun`, Certificates/Data/Kernel/ThDemp/Orb.lean:237. -/
noncomputable def batchesRun (Z W : List Nat) (bs : List (List (List Nat))) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun gs _ ih prev => (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih r) (Nat.blt (nat_lit 0) r))
      (groupsRun D Z W gs prev)) bs

/-- Corpus: `CFSG.KC.ThDemp.pairsLen`, Certificates/Data/Kernel/ThDemp/Orb.lean:242. -/
noncomputable def pairsLen (bs : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun gs _ ih => Nat.add (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun g _ ih2 => Nat.add g.tail.length ih2) gs) ih) bs

/-- Corpus: `CFSG.KC.ThDemp.lowChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:247. -/
noncomputable def lowChk (i : Nat) : Bool :=
  (fun bs => andB (Nat.beq (pairsLen bs) (lget O.sb i))
    (strictB (pt D O i) fun P => Nat.blt (nat_lit 0) (batchesRun D (xBat D P) (yBat D O P) bs (nat_lit 0))))
  (lgetL3 O.grp i)

/-- Corpus: `CFSG.KC.ThDemp.gen`, Certificates/Data/Kernel/ThDemp/Orb.lean:252. -/
noncomputable def gen (g : Nat) : Nat := D.RB (regAt D.rd g)

/-- Corpus: `CFSG.KC.ThDemp.qBuild`, Certificates/Data/Kernel/ThDemp/Orb.lean:254. -/
noncomputable def qBuild : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (pt D O (nat_lit 9))
    (fun m S => strictN S fun S' => (fun e => Nat.lor S' (Nat.shiftLeft
        (mulB (cR (nat_lit 5)) D.rm (ptAt S' (Nat.land e (nat_lit 255))) (gen D (Nat.shiftRight e (nat_lit 8))))
        (Nat.mul (nat_lit 1280) (Nat.succ m)))) (lget O.par (Nat.succ m)))

/-- Corpus: `CFSG.KC.ThDemp.qStack`, Certificates/Data/Kernel/ThDemp/Orb.lean:260. -/
noncomputable def qStack : Nat := qBuild D O (nat_lit 247)

/-- Corpus: `CFSG.KC.ThDemp.keys248`, Certificates/Data/Kernel/ThDemp/Orb.lean:262. -/
noncomputable def keys248 (S : Nat) : Nat :=
  packD (nat_lit 8) (keyB (repN D.rm (nat_lit 1280) (nat_lit 8) (nat_lit 248))
    (repN m63 (nat_lit 1280) (nat_lit 8) (nat_lit 248)) S)

/-- Corpus: `CFSG.KC.ThDemp.bitsOf`, Certificates/Data/Kernel/ThDemp/Orb.lean:266. -/
noncomputable def bitsOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun k _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) k)) l

/-- Corpus: `CFSG.KC.ThDemp.orbChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:269. -/
noncomputable def orbChk : Bool :=
  andB (Nat.beq O.fx5.length (nat_lit 3))
  (andB (Nat.beq O.par.length (nat_lit 248)) (andB (Nat.beq O.ord.length (nat_lit 248))
  (andB (Nat.beq O.edges.length (nat_lit 496))
  (andB (allBelow (nat_lit 247) (nat_lit 4) (fun k => (fun e => andB (Nat.blt (Nat.land e (nat_lit 255)) (Nat.succ k))
      (Nat.blt (Nat.shiftRight e (nat_lit 8)) (nat_lit 2))) (lget O.par (Nat.succ k))))
  (strictB (qStack D O) fun S => strictB (keys248 D S) fun K =>
    andB (allBelow (nat_lit 248) (nat_lit 4) (fun t => Nat.blt (lget O.ord t) (nat_lit 248)))
    (andB (allBelow (nat_lit 247) (nat_lit 4) (fun t =>
      Nat.blt (keyAt K (lget O.ord t)) (keyAt K (lget O.ord (Nat.succ t)))))
    (andB (allBelow (nat_lit 496) (nat_lit 8) (fun t => (fun e => andB (Nat.blt (Nat.land e (nat_lit 255)) (nat_lit 248))
        (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (ptAt S (Nat.shiftRight t (nat_lit 1))) (gen D (Nat.land t (nat_lit 1))))
          (ptAt S (Nat.land e (nat_lit 255))) (Nat.shiftRight e (nat_lit 8)))) (lget O.edges t)))
    (strictB (keys248 D (mulB (cR (nat_lit 1240)) D.rm S (chainEl D O.x5))) fun K' =>
      strictB (bitsOf O.fx5) fun F => allBelow (nat_lit 248) (nat_lit 4) (fun k =>
        Bool.rec (motive := fun _ => Bool) (BigS.notB (Nat.beq (keyAt K k) (keyAt K' k))) true (bitB F k))))))))))

/-- Corpus: `CFSG.KC.ThDemp.uVec`, Certificates/Data/Kernel/ThDemp/Orb.lean:286. -/
noncomputable def uVec (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (bitsN c k (nat_lit 1)) (D.bvL k))) (nat_lit 5)

/-- Corpus: `CFSG.KC.ThDemp.uAll`, Certificates/Data/Kernel/ThDemp/Orb.lean:290. -/
noncomputable def uAll : Nat := stackN (nat_lit 256) (nat_lit 32) (uVec D)

/-- Corpus: `CFSG.KC.ThDemp.pow5`, Certificates/Data/Kernel/ThDemp/Orb.lean:292. -/
noncomputable def pow5 (M e : Nat) : Nat := powB D.c D.rm D.ONE M e (nat_lit 5)

/-- Corpus: `CFSG.KC.ThDemp.ordChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:294. -/
noncomputable def ordChk (X p : Nat) : Bool :=
  andB (Nat.beq (pow5 D X p) D.ONE) (BigS.notB (Nat.beq X D.ONE))

/-- Corpus: `CFSG.KC.ThDemp.cent5`, Certificates/Data/Kernel/ThDemp/Orb.lean:297. -/
noncomputable def cent5 (X : Nat) : Nat :=
  sumBelow (nat_lit 32) (nat_lit 1) (fun y => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (D.mul (D.T 5 y) X) (D.mul X (D.T 5 y))))

/-- Corpus: `CFSG.KC.ThDemp.rowAt`, Certificates/Data/Kernel/ThDemp/Orb.lean:301. -/
noncomputable def rowAt (M c : Nat) : Nat := Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 256) c)) D.rm

/-- Corpus: `CFSG.KC.ThDemp.eqRows`, Certificates/Data/Kernel/ThDemp/Orb.lean:303. -/
noncomputable def eqRows (A B : Nat) : Nat :=
  sumBelow (nat_lit 32) (nat_lit 1) (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (rowAt D A c) (rowAt D B c)))

/-- Corpus: `CFSG.KC.ThDemp.cycPt`, Certificates/Data/Kernel/ThDemp/Orb.lean:307. -/
noncomputable def cycPt (X u f : Nat) : Nat :=
  strictN (vecB D.rm u X) fun u1 => strictN (vecB D.rm u1 X) fun u2 => strictN (vecB D.rm u2 X) fun u3 =>
    Nat.lor (Nat.lor (Nat.lor (Nat.lor u (Nat.shiftLeft u1 (nat_lit 256))) (Nat.shiftLeft u2 (nat_lit 512)))
      (Nat.shiftLeft u3 (nat_lit 768))) (Nat.shiftLeft f (nat_lit 1024))

/-- Corpus: `CFSG.KC.ThDemp.powStack`, Certificates/Data/Kernel/ThDemp/Orb.lean:312. -/
noncomputable def powStack (Y X : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun m S => strictN S fun S' =>
      Nat.lor S' (Nat.shiftLeft (mulB (cR (nat_lit 5)) D.rm (ptAt S' m) Y) (Nat.mul (nat_lit 1280) (Nat.succ m))))

/-- Corpus: `CFSG.KC.ThDemp.qRows`, Certificates/Data/Kernel/ThDemp/Orb.lean:317. -/
noncomputable def qRows (q k L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ptAt L (Nat.mod (Nat.mul (nat_lit 5) k) (nat_lit 31)))
    (fun j acc => Nat.xor acc (Nat.mul (bitsN q j (nat_lit 1)) (ptAt L (Nat.mod (Nat.mul j k) (nat_lit 31)))))
    (nat_lit 5)

/-- Corpus: `CFSG.KC.ThDemp.qCount`, Certificates/Data/Kernel/ThDemp/Orb.lean:322. -/
noncomputable def qCount (q L : Nat) : Nat :=
  sumBelow (nat_lit 30) (nat_lit 1) (fun k => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (qRows q (Nat.succ k) L) (nat_lit 0)))

/-- Corpus: `CFSG.KC.ThDemp.wordM`, Certificates/Data/Kernel/ThDemp/Orb.lean:326. -/
noncomputable def wordM (w : List Nat) : Nat := wordR D D.c D.ONE w

/-- Corpus: `CFSG.KC.ThDemp.wordsChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:328. -/
noncomputable def wordsChk : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true (fun r _ ih2 => andB (regBelow r D.nreg) ih2) w) ih)
    O.words

/-- Corpus: `CFSG.KC.ThDemp.codeChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:333. -/
noncomputable def codeChk (e : Nat) : Bool :=
  allBelow (nat_lit 6) (nat_lit 1) (fun l => Nat.blt (bitsN e (Nat.mul (nat_lit 8) l) (nat_lit 8)) (D.oszL l))

/-- Corpus: `CFSG.KC.ThDemp.codesChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:336. -/
noncomputable def codesChk : Bool :=
  andB (codeChk D O.x5) (andB (codeChk D O.x31) (andB (codeChk D O.yb) (codeChk D O.dm)))

/-- Corpus: `CFSG.KC.ThDemp.eltChk1`, Certificates/Data/Kernel/ThDemp/Orb.lean:339. -/
noncomputable def eltChk1 : Bool :=
  andB (wordsChk D O)
  ((fun X5 X31 YB => (fun U => andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm U (gen D 0)) U O.gd0)
    (andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm U (gen D 1)) U O.gd1)
    (andB (nodupB (combsL (rowsOf D.rm U) (nat_lit 0)))
    (andB (ordChk D X5 (nat_lit 5)) (andB (ordChk D X31 (nat_lit 31)) (andB (ordChk D YB (nat_lit 31))
    (andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (pt D O 7) X31) (pt D O 7) O.Ga)
      (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (pt D O 8) YB) (pt D O 8) O.Gb))))))))
    (U0 D))
  (chainEl D O.x5) (chainEl D O.x31) (chainEl D O.yb))

/-- Corpus: `CFSG.KC.ThDemp.centChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:350. -/
noncomputable def centChk : Bool :=
  (fun X5 X31 => andB (Nat.ble (cent5 D X5) (nat_lit 2)) (andB (Nat.ble (cent5 D X31) (nat_lit 1))
    (strictB (uAll D) fun A => strictB (mulB (cR (nat_lit 32)) D.rm A X5) fun A1 =>
      strictB (mulB (cR (nat_lit 32)) D.rm A1 X5) fun A2 => strictB (mulB (cR (nat_lit 32)) D.rm A2 X5) fun A3 =>
      strictB (mulB (cR (nat_lit 32)) D.rm A3 X5) fun A4 =>
      strictB (Nat.xor (Nat.xor (Nat.xor (Nat.xor A A1) A2) A3) A4) fun N =>
      andB (Nat.ble (eqRows D A1 A) (nat_lit 2))
      (andB (Nat.ble (eqRows D N (nat_lit 0)) (nat_lit 16))
      (andB (Nat.blt (nat_lit 0) O.f5) (andB (Nat.blt O.f5 (nat_lit 32))
      (andB (Nat.beq (rowAt D A1 O.f5) (rowAt D A O.f5))
      (andB (Nat.blt (nat_lit 0) O.v5) (andB (Nat.blt O.v5 (nat_lit 32))
      (andB (Nat.beq (rowAt D N O.v5) (nat_lit 0))
      (andB (combChk D.rm (U0 D) (cycPt D X5 (uVec D O.v5) (uVec D O.f5)) O.gs5)
        (combChk D.rm (U0 D) (cycPt D X31 (D.bvL 0) (vecB D.rm (vecB D.rm (vecB D.rm (vecB D.rm (D.bvL 0) X31) X31) X31) X31))
          O.gs31))))))))))))
  (chainEl D O.x5) (chainEl D O.x31)

/-- Corpus: `CFSG.KC.ThDemp.qChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:367. -/
noncomputable def qChk : Bool :=
  (fun La Lb => andB (Nat.beq (qRows O.qm (nat_lit 1) La) (nat_lit 0))
    (andB (BigS.notB (Nat.beq (qRows O.qm (nat_lit 5) La) (nat_lit 0)))
    (andB (BigS.notB (Nat.beq (qRows O.qm (nat_lit 25) La) (nat_lit 0)))
    (andB (Nat.ble (qCount O.qm La) (nat_lit 5)) (Nat.ble (qCount O.qm Lb) (nat_lit 5))))))
  (powStack D (chainEl D O.x31) (U0 D) (nat_lit 30)) (powStack D (chainEl D O.yb) (U0 D) (nat_lit 30))

/-- Corpus: `CFSG.KC.ThDemp.normChk`, Certificates/Data/Kernel/ThDemp/Orb.lean:374. -/
noncomputable def normChk : Bool :=
  (fun X31 => strictB (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))) fun M =>
    strictB (mulB (cR (nat_lit 5)) D.rm (U0 D) M) fun P1 => strictB (mulB (cR (nat_lit 5)) D.rm P1 M) fun P2 =>
    andB (Nat.beq (D.mul M X31) (D.mul (pow5 D X31 (nat_lit 5)) M))
    (andB (BigS.notB (Nat.beq (keyL D.rm (U0 D)) (keyL D.rm P1)))
    (andB (BigS.notB (Nat.beq (keyL D.rm (U0 D)) (keyL D.rm P2)))
      (BigS.notB (Nat.beq (keyL D.rm P1) (keyL D.rm P2))))))
  (chainEl D O.x31)

end CFSGOutside.Corpus.Th.KC.ThDemp
