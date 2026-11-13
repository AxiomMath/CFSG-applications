import Mathlib

/-!
# Copied corpus definitions: the Baby Monster model and its strip engine

Definitions copied verbatim from AxiomMath/CFSG @ 69cb972 by
a generator script (each docstring names the corpus declaration
and file:line). The corpus namespaces `CFSG.X` are mapped to `CFSGOutside.Corpus.B.X`. The seed strings
`BSeed1`, `BSeed2` read `Data/BG1-f2r4370B0.m1`, `.m2`, byte-for-byte copies of
`CFSG/Blueprint/Data/BG1-f2r4370B0.m1`, `.m2`.

* the model: `NativeSporadic.decode`, `seedMonoid`, `BSeed1`, `BSeed2`, `B`, and the seeds `genA₁`,
  `genA₂`;
* the classes of involutions and the orbits of `C(2A)` on `2A` (`BabyTables.lean`);
* the strip representation of 4370 × 4370 matrices over `𝔽₂` and the kernel checks on it
  (`lget`, `F2.lean`, `stripMat`, `AllStrips`, `idStrips`, `AllStripsX`).
-/

namespace CFSGOutside.Corpus.B.Blueprint.NativeSporadic

noncomputable section

/-- Corpus: `CFSG.Blueprint.NativeSporadic.asciiWhitespace`, CFSG/Blueprint/NativeSporadic.lean:10. -/
def asciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

/-- Corpus: `CFSG.Blueprint.NativeSporadic.decode`, CFSG/Blueprint/NativeSporadic.lean:13. -/
def decode (p d mode : ℕ) (s : String) : Matrix (Fin d) (Fin d) (ZMod p) :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let entries : List ℕ := if mode = 1 then
    (body.filter fun c => !asciiWhitespace c).map fun c =>
      if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0
    else
      ((String.ofList (body.map fun c => if asciiWhitespace c then ' ' else c)).splitOn " ").filter
        (· != "") |>.map fun token => if token.toList.all (fun c => '0' ≤ c && c ≤ '9') then token.toNat?.getD 0 else 0
  fun i j => (entries[i.val * d + j.val]?.getD 0 : ZMod p)

/-- Corpus: `CFSG.Blueprint.NativeSporadic.seedMonoid`, CFSG/Blueprint/NativeSporadic.lean:23. -/
def seedMonoid (p d mode : ℕ) (s₁ s₂ : String) :
    Submonoid (Matrix (Fin d) (Fin d) (ZMod p)) :=
  Submonoid.closure {decode p d mode s₁, decode p d mode s₂}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.BSeed1`, CFSG/Blueprint/NativeSporadic.lean:123. -/
def BSeed1 : String := include_str "../Data"/"BG1-f2r4370B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.BSeed2`, CFSG/Blueprint/NativeSporadic.lean:124. -/
def BSeed2 : String := include_str "../Data"/"BG1-f2r4370B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.B`, CFSG/Blueprint/NativeSporadic.lean:125. -/
abbrev B : Type := (seedMonoid 2 4370 1 BSeed1 BSeed2)ˣ

end

end CFSGOutside.Corpus.B.Blueprint.NativeSporadic

namespace CFSGOutside.Corpus.B.Monster.GMS

open CFSGOutside.Corpus.B.Blueprint.NativeSporadic

/-- Corpus: `CFSG.Monster.GMS.babyCentOrder`, CFSG/Monster/GMS/Facts/BabyTables.lean:11. -/
def babyCentOrder : Fin 4 → ℕ :=
  ![2 ^ 38 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19,
    2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23,
    2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7,
    2 ^ 27 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17]

/-- Corpus: `CFSG.Monster.GMS.BabyInv`, CFSG/Monster/GMS/Facts/BabyTables.lean:17. -/
def BabyInv (k : Fin 4) (t : B) : Prop :=
  orderOf t = 2 ∧ Nat.card (Subgroup.centralizer ({t} : Set B)) = babyCentOrder k

/-- Corpus: `CFSG.Monster.GMS.BabyTableIII`, CFSG/Monster/GMS/Facts/BabyTables.lean:20. -/
def BabyTableIII : Prop :=
  (∀ t : B, orderOf t = 2 → ∃ k, BabyInv k t) ∧
    ∀ k s t, BabyInv k s → BabyInv k t → IsConj s t

/-- Corpus: `CFSG.Monster.GMS.BabyOrbit`, CFSG/Monster/GMS/Facts/BabyTables.lean:24. -/
def BabyOrbit (k : Fin 4) (r s : B) : Prop :=
  match k with
  | 0 => BabyInv 1 (r * s)
  | 1 => BabyInv 3 (r * s)
  | 2 => orderOf (r * s) = 3
  | 3 => orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2)

/-- Corpus: `CFSG.Monster.GMS.babyOrbitSize`, CFSG/Monster/GMS/Facts/BabyTables.lean:31. -/
def babyOrbitSize : Fin 4 → ℕ := ![3968055, 23113728, 2370830336, 11174042880]

/-- Corpus: `CFSG.Monster.GMS.BabyTableIV`, CFSG/Monster/GMS/Facts/BabyTables.lean:33. -/
def BabyTableIV : Prop :=
  ∀ r : B, BabyInv 0 r →
    (∀ s, BabyInv 0 s → s ≠ r → ∃ k, BabyOrbit k r s) ∧
    (∀ k s s', BabyInv 0 s → BabyInv 0 s' → BabyOrbit k r s → BabyOrbit k r s' →
      ∃ g ∈ Subgroup.centralizer ({r} : Set B), g * s * g⁻¹ = s') ∧
    ∀ k, {s | BabyInv 0 s ∧ BabyOrbit k r s}.ncard = babyOrbitSize k


end CFSGOutside.Corpus.B.Monster.GMS

namespace CFSGOutside.Corpus.B.Monster.B

open CFSGOutside.Corpus.B.Blueprint


/-- Corpus: `CFSG.Monster.B.genA₁`, CFSG/Monster/B/Pinned/GeneratorDeterminantsBase.lean:14. -/
noncomputable abbrev genA₁ : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1

/-- Corpus: `CFSG.Monster.B.genA₂`, CFSG/Monster/B/Pinned/GeneratorDeterminantsBase.lean:17. -/
noncomputable abbrev genA₂ : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2

end CFSGOutside.Corpus.B.Monster.B

namespace CFSGOutside.Corpus.B.KC.YModel

/-- Corpus: `CFSG.KC.YModel.lget`, Certificates/Data/Kernel/YModel/Text.lean:100. -/
noncomputable def lget (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun j' _ => ih j') j) l i

end CFSGOutside.Corpus.B.KC.YModel

namespace CFSGOutside.Corpus.B.KC.BM

/-- Corpus: `CFSG.KC.BM.forceB`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:9. -/
noncomputable def forceB (v : Nat) (k : Nat → Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (k v) (k v) (Nat.beq v (nat_lit 0))

/-- Corpus: `CFSG.KC.BM.forceBB`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:12. -/
noncomputable def forceBB (v : Nat) (k : Nat → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (k v) (k v) (Nat.beq v (nat_lit 0))

/-- Corpus: `CFSG.KC.BM.LM`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:15. -/
noncomputable def LM : Nat := nat_lit 18446744073709551615

/-- Corpus: `CFSG.KC.BM.SM`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:17. -/
noncomputable def SM : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 279680)) (nat_lit 1)) LM

/-- Corpus: `CFSG.KC.BM.mulS`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:20. -/
noncomputable def mulS (Bs : List Nat) (A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun u ih acc =>
      (fun t SMa SMb => ih (Nat.xor acc
          (List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
            (fun _ a0 a1 => Nat.xor (Nat.shiftRight a0 t) (Nat.shiftRight a1 (Nat.succ t)))
            (fun T _ ih2 Ac a0 a1 => ih2 (Nat.shiftRight Ac (nat_lit 4096))
                (Nat.xor a0 (Nat.mul (Nat.land Ac LM) (Nat.land T SMa)))
                (Nat.xor a1 (Nat.mul (Nat.shiftRight (Nat.land Ac (nat_lit 340282366920938463463374607431768211455))
                  (nat_lit 64)) (Nat.land T SMb))))
            Bs (Nat.shiftRight A (Nat.mul (nat_lit 64) t)) (nat_lit 0) (nat_lit 0))))
        (Nat.add u u) (Nat.shiftLeft SM (Nat.add u u)) (Nat.shiftLeft SM (Nat.succ (Nat.add u u))))
    (nat_lit 32) (nat_lit 0)

/-- Corpus: `CFSG.KC.BM.mulW`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:34. -/
noncomputable def mulW (Ws : List (List Nat)) (A : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun Bs _ ih A => forceB (mulS Bs A) ih) Ws A

/-- Corpus: `CFSG.KC.BM.rowsS`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:38. -/
noncomputable def rowsS (s : Nat) : Nat :=
  (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 64) r (Nat.ble r (nat_lit 64)))
    (Nat.sub (nat_lit 4370) (Nat.mul (nat_lit 64) s))

/-- Corpus: `CFSG.KC.BM.idS`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:42. -/
noncomputable def idS (s : Nat) : Nat :=
  Nat.shiftLeft
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 65) (rowsS s)))
      (nat_lit 1)) (nat_lit 36893488147419103231))
    (Nat.mul (nat_lit 4096) s)

/-- Corpus: `CFSG.KC.BM.maskS`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:48. -/
noncomputable def maskS (s : Nat) : Nat :=
  Nat.mul SM (Nat.sub (Nat.shiftLeft (nat_lit 1) (rowsS s)) (nat_lit 1))

/-- Corpus: `CFSG.KC.BM.wfMat`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:51. -/
noncomputable def wfMat (M : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s))
      (Nat.beq (Nat.land T (maskS s)) T)) M (nat_lit 0)) (nat_lit 69)

/-- Corpus: `CFSG.KC.BM.eqMat`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:56. -/
noncomputable def eqMat (X Y : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun Y => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Y)
    (fun x _ ih Y => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (ih ys) (Nat.beq x y)) Y) X Y

/-- Corpus: `CFSG.KC.BM.isId`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:62. -/
noncomputable def isId (X : List Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s))
      (Nat.beq T (idS s))) X (nat_lit 0)) (nat_lit 69)

/-- Corpus: `CFSG.KC.BM.vecMul`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:67. -/
noncomputable def vecMul (Rb : List (List Nat)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun blk _ ih v acc =>
      List.rec (motive := fun _ => Nat → Nat → Nat) (fun v acc => ih v acc)
        (fun r _ ih2 v acc =>
          forceB (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) r)) (fun acc' =>
            ih2 (Nat.shiftRight v (nat_lit 1)) acc')) blk v acc) Rb v (nat_lit 0)

/-- Corpus: `CFSG.KC.BM.vecW`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:75. -/
noncomputable def vecW (Ws : List (List (List Nat))) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun R _ ih v => forceB (vecMul R v) ih) Ws v

/-- Corpus: `CFSG.KC.BM.notB`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:79. -/
noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

/-- Corpus: `CFSG.KC.BM.andB`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:81. -/
noncomputable def andB (b c : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false c b

/-- Corpus: `CFSG.KC.BM.foldRows`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:83. -/
noncomputable def foldRows (f : Nat → Nat → Nat → Nat) (M : List Nat) (st : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun T _ ih i st =>
      Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ i st => ih i st)
        (fun _ ih2 T i st =>
          forceB (f i (Nat.land T SM) st) (fun st' => ih2 (Nat.shiftRight T (nat_lit 1)) (Nat.succ i) st'))
        (nat_lit 64) T i st) M (nat_lit 0) st

/-- Corpus: `CFSG.KC.BM.echStep`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:91. -/
noncomputable def echStep (r st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) r
    (andB (notB (Nat.beq r (nat_lit 0))) (andB (Nat.blt r st) (Nat.blt r (Nat.xor r st))))

/-- Corpus: `CFSG.KC.BM.topRow`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:95. -/
noncomputable def topRow : Nat := Nat.shiftLeft (nat_lit 1) (nat_lit 279681)

/-- Corpus: `CFSG.KC.BM.shapeOK`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:97. -/
noncomputable def shapeOK (M : List Nat) (k : Nat) : Bool :=
  notB (Nat.beq (foldRows (fun i r st =>
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st (Nat.beq r (nat_lit 0)))
      (echStep r st) (Nat.blt i k)) M topRow) (nat_lit 0))

/-- Corpus: `CFSG.KC.BM.echFrom`, CFSG/Certificates/Kernel/BabyMonster/F2.lean:103. -/
noncomputable def echFrom (M : List Nat) (k : Nat) : Bool :=
  notB (Nat.beq (foldRows (fun i r st =>
    Bool.rec (motive := fun _ => Nat) st
      (Bool.rec (motive := fun _ => Nat) st (echStep r st) (Nat.blt i (nat_lit 4370)))
      (Nat.ble k i)) M topRow) (nat_lit 0))

end CFSGOutside.Corpus.B.KC.BM

namespace CFSGOutside.Corpus.B.KC.BM

open CFSGOutside.Corpus.B.KC.YModel

/-- Corpus: `CFSG.KC.BM.stripMat`, CFSG/Certificates/Kernel/BabyMonster/SoundDefs.lean:47. -/
noncomputable def stripMat (S : List Nat) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  fun i j => if (lget S (i.val / 64)).testBit (64 * j.val + i.val % 64) then 1 else 0

/-- Corpus: `CFSG.KC.BM.AllStrips`, CFSG/Certificates/Kernel/BabyMonster/SoundDefs.lean:50. -/
inductive AllStrips (Ws : List (List Nat)) : List Nat → List Nat → Prop
  | nil : AllStrips Ws [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (mulW Ws a) c = true → AllStrips Ws as cs → AllStrips Ws (a :: as) (c :: cs)


/-- Corpus: `CFSG.KC.BM.idStrips`, CFSG/Certificates/Kernel/BabyMonster/SoundDefs.lean:60. -/
noncomputable def idStrips : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons (idS k) acc)) (nat_lit 69) List.nil

end CFSGOutside.Corpus.B.KC.BM

namespace CFSGOutside.Corpus.B.KC.BM.Fix

open CFSGOutside.Corpus.B.KC.BM

/-- Corpus: `CFSG.KC.BM.Fix.AllStripsX`, CFSG/Certificates/Kernel/BabyMonster/FixSound.lean:29. -/
inductive AllStripsX (Q : List Nat) : List Nat → List Nat → Prop
  | nil : AllStripsX Q [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (Nat.xor (mulS Q a) a) c = true → AllStripsX Q as cs →
        AllStripsX Q (a :: as) (c :: cs)

end CFSGOutside.Corpus.B.KC.BM.Fix
