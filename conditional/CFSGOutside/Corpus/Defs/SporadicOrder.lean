import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Copied corpus definitions: orders of the sporadic groups

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The copies are:

* `Open.orderJ3` to `Open.orderMonster` from `CFSG/Open/SporadicExistence.lean` (lines 42 to 65);
* `HardMathSupport.Solomon.Coordinator.sporOrd` from `CFSG/HardMathSupport/Solomon/Coordinator/GFR2FamSpor.lean`
  (line 16) and `SporadicOrdersTable` (line 44) from the same file.

`clean/CFSGOutsideClean/Corpus/Defs/SporadicOrder.lean` shows that each copy equals its original.
-/


namespace CFSGOutside.Corpus

namespace Open

def orderJ3 : ℕ := 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19

def orderRu : ℕ := 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29

def orderON : ℕ := 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31

def orderHN : ℕ := 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19

def orderFi23 : ℕ := 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23

def orderCo1 : ℕ := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23

def orderLy : ℕ := 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67

def orderTh : ℕ := 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31

def orderJ4 : ℕ := 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43

def orderFi24Prime : ℕ := 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29

def orderBabyMonster : ℕ := 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

def orderMonster : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

end Open

namespace HardMathSupport.Solomon.Coordinator

open Open

def sporOrd : TauCeti.SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => orderJ3
  | .J4 => orderJ4
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => orderRu
  | .Suz => 448345497600
  | .ONan => orderON
  | .Co1 => orderCo1
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => orderFi23
  | .Fi24Prime => orderFi24Prime
  | .HN => orderHN
  | .Ly => orderLy
  | .Th => orderTh
  | .B => orderBabyMonster
  | .M => orderMonster

def SporadicOrdersTable : Prop :=
  ∀ name : TauCeti.SporadicName, Nat.card (TauCeti.CFSGIndex.sporadic name).Group = sporOrd name

end HardMathSupport.Solomon.Coordinator

end CFSGOutside.Corpus
