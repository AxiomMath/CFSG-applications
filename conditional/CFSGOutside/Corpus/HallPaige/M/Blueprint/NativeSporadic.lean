import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

/-!
# Copied corpus declarations from `CFSG/Blueprint/NativeSporadic.lean`

Declarations copied verbatim from AxiomMath/CFSG @ 69cb972 by a script, with
`CFSG.*` renamed to `CFSGOutside.Corpus.M.*` (the definitional closure of the statements of the
classes in `Corpus/HallPaige/M.lean`, with the corpus proofs of the theorems these definitions
use). The imports are the module's own transitive non-corpus imports and the copies of its
corpus imports, so every proof elaborates in the corpus's environment.
-/

/-! ### `CFSG/Blueprint/NativeSporadic.lean` -/

noncomputable section

namespace CFSGOutside.Corpus.M.Blueprint.NativeSporadic

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

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M11`, CFSG/Blueprint/NativeSporadic.lean:27. -/
def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]),
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M12`, CFSG/Blueprint/NativeSporadic.lean:31. -/
def M12 : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]),
    (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M22`, CFSG/Blueprint/NativeSporadic.lean:35. -/
def M22 : Subgroup (Equiv.Perm (Fin 22)) :=
  Subgroup.closure {(List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]),
    (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M23`, CFSG/Blueprint/NativeSporadic.lean:39. -/
def M23 : Subgroup (Equiv.Perm (Fin 23)) :=
  Subgroup.closure {(List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]),
    (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M24`, CFSG/Blueprint/NativeSporadic.lean:43. -/
def M24 : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]),
    (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J1Seed1`, CFSG/Blueprint/NativeSporadic.lean:47. -/
def J1Seed1 : String := include_str "../../Data"/"MJ1G1-f11r7B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J1Seed2`, CFSG/Blueprint/NativeSporadic.lean:48. -/
def J1Seed2 : String := include_str "../../Data"/"MJ1G1-f11r7B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J1`, CFSG/Blueprint/NativeSporadic.lean:49. -/
abbrev J1 : Type := (seedMonoid 11 7 3 J1Seed1 J1Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J2Seed1`, CFSG/Blueprint/NativeSporadic.lean:51. -/
def J2Seed1 : String := include_str "../../Data"/"MJ2G1-f5r14B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J2Seed2`, CFSG/Blueprint/NativeSporadic.lean:52. -/
def J2Seed2 : String := include_str "../../Data"/"MJ2G1-f5r14B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J2`, CFSG/Blueprint/NativeSporadic.lean:53. -/
abbrev J2 : Type := (seedMonoid 5 14 1 J2Seed1 J2Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J3Seed1`, CFSG/Blueprint/NativeSporadic.lean:55. -/
def J3Seed1 : String := include_str "../../Data"/"MJ3G1-f2r80B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J3Seed2`, CFSG/Blueprint/NativeSporadic.lean:56. -/
def J3Seed2 : String := include_str "../../Data"/"MJ3G1-f2r80B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J3`, CFSG/Blueprint/NativeSporadic.lean:57. -/
abbrev J3 : Type := (seedMonoid 2 80 1 J3Seed1 J3Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4Seed1`, CFSG/Blueprint/NativeSporadic.lean:59. -/
def J4Seed1 : String := include_str "../../Data"/"J4G1-f2r112B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4Seed2`, CFSG/Blueprint/NativeSporadic.lean:60. -/
def J4Seed2 : String := include_str "../../Data"/"J4G1-f2r112B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.J4`, CFSG/Blueprint/NativeSporadic.lean:61. -/
abbrev J4 : Type := (seedMonoid 2 112 1 J4Seed1 J4Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co1Seed1`, CFSG/Blueprint/NativeSporadic.lean:63. -/
def Co1Seed1 : String := include_str "../../Data"/"MCo1G1-f2r24B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co1Seed2`, CFSG/Blueprint/NativeSporadic.lean:64. -/
def Co1Seed2 : String := include_str "../../Data"/"MCo1G1-f2r24B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co1`, CFSG/Blueprint/NativeSporadic.lean:65. -/
abbrev Co1 : Type := (seedMonoid 2 24 1 Co1Seed1 Co1Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co2Seed1`, CFSG/Blueprint/NativeSporadic.lean:67. -/
def Co2Seed1 : String := include_str "../../Data"/"MCo2G1-f2r22B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co2Seed2`, CFSG/Blueprint/NativeSporadic.lean:68. -/
def Co2Seed2 : String := include_str "../../Data"/"MCo2G1-f2r22B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co2`, CFSG/Blueprint/NativeSporadic.lean:69. -/
abbrev Co2 : Type := (seedMonoid 2 22 1 Co2Seed1 Co2Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co3Seed1`, CFSG/Blueprint/NativeSporadic.lean:71. -/
def Co3Seed1 : String := include_str "../../Data"/"MCo3G1-f2r22B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co3Seed2`, CFSG/Blueprint/NativeSporadic.lean:72. -/
def Co3Seed2 : String := include_str "../../Data"/"MCo3G1-f2r22B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Co3`, CFSG/Blueprint/NativeSporadic.lean:73. -/
abbrev Co3 : Type := (seedMonoid 2 22 1 Co3Seed1 Co3Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi22Seed1`, CFSG/Blueprint/NativeSporadic.lean:75. -/
def Fi22Seed1 : String := include_str "../../Data"/"MF22G1-f3r77B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi22Seed2`, CFSG/Blueprint/NativeSporadic.lean:76. -/
def Fi22Seed2 : String := include_str "../../Data"/"MF22G1-f3r77B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi22`, CFSG/Blueprint/NativeSporadic.lean:77. -/
abbrev Fi22 : Type := (seedMonoid 3 77 1 Fi22Seed1 Fi22Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23Seed1`, CFSG/Blueprint/NativeSporadic.lean:79. -/
def Fi23Seed1 : String := include_str "../../Data"/"F23G1-f3r253B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23Seed2`, CFSG/Blueprint/NativeSporadic.lean:80. -/
def Fi23Seed2 : String := include_str "../../Data"/"F23G1-f3r253B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi23`, CFSG/Blueprint/NativeSporadic.lean:81. -/
abbrev Fi23 : Type := (seedMonoid 3 253 1 Fi23Seed1 Fi23Seed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi24primeSeed1`, CFSG/Blueprint/NativeSporadic.lean:83. -/
def Fi24primeSeed1 : String := include_str "../../Data"/"MF24G1-f3r781B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi24primeSeed2`, CFSG/Blueprint/NativeSporadic.lean:84. -/
def Fi24primeSeed2 : String := include_str "../../Data"/"MF24G1-f3r781B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Fi24prime`, CFSG/Blueprint/NativeSporadic.lean:85. -/
abbrev Fi24prime : Type := (seedMonoid 3 781 1 Fi24primeSeed1 Fi24primeSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.HSSeed1`, CFSG/Blueprint/NativeSporadic.lean:87. -/
def HSSeed1 : String := include_str "../../Data"/"MHSG1-f2r20B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.HSSeed2`, CFSG/Blueprint/NativeSporadic.lean:88. -/
def HSSeed2 : String := include_str "../../Data"/"MHSG1-f2r20B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.HS`, CFSG/Blueprint/NativeSporadic.lean:89. -/
abbrev HS : Type := (seedMonoid 2 20 1 HSSeed1 HSSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.McLSeed1`, CFSG/Blueprint/NativeSporadic.lean:91. -/
def McLSeed1 : String := include_str "../../Data"/"MMcLG1-f3r21B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.McLSeed2`, CFSG/Blueprint/NativeSporadic.lean:92. -/
def McLSeed2 : String := include_str "../../Data"/"MMcLG1-f3r21B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.McL`, CFSG/Blueprint/NativeSporadic.lean:93. -/
abbrev McL : Type := (seedMonoid 3 21 1 McLSeed1 McLSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.HeSeed1`, CFSG/Blueprint/NativeSporadic.lean:95. -/
def HeSeed1 : String := include_str "../../Data"/"MHeG1-f7r50B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.HeSeed2`, CFSG/Blueprint/NativeSporadic.lean:96. -/
def HeSeed2 : String := include_str "../../Data"/"MHeG1-f7r50B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.He`, CFSG/Blueprint/NativeSporadic.lean:97. -/
abbrev He : Type := (seedMonoid 7 50 1 HeSeed1 HeSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.RuSeed1`, CFSG/Blueprint/NativeSporadic.lean:99. -/
def RuSeed1 : String := include_str "../../Data"/"MRuG1-f2r28B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.RuSeed2`, CFSG/Blueprint/NativeSporadic.lean:100. -/
def RuSeed2 : String := include_str "../../Data"/"MRuG1-f2r28B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Ru`, CFSG/Blueprint/NativeSporadic.lean:101. -/
abbrev Ru : Type := (seedMonoid 2 28 1 RuSeed1 RuSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.SuzSeed1`, CFSG/Blueprint/NativeSporadic.lean:103. -/
def SuzSeed1 : String := include_str "../../Data"/"MSuzG1-f3r64B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.SuzSeed2`, CFSG/Blueprint/NativeSporadic.lean:104. -/
def SuzSeed2 : String := include_str "../../Data"/"MSuzG1-f3r64B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Suz`, CFSG/Blueprint/NativeSporadic.lean:105. -/
abbrev Suz : Type := (seedMonoid 3 64 1 SuzSeed1 SuzSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.ONSeed1`, CFSG/Blueprint/NativeSporadic.lean:107. -/
def ONSeed1 : String := include_str "../../Data"/"MONG1-f3r154B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.ONSeed2`, CFSG/Blueprint/NativeSporadic.lean:108. -/
def ONSeed2 : String := include_str "../../Data"/"MONG1-f3r154B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.ON`, CFSG/Blueprint/NativeSporadic.lean:109. -/
abbrev ON : Type := (seedMonoid 3 154 1 ONSeed1 ONSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.HNSeed1`, CFSG/Blueprint/NativeSporadic.lean:111. -/
def HNSeed1 : String := include_str "../../Data"/"MHNG1-f5r133B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.HNSeed2`, CFSG/Blueprint/NativeSporadic.lean:112. -/
def HNSeed2 : String := include_str "../../Data"/"MHNG1-f5r133B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.HN`, CFSG/Blueprint/NativeSporadic.lean:113. -/
abbrev HN : Type := (seedMonoid 5 133 1 HNSeed1 HNSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.LySeed1`, CFSG/Blueprint/NativeSporadic.lean:115. -/
def LySeed1 : String := include_str "../../Data"/"LyG1-f5r111B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.LySeed2`, CFSG/Blueprint/NativeSporadic.lean:116. -/
def LySeed2 : String := include_str "../../Data"/"LyG1-f5r111B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Ly`, CFSG/Blueprint/NativeSporadic.lean:117. -/
abbrev Ly : Type := (seedMonoid 5 111 1 LySeed1 LySeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.ThSeed1`, CFSG/Blueprint/NativeSporadic.lean:119. -/
def ThSeed1 : String := include_str "../../Data"/"ThG1-f2r248B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.ThSeed2`, CFSG/Blueprint/NativeSporadic.lean:120. -/
def ThSeed2 : String := include_str "../../Data"/"ThG1-f2r248B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.Th`, CFSG/Blueprint/NativeSporadic.lean:121. -/
abbrev Th : Type := (seedMonoid 2 248 1 ThSeed1 ThSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.BSeed1`, CFSG/Blueprint/NativeSporadic.lean:123. -/
def BSeed1 : String := include_str "../../Data"/"BG1-f2r4370B0.m1"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.BSeed2`, CFSG/Blueprint/NativeSporadic.lean:124. -/
def BSeed2 : String := include_str "../../Data"/"BG1-f2r4370B0.m2"
/-- Corpus: `CFSG.Blueprint.NativeSporadic.B`, CFSG/Blueprint/NativeSporadic.lean:125. -/
abbrev B : Type := (seedMonoid 2 4370 1 BSeed1 BSeed2)ˣ

/-- Corpus: `CFSG.Blueprint.NativeSporadic.y443Adjacent`, CFSG/Blueprint/NativeSporadic.lean:127. -/
def y443Adjacent (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val ∈ ({1, 5, 9} : Set ℕ)) ∨
  (j.val = 0 ∧ i.val ∈ ({1, 5, 9} : Set ℕ)) ∨
  (i.val + 1 = j.val ∧ i.val ∈ ({1, 2, 3, 5, 6, 7, 9, 10} : Set ℕ)) ∨
  (j.val + 1 = i.val ∧ j.val ∈ ({1, 2, 3, 5, 6, 7, 9, 10} : Set ℕ))

/-- Corpus: `CFSG.Blueprint.NativeSporadic.y443Relations`, CFSG/Blueprint/NativeSporadic.lean:133. -/
def y443Relations : Set (FreeGroup (Fin 12)) := by
  classical
  exact {w | ∃ i : Fin 12, w = FreeGroup.of i ^ 2} ∪
  {w | ∃ i j : Fin 12, i.val < j.val ∧
    w = (FreeGroup.of i * FreeGroup.of j) ^ (if y443Adjacent i j then 3 else 2)} ∪
  {(FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 0 *
    FreeGroup.of 5 * FreeGroup.of 6 * FreeGroup.of 0 * FreeGroup.of 9 * FreeGroup.of 10) ^ 10}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Y443`, CFSG/Blueprint/NativeSporadic.lean:141. -/
abbrev Y443 : Type := PresentedGroup y443Relations

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M`, CFSG/Blueprint/NativeSporadic.lean:143. -/
abbrev M : Type := commutator Y443

/-- Corpus: `CFSG.Blueprint.NativeSporadic.Carrier`, CFSG/Blueprint/NativeSporadic.lean:145. -/
def Carrier : TauCeti.SporadicName → Type
  | .M11 => M11
  | .M12 => M12
  | .M22 => M22
  | .M23 => M23
  | .M24 => M24
  | .J1 => J1
  | .J2 => J2
  | .J3 => J3
  | .J4 => J4
  | .Co1 => Co1
  | .Co2 => Co2
  | .Co3 => Co3
  | .Fi22 => Fi22
  | .Fi23 => Fi23
  | .Fi24Prime => Fi24prime
  | .HS => HS
  | .McL => McL
  | .He => He
  | .Ru => Ru
  | .Suz => Suz
  | .ONan => ON
  | .HN => HN
  | .Ly => Ly
  | .Th => Th
  | .B => B
  | .M => M

/-- Corpus: `CFSG.Blueprint.NativeSporadic.carrierGroup`, CFSG/Blueprint/NativeSporadic.lean:173. -/
instance carrierGroup (s : TauCeti.SporadicName) : Group (Carrier s) := by
  cases s <;> dsimp [Carrier] <;> infer_instance

end CFSGOutside.Corpus.M.Blueprint.NativeSporadic
