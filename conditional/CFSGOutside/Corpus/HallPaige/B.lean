import CFSGOutside.Corpus.HallPaige.B.SevenFacts
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Baby Monster

The corpus theorems used for `B` (AxiomMath/CFSG @ 69cb972), stated as the fields of a class with their
exact statements, over the copied definitions of `CFSGOutside.Corpus.B` (`B/Defs.lean`, `B/Data.lean`,
`B/SevenFacts.lean`). They describe the corpus model `NativeSporadic.B ≤ GL₄₃₇₀(𝔽₂)` (the units of the
closure of the two seeds) and its action on the class `2A` (`BabyInv 0`):

* `babyTableIII`, `babyTableIV`: the involution classes and the five orbits of `C(r)`, `r ∈ 2A`, on `2A`
  (sizes `1, 3968055, 23113728, 2370830336, 11174042880`, each `C(r)`-transitive);
* `babyInv_zero_of_rank_1860`, `babyInv_one_of_rank_2048`, `babyInv_three_of_rank_2158`: an involution
  `X` lies in `2A`, `2B`, `2C` (`BabyInv 0, 1, 3`) when `rank (X - 1)` is `1860`, `2048`, `2158`;
* `nonempty_mulEquiv`: the model is the presented group `B`;
* `certificate17101`, `certificate17450`, `genA₁_mul_self`: certified facts about the seed `genA₁` and
  the corpus matrices `Seven.*`, `SevenLocal.*` (orders, commutations, ranks, membership in the model);
* `stripMat_mul_of_allStrips`, `stripMat_mul_eq_one`, `rank_sub_one_of_cert`: soundness of the corpus
  strip engine (products and rank certificates checked by kernel evaluation).
-/

namespace CFSGOutside.Corpus.B

open Blueprint KC.BM KC.BM.Fix

/-- The corpus theorems for `B`. -/
class Theorems : Prop where
  /-- Corpus: `CFSG.Monster.Existence.babyTableIII`, CFSG/Monster/Existence/MilestoneInputs.lean:303. -/
  babyTableIII :
    Monster.GMS.BabyTableIII
  /-- Corpus: `CFSG.Monster.Existence.babyTableIV`, CFSG/Monster/Existence/MilestoneInputs.lean:307. -/
  babyTableIV :
    Monster.GMS.BabyTableIV
  /-- Corpus: `CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.babyInv_zero_of_rank_1860`,
  CFSG/HardMathSupport/Timmesfeld/SporadicBalance/BSevenElems.lean:222. -/
  babyInv_zero_of_rank_1860 {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 1860) : Monster.GMS.BabyInv 0 X
  /-- Corpus: `CFSG.Monster.Existence.babyInv_one_of_rank_2048`,
  CFSG/Monster/Existence/BabyW2Classes.lean:102. -/
  babyInv_one_of_rank_2048
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2048) : Monster.GMS.BabyInv 1 X
  /-- Corpus: `CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.babyInv_three_of_rank_2158`,
  CFSG/HardMathSupport/Timmesfeld/SporadicBalance/BSevenLocal.lean:180. -/
  babyInv_three_of_rank_2158 {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2158) : Monster.GMS.BabyInv 3 X
  /-- Corpus: `CFSG.Sporadic.Bridge.B.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/BBound.lean:16. -/
  nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.B ≃* TauCeti.SporadicName.B.Group)
  /-- Corpus: `Certificates.certificate17101`, Certificates/Certificate17101.lean:17. -/
  certificate17101 : SevenFacts.Fact17101 ∧
    Blueprint.NativeSporadic.decode 2 4370 1 Blueprint.NativeSporadic.BSeed1 =
      stripMat Seeds.A1 ∧
    Blueprint.NativeSporadic.decode 2 4370 1 Blueprint.NativeSporadic.BSeed2 =
      stripMat Seeds.A2 ∧
    ∀ S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2)), stripMat Seeds.A1 ∈ S →
      stripMat Seeds.A2 ∈ S → stripMat Seven.g ∈ S ∧ stripMat Seven.al ∈ S ∧
        stripMat Seven.t1 ∈ S ∧ stripMat Seven.e3 ∈ S
  /-- Corpus: `Certificates.certificate17450`, Certificates/Certificate17450.lean:12. -/
  certificate17450 : KC.BM.SevenFacts.Fact17450
  /-- Corpus: `CFSG.Monster.B.genA₁_mul_self`, CFSG/Monster/B/Pinned/GeneratorDeterminants.lean:15. -/
  genA₁_mul_self : Monster.B.genA₁ * Monster.B.genA₁ = 1
  /-- Corpus: `CFSG.KC.BM.stripMat_mul_of_allStrips`,
  CFSG/Certificates/Kernel/BabyMonster/Sound.lean:12. -/
  stripMat_mul_of_allStrips {Ws : List (List Nat)} {A C : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hA : wfMat A = true) (h : AllStrips Ws A C) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = stripMat C
  /-- Corpus: `CFSG.KC.BM.stripMat_mul_eq_one`, CFSG/Certificates/Kernel/BabyMonster/Sound.lean:19. -/
  stripMat_mul_eq_one {Ws : List (List Nat)} {A : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hA : wfMat A = true) (h : AllStrips Ws A idStrips) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = 1
  /-- Corpus: `CertificateChecks.KernelBM.FiveA.rank_sub_one_of_cert`,
  Certificates/Kernel/BabyMonster/FiveA/RankLin.lean:59. -/
  rank_sub_one_of_cert {M P R : List Nat} {k : ℕ} (hk : k ≤ 4370)
    (hM : wfMat M = true) (hP : wfMat P = true) (hR : wfMat R = true)
    (hrk : AllStripsX M P R) (hs : shapeOK R k = true) (he : echFrom P k = true) :
    (stripMat M - 1).rank = k

end CFSGOutside.Corpus.B
