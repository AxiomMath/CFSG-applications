import CFSGOutside.Corpus.HallPaige.Ly.Defs
import CFSGOutside.Corpus.HallPaige.Ly.Packed
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Lyons group

The corpus theorems used for `Ly` (AxiomMath/CFSG @ 69cb972), stated as fields of the class
`CFSGOutside.Corpus.Ly.Theorems` with their exact statements, over the copied definitions of
`CFSGOutside.Corpus.Ly` (`Ly/Defs.lean`, `Ly/Data.lean`, `Ly/Packed.lean`):

* the seed instance `LySeed` of the 111-dimensional model `J ≤ GL₁₁₁(𝔽₅)`;
* `F1_all`: the action of `J` on the orbit `Ω` of `opE`, its stabilizer `lyH ≅ G₂(5)` and the
  five `lyH`-orbits on `Ω` (the double cosets of `lyH`);
* the packed-matrix facts `fmul`, `one_facts`, `af_facts` and `aStar_zero`, `aStar_one`, used to
  evaluate words in `J` in the kernel;
* `bridge_hom` and `finite_card_le`, which identify `J` with the presented group `Ly`.
-/

namespace CFSGOutside.Corpus.Ly

open MulAction

open Classical in
/-- The corpus theorems for `Ly`. -/
class Theorems : Prop where
  /-- Corpus: `Certificates.certificate3085.lySeed`, Certificates/Certificate3085.lean:47. -/
  lySeed : LySeed
  /-- Corpus: `CertificateChecks.KernelLy.Omega.F1_all`, Certificates/Kernel/Ly3085/Squeeze.lean:21. -/
  F1_all [LySeed] :
    (stabilizer J opE = lyH ∧ Nat.card lyH = 5859000000 ∧ Nat.card (orbit J opE) = 8835156) ∧
      ((Finset.univ.biUnion subO : Finset LyOperator) : Set LyOperator) = orbit J opE ∧
      (Pairwise fun i j => Disjoint (subO i) (subO j)) ∧
      Nat.card (orbit lyH opE) = 1 ∧ Nat.card (orbit lyH (gRep 1 • opE)) = 19530 ∧
      Nat.card (orbit lyH (gRep 2 • opE)) = 968750 ∧
      Nat.card (orbit lyH (gRep 3 • opE)) = 2034375 ∧
      Nat.card (orbit lyH (gRep 4 • opE)) = 5812500
  /-- Corpus: `CertificateChecks.KernelLy.Omega.one_facts`, Certificates/Kernel/Ly3085/Bridge.lean:63. -/
  one_facts : LCanon 12 111 111 BC.ONEF ∧ bigM BC.ONEF = 1
  /-- Corpus: `CertificateChecks.KernelLy.Omega.fmul`, Certificates/Kernel/Ly3085/Bridge.lean:68. -/
  fmul {X Y : ℕ} (hX : LCanon 12 111 111 X) (hY : LCanon 12 111 111 Y) :
    LCanon 12 111 111 (fMul BC X Y) ∧ bigM (fMul BC X Y) = bigM X * bigM Y
  /-- Corpus: `CertificateChecks.KernelLy.Omega.aStar_zero`, Certificates/Kernel/Ly3085/Bridge.lean:101. -/
  aStar_zero [LySeed] : aStar 0 = a
  /-- Corpus: `CertificateChecks.KernelLy.Omega.aStar_one`, Certificates/Kernel/Ly3085/Bridge.lean:106. -/
  aStar_one [LySeed] : aStar 1 = b
  /-- Corpus: `CertificateChecks.KernelLy.Omega.af_facts`, Certificates/Kernel/Ly3085/Bridge.lean:111. -/
  af_facts [LySeed] {j : ℕ} (hj : j < 7) :
    LCanon 12 111 111 (AF j) ∧ bigM (AF j) = mat (aStar j) ∧
      LCanon 12 111 111 (AI j) ∧ bigM (AI j) = mat (aStar j)⁻¹
  /-- Corpus: `Certificates.certificate3085.bridge_hom`, Certificates/Certificate3085.lean:49. -/
  bridge_hom :
    ∃ φ : TauCeti.Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
      ∀ g : GL (Fin 111) (ZMod 5), g.val = mA ∨ g.val = mB → g ∈ φ.range
  /-- Corpus: `CFSG.Sporadic.Presentation.Ly.finite_card_le`, CFSG/Sporadic/Presentation/Ly.lean:10. -/
  finite_card_le : Finite TauCeti.SporadicName.Ly.Group ∧
    Nat.card TauCeti.SporadicName.Ly.Group ≤ 51765179004000000

end CFSGOutside.Corpus.Ly
