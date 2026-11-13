import Mathlib

/-!
# Corpus definitions: strong closure and the odd core

Verbatim copies, under `CFSGOutside.Corpus`, of
- `CFSG.Open.fusionStronglyClosed` (`CFSG/Open/FusionDefs.lean`, line 19), and
- `CFSG.Open.goldschmidtOddCore` with its normality instance
  (`CFSG/Open/GoldschmidtStronglyClosedAbelianMilestoneDefs.lean`, lines 15–19),

at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.
-/

namespace CFSGOutside.Corpus

/-- `A` is strongly closed in `S` with respect to `G`: a conjugate of an element of `A` that
lies in `S` lies in `A` (Goldschmidt's sense). -/
def fusionStronglyClosed {G : Type*} [Group G] (A : Set G) (S : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A

/-- The largest normal subgroup of odd order, `O(H)`. -/
def goldschmidtOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance goldschmidtOddCore_normal (H : Type*) [Group H] : (goldschmidtOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

end CFSGOutside.Corpus
