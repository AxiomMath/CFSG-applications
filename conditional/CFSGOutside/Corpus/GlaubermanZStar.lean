import Mathlib

/-!
# Corpus input: Glauberman's Z*-theorem for isolated involutions

Statement of `CFSG.ZStar.glauberman_zStar`, copied verbatim from `CFSG/LocalAnalysis/ZStar.lean` (line 15) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `CFSG.Milestones.glauberman_zStar`
(`CFSG/Milestones/LR_Glauberman_Z_star_central_Sylow_involution.lean`, line 24) is the same theorem. The clean
build provides the instance, in `clean/CFSGOutsideClean/Corpus/GlaubermanZStar.lean`.

An involution `t` of a finite group `G` that commutes with none of its other conjugates lies in `Z*(G)`: some
normal subgroup of odd order contains every commutator `g t g⁻¹ t⁻¹`.
-/

namespace CFSGOutside.Corpus

/-- Glauberman's Z*-theorem, as `CFSG.ZStar.glauberman_zStar` states it. -/
class GlaubermanZStar : Prop where
  glauberman_zStar : ∀ (G : Type) [Group G] [Fintype G] (t : G) (_ht1 : t ≠ 1) (_ht2 : t * t = 1)
    (_hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t),
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧ ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N

end CFSGOutside.Corpus
