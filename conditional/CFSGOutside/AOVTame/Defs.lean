import CFSGOutside.AOVTame.Kappa

/-!
# AOV tameness: tame fusion systems

AOV Definition 2.? (`d:tame`, §2.2): a saturated fusion system `F` over `S` is *tame* if there is a
finite group `G` with `S ∈ Syl_p(G)`, `F ≅ F_S(G)`, and `κ_G : Out(G) → Out_typ(L^c_S(G))` split
surjective.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe w

/-- `G` tamely realizes `F` over the Sylow subgroup `T`: `F ≅ F_T(G)` and `κ_G` is split surjective. -/
def TamelyRealizes {S : Type w} [Group S] (p : ℕ) [Fact p.Prime] (F : FusionSystem S)
    (G : Type) [Group G] [Finite G] (T : Sylow p G) : Prop :=
  Nonempty (FusionIso F (ofGroup G (T : Subgroup G))) ∧
    ∃ s : OutTyp p (T : Subgroup G) →* Out G, (kappa p T).comp s = MonoidHom.id _

/-- `F` is tame (AOV §2.2, `d:tame`). -/
def IsTame {S : Type w} [Group S] [Finite S] (p : ℕ) [Fact p.Prime] (F : FusionSystem S) : Prop :=
  F.Saturated p ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G) (T : Sylow p G), TamelyRealizes p F G T

end AndersenOliverVentura.Tame
