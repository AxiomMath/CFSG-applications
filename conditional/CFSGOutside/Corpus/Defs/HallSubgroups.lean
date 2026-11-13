import Mathlib

/-!
# Copied corpus definitions: Hall subgroups

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`:

* `CFSG.FeitThompson.IsPiNumber` and `CFSG.FeitThompson.IsHallSubgroup`
  (`CFSG/FeitThompson/Foundations/HallContainsNormalPrimeSupport.lean`, lines 18 and 68), the corpus-own notion
  (`π : Set ℕ`);
* `CFSG.IsHallSubgroup` (`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/HallSubgroups/Core.lean`, line 19), the
  notion of the vendored Qiuzhen-CFSG files (`π : Set Nat.Primes`).
-/

namespace CFSGOutside.Corpus

namespace FeitThompson

variable {G : Type*} [Group G]

/-- All prime factors of `n` lie in `π`. Copy of `CFSG.FeitThompson.IsPiNumber`. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ∈ π

/-- A Hall `π`-subgroup. Copy of `CFSG.FeitThompson.IsHallSubgroup`. -/
structure IsHallSubgroup (π : Set ℕ) (H : Subgroup G) : Prop where
  natCard : IsPiNumber π (Nat.card H)
  index : IsPiNumber πᶜ H.index

end FeitThompson

/-- A Hall `π`-subgroup: a subgroup whose order involves only primes in `π` and whose index involves only primes not
in `π`. Copy of `CFSG.IsHallSubgroup`. -/
class IsHallSubgroup {G : Type*} [Group G] (π : Set Nat.Primes) (H : Subgroup G) : Prop where
  p_in_pi_of_p_dvd_card (p : Nat.Primes) : p.val ∣ Nat.card H → p ∈ π
  p_in_pi_of_p_dvd_index (p : Nat.Primes) : p.val ∣ H.index → p ∉ π

end CFSGOutside.Corpus
