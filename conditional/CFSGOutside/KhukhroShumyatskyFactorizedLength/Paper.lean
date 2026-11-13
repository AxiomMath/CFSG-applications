import CFSGOutside.KhukhroShumyatskyFactorizedLength.Factorizations
import CFSGOutside.KhukhroShumyatskyFactorizedLength.SeriesOperations
import CFSGOutside.Corpus.Schreier

/-!
# Nonsoluble length of factorized groups (Khukhro–Shumyatsky)

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780, DOI 10.1007/s10231-014-0443-1, arXiv:1405.1899.

**Theorem 1.1.** If a finite group `G = AB` is factorized by two subgroups `A`, `B` of coprime orders, then the
nonsoluble length satisfies `λ(G) ≤ 2^{h*(A)+h*(B)} − 1`, where `h*` is the generalized Fitting height:
`nonsolubleLength_le_of_isFactorization` (and the `∀`-form `nonsolubleLengthLE_of_isFactorization`).

The classification of finite simple groups is the hypothesis `hCFSG`, as in the paper; it enters only through
Schreier's conjecture. The corpus theorems the proof uses are class hypotheses: `Schreier` (Lemma 2.1) and
`BurnsidePQ` (Burnside's `p^a q^b` theorem).

**Proof route.** Induction on `n ≥ h*(A) + h*(B)`. Pass to `Y = G/R(G)`, where `F(Y) = 1`, so the components `S`
of `Y` are the simple factors of `F*(Y) = E(Y)`. Each factorizes as `S = (S ∩ A)(S ∩ B)`. The kernels `K_A`,
`K_B` of the action on the components with `S ∩ A`, resp. `S ∩ B`, not of prime-power order are normal and
`K_A ∩ K_B = K` by Burnside. Lemma 3.3, `F*(A) ≤ K_A`, makes `h*` drop in `Y/K_A` and `Y/K_B`, so the induction
hypothesis applies, and the series of `Y/K_B` intersected with `K_A` is concatenated with that of `Y/K_A` and
the block `1 ≤ E(Y) ≤ K` (Schreier): `λ(Y) ≤ (2^n − 1) + (2^n − 1) + 1 = 2^{n+1} − 1`.
-/

namespace CFSGOutside.KhukhroShumyatskyFactorizedLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores CFSGOutside.NonsolubleLength

section MainTheorem

lemma IsFactorization.map {Y Z : Type*} [Group Y] [Group Z] {A B : Subgroup Y}
    (h : IsFactorization A B) (f : Y →* Z) (hf : Function.Surjective f) :
    IsFactorization (A.map f) (B.map f) := by
  intro z
  obtain ⟨y, rfl⟩ := hf z
  obtain ⟨a, ha, b, hb, rfl⟩ := h y
  exact ⟨f a, mem_map_of_mem f ha, f b, mem_map_of_mem f hb, map_mul f a b⟩

lemma coprime_map {Y Z : Type*} [Group Y] [Group Z] {A B : Subgroup Y}
    (h : (Nat.card A).Coprime (Nat.card B)) (f : Y →* Z) :
    (Nat.card (A.map f)).Coprime (Nat.card (B.map f)) :=
  Nat.Coprime.coprime_dvd_left (Subgroup.card_map_dvd A f)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd B f) h)

/-- The statement proved by induction on `n`. -/
def Claim (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G), IsFactorization A B →
    (Nat.card A).Coprime (Nat.card B) → ∀ hA hB : ℕ, GenFittingHeightLE A hA →
    GenFittingHeightLE B hB → hA + hB ≤ n → NonsolubleLengthLE G (2 ^ n - 1)

lemma claim_zero : Claim 0 := by
  intro G _ _ A B hAB _ hA hB gA gB hsum
  obtain rfl : hA = 0 := by omega
  obtain rfl : hB = 0 := by omega
  haveI := subsingleton_of_genFittingHeightLE_zero gA
  haveI := subsingleton_of_genFittingHeightLE_zero gB
  haveI : Subsingleton G := ⟨fun x y => by
    have key : ∀ g : G, g = 1 := fun g => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hAB g
      have h1 : (⟨a, ha⟩ : A) = 1 := Subsingleton.elim _ _
      have h2 : (⟨b, hb⟩ : B) = 1 := Subsingleton.elim _ _
      rw [show a = 1 from congrArg Subtype.val h1, show b = 1 from congrArg Subtype.val h2,
        mul_one]
    rw [key x, key y]⟩
  exact nonsolubleLengthLE_zero_of_isSolvable

variable (hCFSG : TauCeti.ClassificationStatement.{0})

section Step

variable {Y : Type} [Group Y] [Finite Y] (hF : fittingSubgroup Y = ⊥)

include hF in
/-- From the induction hypothesis: a series of `Y` from `K_A` with `2^n - 1` nonsoluble factors. -/
lemma series_from_kernelA {n : ℕ} (IH : Claim n) {A B : Subgroup Y} (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) {hA hB : ℕ} (gA : GenFittingHeightLE A hA)
    (gB : GenFittingHeightLE B hB) (hsum : hA + hB ≤ n + 1) :
    Nonempty (NSeries Y (kernelOf (compsA A)) (2 ^ n - 1)) := by
  haveI : (kernelOf (compsA A)).Normal := kernelOf_compsA_normal hAB hcop
  set KA := kernelOf (compsA A)
  let π := QuotientGroup.mk' KA
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective KA
  have hlift : NonsolubleLengthLE (Y ⧸ KA) (2 ^ n - 1) → Nonempty (NSeries Y KA (2 ^ n - 1)) :=
    fun ⟨s⟩ => ⟨(s.comap π hπ).cast (QuotientGroup.ker_mk' KA)⟩
  apply hlift
  rcases hA with _ | k
  · -- `A = 1`: then `K_A = Y`
    haveI := subsingleton_of_genFittingHeightLE_zero gA
    have hKA : KA = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine mem_kernelOf.2 fun S hS => absurd ⟨2, 0, Nat.prime_two, ?_⟩ hS.2
      rw [pow_zero, Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
      have ha : (⟨a, a.2.2⟩ : A) = ⟨b, b.2.2⟩ := Subsingleton.elim _ _
      have hab : (a : Y) = b := congrArg (fun z : A => (z : Y)) ha
      exact Subtype.ext hab
    haveI : Subsingleton (Y ⧸ KA) := by
      rw [QuotientGroup.subsingleton_iff]; exact hKA
    exact NonsolubleLengthLE.mono (Nat.zero_le _) nonsolubleLengthLE_zero_of_isSolvable
  · have hker : generalizedFitting A ≤ (π.subgroupMap A).ker := by
      intro x hx
      have := generalizedFitting_le_kernelOf hF ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : Y)).2 this
    exact IH _ _ _ (hAB.map π hπ) (coprime_map hcop π) k hB
      (gA.of_surjective_of_le_ker (π.subgroupMap_surjective A) hker)
      (gB.of_surjective (π.subgroupMap_surjective B)) (by omega)

include hF hCFSG in
lemma step [BurnsidePQ.{0}] [Schreier] {n : ℕ} (IH : Claim n) {A B : Subgroup Y} (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) {hA hB : ℕ} (gA : GenFittingHeightLE A hA)
    (gB : GenFittingHeightLE B hB) (hsum : hA + hB ≤ n + 1) :
    NonsolubleLengthLE Y (2 ^ (n + 1) - 1) := by
  obtain ⟨sA⟩ := series_from_kernelA hF IH hAB hcop gA gB hsum
  obtain ⟨sB⟩ := series_from_kernelA hF IH hAB.symm hcop.symm gB gA (by omega)
  haveI : (kernelOf (compsA A)).Normal := kernelOf_compsA_normal hAB hcop
  haveI : (layer Y).Normal := (factorFamily_components hF).normal
  have s := (NSeries.interConcat sB sA).cast (kernelOf_compsA_inf hF hAB hcop)
  have hVK : layer Y ≤ kernelOf (components Y) := fun v hv => mem_kernelOf.2 fun S hS =>
    (factorFamily_components hF).normalizes S hS hv
  have s' := s.prependBlock (A := ⊥) (B := layer Y) bot_le hVK ⟨0, rfl⟩
    (semisimpleFactor_layer hF) (dA_kernel_le_layer hF hCFSG)
  have h2 : 2 ^ n - 1 + (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
    have := Nat.one_le_two_pow (n := n)
    rw [pow_succ]; omega
  rw [← h2]
  exact ⟨s'⟩

end Step

include hCFSG in
theorem claim [BurnsidePQ.{0}] [Schreier] : ∀ n, Claim n := by
  intro n
  induction n with
  | zero => exact claim_zero
  | succ n IH =>
    intro G _ _ A B hAB hcop hA hB gA gB hsum
    set R := solvableRadical G
    let π := QuotientGroup.mk' R
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
    obtain ⟨s⟩ := step hCFSG (fittingSubgroup_quotient_solvableRadical_eq_bot G) IH
      (hAB.map π hπ) (coprime_map hcop π) (gA.of_surjective (π.subgroupMap_surjective A))
      (gB.of_surjective (π.subgroupMap_surjective B)) hsum
    exact ⟨((s.comap π hπ).cast (QuotientGroup.ker_mk' R)).prependSoluble
      ((isSolvable_subgroup_iff R).1
        isSolvable_solvableRadical)⟩

include hCFSG in
/-- **Theorem 1.1 (Khukhro–Shumyatsky, Ann. Mat. Pura Appl. 2015)**, in `∀`-form: if `G = AB` with
`gcd(|A|, |B|) = 1`, `h*(A) ≤ a` and `h*(B) ≤ b`, then `λ(G) ≤ 2^{a+b} - 1`. -/
theorem nonsolubleLengthLE_of_isFactorization [BurnsidePQ.{0}] [Schreier] (G : Type) [Group G] [Finite G]
    (A B : Subgroup G) (hAB : IsFactorization A B) (hcop : (Nat.card A).Coprime (Nat.card B))
    {a b : ℕ} (hA : GenFittingHeightLE A a) (hB : GenFittingHeightLE B b) :
    NonsolubleLengthLE G (2 ^ (a + b) - 1) :=
  claim hCFSG (a + b) G A B hAB hcop a b hA hB le_rfl

include hCFSG in
/-- **Length of factorized groups.** Let G = AB be a finite group with A and B subgroups of coprime orders. Then the
nonsoluble length of G is at most 2^(h*(A) + h*(B)) − 1, where h*(X) is the generalized Fitting height of X, the
least h with F*_h(X) = X for the series F*_{i+1}(X)/F*_i(X) = F*(X/F*_i(X)).

Source: E. I. Khukhro and P. Shumyatsky, On the length of finite factorized groups, Ann. Mat. Pura Appl. 194 (2015),
1775–1780, Theorem 1.1. https://doi.org/10.1007/s10231-014-0443-1

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem nonsolubleLength_le_of_isFactorization [BurnsidePQ.{0}] [Schreier] (G : Type) [Group G]
    [Finite G] (A B : Subgroup G) (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    nonsolubleLength G ≤ 2 ^ (genFittingHeight A + genFittingHeight B) - 1 :=
  Nat.sInf_le (nonsolubleLengthLE_of_isFactorization hCFSG G A B hAB hcop
    genFittingHeightLE_genFittingHeight genFittingHeightLE_genFittingHeight)

end MainTheorem

end CFSGOutside.KhukhroShumyatskyFactorizedLength
