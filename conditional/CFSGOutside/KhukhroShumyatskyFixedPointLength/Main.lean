import CFSGOutside.Corpus.OddOrder
import CFSGOutside.Corpus.Schreier
import CFSGOutside.KhukhroShumyatskyFixedPointLength.Chain

/-!
# Khukhro–Shumyatsky, fixed points: the prime case and Theorem 1.3

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. The prime case of Theorem 1.3 (`nonsolubleLengthLE_of_prime`), and Theorem 1.3 itself
(`nonsolubleLengthLE_of_coprime_action`) by induction on `|A|`, with their numerical forms. The classification
statement is a hypothesis, as in the paper; the corpus theorems the proofs use (Feit–Thompson and Schreier's
conjecture for the catalogue) are class hypotheses.
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section Prime

variable {G : Type} [Group G] [Finite G]

lemma commSub_inv (φ : MulAut G) : ∀ n ∈ commSub φ, φ n ∈ commSub φ := by
  intro n hn
  induction hn using closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [map_mul, map_inv]; exact inv_mul_mem_commSub φ _
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

/-- A subgroup of a subgroup is isomorphic to its image in the ambient group. -/
noncomputable def equivOfMapSubtype {H : Subgroup G} {K : Subgroup H} {L : Subgroup G}
    (h : K.map H.subtype = L) : K ≃* L :=
  (K.equivMapOfInjective _ H.subtype_injective).trans (MulEquiv.subgroupCongr h)

variable {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}

/-- **The prime-order case of Theorem 1.3**: `λ(G) ≤ 2 λ(C_G(φ)) + 1`. -/
theorem nonsolubleLengthLE_of_prime [OddOrder.{0}] [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (2 * l + 1) := by
  set N := commSub φ with hNdef
  haveI : N.Normal := commSub_normal φ
  have hNinv : IsInv φ N := isInv_of_forall (commSub_inv φ)
  set ψ := restrictAut φ N hNinv
  have hψ : ψ ^ p = 1 := restrictAut_pow_eq_one hφ N hNinv
  have hpN : ¬ p ∣ Nat.card N := fun h => hpG (h.trans (card_subgroup_dvd_card N))
  -- `[N, φ] = N`
  have hcommN : commSub ψ = ⊤ := by
    have hle : N ≤ (commSub ψ).map N.subtype := by
      refine (closure_le _).2 ?_
      rintro _ ⟨g, rfl⟩
      obtain ⟨c, hc, m, hm, rfl⟩ := exists_fixed_mul_commSub hφ hpG g
      refine ⟨(⟨m, hm⟩ : N)⁻¹ * ψ ⟨m, hm⟩, inv_mul_mem_commSub ψ _, ?_⟩
      have hc' : φ c = c := hc
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, restrictAut_apply, ψ]
      rw [map_mul, hc']; group
    rw [eq_top_iff]
    intro n _
    obtain ⟨m, hm, hmn⟩ := hle n.2
    rwa [show n = m from Subtype.ext hmn.symm]
  -- `C_N(φ) ≅ N ∩ C_G(φ)`, normal in `C_G(φ)`
  have hC : NonsolubleLengthLE (fixedSub ψ) l := by
    have h1 := NonsolubleLengthLE.of_normal (N.subgroupOf (fixedSub φ)) hl
    refine NonsolubleLengthLE.of_mulEquiv ((equivOfMapSubtype (subgroupOf_map_subtype _ _)).trans
      (equivOfMapSubtype (L := N ⊓ fixedSub φ) ?_).symm) h1
    ext x
    simp only [mem_map, Subgroup.coe_subtype, mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by
        have : ψ y = y := hy
        have := congrArg Subtype.val this
        rwa [restrictAut_apply] at this⟩
    · rintro ⟨hxN, hxC⟩
      exact ⟨⟨x, hxN⟩, Subtype.ext (by rw [restrictAut_apply]; exact hxC), rfl⟩
  have hN' := nonsolubleLengthLE_of_commSub_eq_top hCFSG hψ hpN hcommN hC
  -- `G/N` is an image of `C_G(φ)`
  have hQ : NonsolubleLengthLE (G ⧸ N) l := by
    refine NonsolubleLengthLE.of_surjective (f := (QuotientGroup.mk' N).comp (fixedSub φ).subtype)
      ?_ hl
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_fixed_mul_commSub hφ hpG g
    refine ⟨⟨c, hc⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using hn
  have := NonsolubleLengthLE.extension N hN' hQ
  rwa [show l + 1 + l = 2 * l + 1 by ring] at this

end Prime

section General

/-- A nontrivial finite soluble group has a normal subgroup of prime index. -/
lemma exists_normal_index_prime {A : Type*} [Group A] [Finite A] [Group.IsSolvable A]
    [Nontrivial A] : ∃ A0 : Subgroup A, A0.Normal ∧ A0.index.Prime := by
  have hne : commutator A ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := A)
    have : ∀ k, derivedSeries A k = ⊤ := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, h]
    exact bot_ne_top (hn.symm.trans (this n))
  have hsurj : Function.Surjective (Abelianization.of (G := A)) := QuotientGroup.mk_surjective
  haveI : Nontrivial (Abelianization A) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hne
    rw [eq_top_iff]
    intro x _
    have : (Abelianization.of x : Abelianization A) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).1 this
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := Abelianization A)).ne'
  obtain ⟨K, hKi, hKn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hqd
  refine ⟨K.comap Abelianization.of, inferInstance, ?_⟩
  rw [index_comap_of_surjective _ hsurj, hKi]
  exact hq

open ArithmeticFunction in
/-- **Theorem 1.3 (Khukhro–Shumyatsky)**, in the form `λ(G) ≤ 2^{Ω(|A|)} (λ(C_G(A)) + 1) - 1`. -/
theorem nonsolubleLengthLE_of_coprime_action_aux [OddOrder.{0}] [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    (n : ℕ) : ∀ {G : Type} [Group G] [Finite G] {A : Type} [Group A] [Finite A]
      (α : A →* MulAut G), Nat.card A = n → Nat.Coprime (Nat.card A) (Nat.card G) →
      ∀ l, NonsolubleLengthLE (fixA α) l →
        NonsolubleLengthLE G (2 ^ cardFactors (Nat.card A) * (l + 1) - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ A _ _ α hn hcop l hl
  by_cases hGs : Group.IsSolvable G
  · exact NonsolubleLengthLE.mono (Nat.zero_le _)
      nonsolubleLengthLE_zero_of_isSolvable
  have h2G : 2 ∣ Nat.card G := by
    by_contra h
    exact hGs (OddOrder.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)))
  haveI : Group.IsSolvable A := by
    refine OddOrder.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => ?_))
    have := Nat.dvd_gcd h h2G
    rw [hcop.gcd_eq_one] at this
    omega
  by_cases hA : Nontrivial A
  · obtain ⟨A0, hA0n, hq⟩ := exists_normal_index_prime (A := A)
    set q := A0.index with hqdef
    haveI : Fact q.Prime := ⟨hq⟩
    have hco : IsCoatom A0 := isCoatom_of_index_prime hq
    obtain ⟨a, ha⟩ : ∃ a, a ∉ A0 := by
      by_contra h
      push Not at h
      exact hco.1 (eq_top_iff.2 fun x _ => h x)
    have haq : a ^ q ∈ A0 := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hqdef, Subgroup.index]
      exact pow_card_eq_one'
    have hcard : Nat.card A = Nat.card A0 * q := (card_mul_index A0).symm
    set α0 := α.comp A0.subtype
    set G' := fixA α0
    have hinv : IsInv (α a) G' := isInv_of_forall fun g hg b => by
      have hb : a⁻¹ * b * a ∈ A0 := by
        simpa using hA0n.conj_mem _ b.2 a⁻¹
      have : α b (α a g) = α a (α (a⁻¹ * b * a) g) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
        congr 2; group
      show α b (α a g) = α a g
      rw [this]
      congr 1
      exact hg ⟨_, hb⟩
    set φ := restrictAut (α a) G' hinv
    have hφ : φ ^ q = 1 := by
      ext x
      rw [restrictAut_pow_apply, ← map_pow]
      exact x.2 ⟨_, haq⟩
    have hqG' : ¬ q ∣ Nat.card G' := by
      intro h
      have h1 : q ∣ Nat.card A := ⟨Nat.card A0, by rw [hcard, mul_comm]⟩
      have := Nat.dvd_gcd h1 (h.trans (card_subgroup_dvd_card G'))
      rw [hcop.gcd_eq_one] at this
      exact hq.one_lt.ne' (Nat.dvd_one.1 this)
    have hfix : (fixedSub φ).map G'.subtype = fixA α := by
      ext g
      simp only [mem_map, Subgroup.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hya : α a y = y := congrArg Subtype.val hy
        intro b
        let St : Subgroup A := (MulAction.stabilizer (MulAut G) (y : G)).comap α
        have hSt : A0 ≤ St := fun c hc => by
          show α c • (y : G) = y
          exact y.2 ⟨c, hc⟩
        have haSt : a ∈ St := hya
        have htop : St = ⊤ := hco.2 St (lt_of_le_of_ne hSt fun h => ha (h ▸ haSt))
        have hb : b ∈ St := htop ▸ mem_top b
        exact hb
      · intro hg
        refine ⟨⟨g, fun b => hg b⟩, Subtype.ext (hg a), rfl⟩
    have hl' : NonsolubleLengthLE (fixedSub φ) l :=
      NonsolubleLengthLE.of_mulEquiv (equivOfMapSubtype hfix).symm hl
    have hG' := nonsolubleLengthLE_of_prime hCFSG hφ hqG' hl'
    have hlt : Nat.card A0 < n := by
      rw [← hn, hcard]
      have := Nat.card_pos (α := A0)
      have := hq.two_le
      nlinarith
    have hcop0 : Nat.Coprime (Nat.card A0) (Nat.card G) :=
      Nat.Coprime.coprime_dvd_left (card_subgroup_dvd_card A0) hcop
    have := ih _ hlt α0 rfl hcop0 (2 * l + 1) hG'
    have hΩ : cardFactors (Nat.card A) = cardFactors (Nat.card A0) + 1 := by
      rw [hcard, cardFactors_mul Nat.card_pos.ne' hq.ne_zero, cardFactors_apply_prime hq]
    rw [hΩ, pow_succ]
    convert this using 2
    ring
  · rw [not_nontrivial_iff_subsingleton] at hA
    have htop : fixA α = ⊤ := by
      rw [eq_top_iff]
      intro g _ b
      rw [Subsingleton.elim b 1, map_one, MulAut.one_apply]
    have hl0 := NonsolubleLengthLE.of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hl
    rw [Nat.card_unique, cardFactors_one, pow_zero, one_mul, Nat.add_sub_cancel]
    exact hl0

end General

section MainTheorem

open ArithmeticFunction

lemma nonsolubleLengthLE_nonsolubleLength {X : Type} [Group X] [Finite X] :
    NonsolubleLengthLE X (nonsolubleLength X) :=
  Nat.sInf_mem (let ⟨l, hl⟩ := exists_upperSeries_eq_top (X := X)
    ⟨l, nonsolubleLengthLE_iff_upperSeries.2 hl⟩)

variable [hodd : OddOrder.{0}] [hsch : Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
include hodd hsch hCFSG

/-- **Theorem 1.3 (Khukhro–Shumyatsky, Proc. AMS 2015).**  If a finite group `A` acts on a
finite group `G` by automorphisms and `(|A|, |G|) = 1`, then
`λ(G) ≤ 2^{α(|A|)} (λ(C_G(A)) + 1) - 1`, where `α(n) = Ω(n)` is the number of prime factors
of `n` counted with multiplicity. -/
theorem nonsolubleLengthLE_of_coprime_action {G A : Type} [Group G] [Finite G] [Group A]
    [Finite A] (α : A →* MulAut G) (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) {l : ℕ}
    (hl : NonsolubleLengthLE (fixA α) l) :
    NonsolubleLengthLE G (2 ^ cardFactors (Nat.card A) * (l + 1) - 1) :=
  nonsolubleLengthLE_of_coprime_action_aux hCFSG _ α rfl hcop l hl

/-- **Length and fixed points.** If a finite group A acts by automorphisms on a finite group G of coprime order, then
λ(G) ≤ 2^α(|A|)·(λ(C_G(A)) + 1) − 1, where λ is nonsoluble length and α(n) is the number of prime factors of n
counted with multiplicity. If φ is an automorphism of G of prime order p not dividing |G|, then λ(G) ≤ 2λ(C_G(φ)) +
1, and λ(G) ≤ λ(C_G(φ)) + 1 when G = [G, φ].

Source: E. I. Khukhro and P. Shumyatsky, On the length of finite groups and of fixed points, Proc. Amer. Math. Soc.
143 (2015), 3781–3790, Theorem 1.3 and Proposition 3.2. https://arxiv.org/abs/1405.1946

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem nonsolubleLength_le_of_coprime_action {G A : Type} [Group G] [Finite G] [Group A]
    [Finite A] (α : A →* MulAut G) (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    nonsolubleLength G ≤ 2 ^ cardFactors (Nat.card A) * (nonsolubleLength (fixA α) + 1) - 1 :=
  Nat.sInf_le (nonsolubleLengthLE_of_coprime_action hCFSG α hcop
    nonsolubleLengthLE_nonsolubleLength)

/-- **Proposition 3.2**, numerical form: for `φ` of prime order coprime to `|G|` with
`G = [G, φ]`, `λ(G) ≤ λ(C_G(φ)) + 1`. -/
theorem nonsolubleLength_le_of_commSub_eq_top {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {φ : MulAut G} (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)
    (hcomm : commSub φ = ⊤) : nonsolubleLength G ≤ nonsolubleLength (fixedSub φ) + 1 :=
  Nat.sInf_le (nonsolubleLengthLE_of_commSub_eq_top hCFSG hφ hpG hcomm
    nonsolubleLengthLE_nonsolubleLength)

/-- The prime-order case of Theorem 1.3, numerical form: `λ(G) ≤ 2 λ(C_G(φ)) + 1`. -/
theorem nonsolubleLength_le_of_prime {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {φ : MulAut G} (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) :
    nonsolubleLength G ≤ 2 * nonsolubleLength (fixedSub φ) + 1 :=
  Nat.sInf_le (nonsolubleLengthLE_of_prime hCFSG hφ hpG nonsolubleLengthLE_nonsolubleLength)

end MainTheorem

end CFSGOutside.KhukhroShumyatskyFixedPointLength
