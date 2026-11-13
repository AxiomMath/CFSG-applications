import CFSGOutside.CravenGlesser.Burnside
import CFSGOutside.CravenGlesser.NoSeven
import CFSGOutside.CravenGlesser.GLCard
import CFSGOutside.Corpus.Defs.TwoRank
import CFSGOutside.Corpus.MacWilliamsFourGenerator

/-!
# Craven–Glesser, *Fusion systems on small p-groups*, Lemma 6.11

D. A. Craven and A. Glesser, Trans. Amer. Math. Soc. 364 (2012), 5945–5967,
DOI 10.1090/S0002-9947-2012-05580-2, Lemma 6.11 (p. 5962; `l:no57` in arXiv:1007.1639):

> Let `P` be a finite 2-group of 2-rank 2 with a nontrivial odd-order automorphism `φ`. If `P` has a
> `φ`-invariant maximal subgroup, then `P` is 3-generator or 4-generator and `o(φ) = 3`.

The proof differs from the paper's.
* MacWilliams's theorem (the corpus input `MacWilliamsFourGenerator`) makes `P` at most 4-generator, so
  `V = P/Φ(P)` has dimension at most 4.
* The invariant maximal subgroup gives an invariant hyperplane `H` of `V`, and `φ` acts trivially on `V/H`.
  The order `m` of `φ` on `H` divides `|GL(H)|`, which divides 168 (and is 1 if `dim H ≤ 1`). `φ^{2m}` acts
  trivially on `V`, so `φ^{2m} = 1` by Burnside's theorem (`eq_one_of_mem_frattini`). Hence `o(φ)` divides
  `m`, so `o(φ)` divides 21 and `P` is not 1- or 2-generator.
* A 2-group of 2-rank at most 2 has no automorphism of order 7 (`no_aut_order_seven`), so `o(φ) = 3`.
-/

namespace CFSGOutside.CravenGlesser

open Subgroup
open CFSGOutside.Corpus.Open (IsElemAbelian pRank twoRank)

/-- In a finite group of 2-rank 2, elementary abelian 2-subgroups have order at most 4. -/
theorem card_le_four_of_twoRank {P : Type*} [Group P] [Finite P] (hrank : twoRank P = 2)
    (E : Subgroup P) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hpE : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g.1 g.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpE
  have hbdd : BddAbove {k | ∃ E : Subgroup P, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card P, fun j ⟨E', _, _, hj⟩ => ?_⟩
    have h1 : 2 ^ j ≤ Nat.card P := hj ▸ Subgroup.card_le_card_group E'
    have h2 : j < 2 ^ j := Nat.lt_two_pow_self
    omega
  have hle : k ≤ 2 := by
    have := le_csSup hbdd ⟨E, le_top, hE, hk⟩
    rw [twoRank, pRank] at hrank
    omega
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 4 := by norm_num

/-- In a group of order 2, any two nontrivial elements are equal. -/
theorem eq_of_card_two {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 2) {a b : Q} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  by_contra hab
  have h3 : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair hab]
  have := Finset.card_le_univ ({1, a, b} : Finset Q)
  rw [h3, Fintype.card_eq_nat_card, hQ] at this
  omega

/-- **Fusion systems on small 2-groups.** Let P be a finite 2-group of 2-rank 2 and φ a nontrivial automorphism of P of
odd order that leaves some maximal subgroup of P invariant. Then P needs 3 or 4 generators and φ has order 3.

Source: D. A. Craven and A. Glesser, Fusion systems on small p-groups, Trans. Amer. Math. Soc. 364 (2012),
5945–5967, Lemma 6.11. https://doi.org/10.1090/S0002-9947-2012-05580-2

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem lemma_6_11 [Corpus.MacWilliamsFourGenerator] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hrank : twoRank P = 2) (φ : MulAut P) (hφ : φ ≠ 1)
    (hodd : Odd (orderOf φ))
    (hinv : ∃ M : Subgroup P, IsCoatom M ∧ M.map φ.toMonoidHom = M) :
    (Group.rank P = 3 ∨ Group.rank P = 4) ∧ orderOf φ = 3 := by
  classical
  obtain ⟨M, hM, hMφ⟩ := hinv
  have hφM : ∀ x ∈ M, φ x ∈ M := fun x hx => hMφ ▸ mem_map_of_mem φ.toMonoidHom hx
  have hφM' : ∀ x, φ x ∈ M → x ∈ M := by
    intro x hx
    rw [← hMφ] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← φ.injective hyx]; exact hy
  have hE4 := card_le_four_of_twoRank hrank
  -- MacWilliams: `P` is at most 4-generator
  have hE8 : ∀ E : Subgroup P, E.Normal → IsElemAbelian 2 E → Nat.card E ≠ 8 := fun E _ hE h => by
    have := hE4 E hE; omega
  obtain ⟨X, hX4, hXcl⟩ :=
    Corpus.MacWilliamsFourGenerator.cls_connectivity_macwilliams_four_generator P hP hE8 ⊤
  have hrank4 : Group.rank P ≤ 4 := (Group.rank_le hXcl).trans hX4
  -- the Frattini quotient
  haveI : IsElemQuot (frattini P) := isElemQuot_frattini hP
  set N := frattini P
  set V := ElemQuot N
  set T := ElemQuot.induced N φ with hTdef
  have hdimX : Module.finrank (ZMod 2) V ≤ 4 := (ElemQuot.finrank_le_card hXcl).trans hX4
  obtain ⟨S, hScard, hScl⟩ := Group.rank_spec P
  have hdimS : Module.finrank (ZMod 2) V ≤ Group.rank P := hScard ▸ ElemQuot.finrank_le_card hScl
  -- the hyperplane `H = M / Φ(P)`
  let A : AddSubgroup V :=
    { carrier := {v | ∃ m ∈ M, ElemQuot.mk N m = v}
      zero_mem' := ⟨1, one_mem M, ElemQuot.mk_one⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_mem ha hb, ElemQuot.mk_mul a b⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_mem ha, ElemQuot.mk_inv a⟩ }
  let H : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 A
  have hmemH : ∀ v, v ∈ H ↔ ∃ m ∈ M, ElemQuot.mk N m = v := fun v =>
    AddSubgroup.mem_toZModSubmodule 2
  have hTH : ∀ v ∈ H, T v ∈ H := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := (hmemH v).mp hv
    exact (hmemH _).mpr ⟨φ m, hφM m hm, (ElemQuot.induced_mk φ m).symm⟩
  have hHtop : H ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ : ∃ g : P, g ∉ M := by
      by_contra h; push Not at h; exact hM.1 (eq_top_iff.mpr fun g _ => h g)
    obtain ⟨m, hm, hmg⟩ := (hmemH (ElemQuot.mk N g)).mp (htop ▸ Submodule.mem_top)
    have hd : m⁻¹ * g ∈ M := frattini_le_coatom hM (ElemQuot.mk_eq_mk.mp hmg)
    apply hg
    have : g = m * (m⁻¹ * g) := by group
    rw [this]; exact mul_mem hm hd
  -- `φ` acts trivially on `V / H`
  have hTsub : ∀ v, T v - v ∈ H := by
    intro v
    obtain ⟨x, rfl⟩ := ElemQuot.mk_surjective (N := N) v
    refine (hmemH _).mpr ⟨x⁻¹ * φ x, ?_, ?_⟩
    · haveI := normal_of_isCoatom hP hM
      by_cases hx : x ∈ M
      · exact mul_mem (inv_mem hx) (hφM x hx)
      · have hx' : φ x ∉ M := fun h => hx (hφM' x h)
        have hQ := card_quotient_of_isCoatom hP hM
        have := eq_of_card_two hQ (a := (x : P ⧸ M)) (b := (φ x : P ⧸ M))
          (by rwa [Ne, QuotientGroup.eq_one_iff]) (by rwa [Ne, QuotientGroup.eq_one_iff])
        exact QuotientGroup.eq.mp this
    · rw [ElemQuot.mk_mul, ElemQuot.mk_inv, ElemQuot.induced_mk]; abel
  -- the restriction of `T` to `H`
  have hT_n : T ^ orderOf φ = 1 := by
    rw [hTdef, ← ElemQuot.inducedHom_apply, ← map_pow, pow_orderOf_eq_one, map_one]
  set TH := T.restrict hTH
  have hTHpow : ∀ k (h : H), ((TH ^ k) h : V) = (T ^ k) h := by
    intro k h
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change T ((TH ^ k) h : V) = _
      rw [ih, pow_succ', Module.End.mul_apply]
  have hTHunit : IsUnit TH := by
    refine IsUnit.of_pow_eq_one (n := orderOf φ) ?_ (orderOf_pos φ).ne'
    ext h
    rw [hTHpow, hT_n]; rfl
  set m := orderOf TH
  have hm_fix : ∀ h ∈ H, (T ^ m) h = h := by
    intro h hh
    have := hTHpow m ⟨h, hh⟩
    rw [pow_orderOf_eq_one] at this
    exact this.symm
  have hpow_sub : ∀ j v, (T ^ j) v - v ∈ H := by
    intro j v
    induction j with
    | zero => simp
    | succ j ih =>
      have : (T ^ (j + 1)) v - v = T ((T ^ j) v - v) + (T v - v) := by
        rw [pow_succ', Module.End.mul_apply, map_sub]; abel
      rw [this]
      exact H.add_mem (hTH _ ih) (hTsub v)
  have hT2m : T ^ (2 * m) = 1 := by
    ext v
    have hh := hpow_sub m v
    set h := (T ^ m) v - v
    have hv : (T ^ m) v = v + h := by simp only [h]; abel
    rw [Module.End.one_apply, mul_comm, pow_mul, sq, Module.End.mul_apply, hv, map_add,
      hm_fix h hh, hv, add_assoc, add_self_zmod2, add_zero]
  have hφ2m : φ ^ (2 * m) = 1 := by
    apply eq_one_of_mem_frattini hP
    · exact Odd.of_dvd_nat hodd (orderOf_pow_dvd _)
    · apply (ElemQuot.induced_eq_one_iff _).mp
      rw [← ElemQuot.inducedHom_apply, map_pow, ElemQuot.inducedHom_apply, ← hTdef, hT2m]
  have hcop2 : (orderOf φ).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hnm : orderOf φ ∣ m := hcop2.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hφ2m)
  have hHdim : Module.finrank (ZMod 2) H < Module.finrank (ZMod 2) V := Submodule.finrank_lt hHtop
  have hne1 : orderOf φ ≠ 1 := fun h => hφ (orderOf_eq_one_iff.mp h)
  -- `P` is not 1- or 2-generator
  have hrank3 : 3 ≤ Group.rank P := by
    by_contra hlt
    push Not at hlt
    have hHle : Module.finrank (ZMod 2) H ≤ 1 := by omega
    have h1 := orderOf_eq_one_of_finrank_le_one TH hTHunit hHle
    exact hne1 (Nat.dvd_one.mp (h1 ▸ hnm))
  refine ⟨by omega, ?_⟩
  -- `o(φ)` divides 21 and is not divisible by 7
  have hHle3 : Module.finrank (ZMod 2) H ≤ 3 := by omega
  have h168 := orderOf_dvd_of_finrank_le_three TH hTHunit hHle3
  have h21 : orderOf φ ∣ 21 := by
    have : orderOf φ ∣ 21 * 2 ^ 3 := hnm.trans (by simpa using h168)
    exact (Nat.Coprime.pow_right 3 hcop2).dvd_of_dvd_mul_right this
  have h7 : ¬ 7 ∣ orderOf φ := fun h7 =>
    no_aut_order_seven hP hE4 (φ ^ (orderOf φ / 7)) (orderOf_pow_orderOf_div (orderOf_pos φ).ne' h7)
  have hmem : orderOf φ ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨h21, by norm_num⟩
  rw [show Nat.divisors 21 = {1, 3, 7, 21} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h hne1
  · exact h
  · rw [h] at h7; exact absurd (dvd_refl 7) h7
  · rw [h] at h7; exact absurd (by norm_num : 7 ∣ 21) h7

end CFSGOutside.CravenGlesser
