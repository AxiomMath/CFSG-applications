import CFSGOutside.Corpus.Schreier
import CFSGOutside.Wilson.Lemma4

/-!
# Wilson, compact torsion groups: Theorem 2\*

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66
(EuDML 178137), Theorem 2\* (p. 62).

**Theorem 2\*.** *Let `p` be a prime and `K` a normal subgroup of a finite group `H`. If a Sylow `p`-subgroup `Q` of
`K` has a coset `tQ` in `H` of exponent dividing `p^a`, then `K` has a series `1 = K₀ ≤ K₁ ≤ ⋯ ≤ K_{2a+1} = K` such
that `K_i/K_{i-1}` is `p`-soluble for `i` odd and is a direct product of non-abelian simple groups of order
divisible by `p` for `i` even.*

`wilson_theorem2star` is the statement with `tQ = {t q : q ∈ Q}`, "exponent dividing `p^a`" read as
`∀ q ∈ Q, (t q)^(p^a) = 1`, "`p`-soluble" as `CFSGOutside.Corpus.IsPSolvable p` and "direct product of nonabelian
simple groups of order divisible by `p`" as `IsSpProd p`. The series consists of subgroups normal in `H` (stronger
than the paper's "series"). The proof is the paper's induction on `a` (`exists_wilsonSeries`): for the step, Lemma 4
(`lemma4`) gives `1 ≤ K₁ ≤ K₂ ≤ K ∩ N` for the normal closure `N` of the elements `(tq)^(p^a)`, the induction
hypothesis in `H/N` is pulled back to `H` (`pSolFactor_comap`, `spFactor_comap`) and the soluble factor
`(K ∩ N)/K₂` is merged into the next `p`-soluble factor (`pSolFactor_trans`).

The classification of finite simple groups enters as the hypothesis `hCFSG`, only through the Schreier conjecture
(`CFSGOutside.Corpus.Schreier`) used in `lemma4`.
-/

namespace CFSGOutside.Wilson

open Subgroup CFSGOutside.Corpus

section Theorem2Star

variable {p : ℕ} [hp : Fact p.Prime]

/-- The conclusion of Theorem 2*: a series `1 = K₀ ≤ K₁ ≤ ⋯ ≤ K_{2a+1} = K` of normal
subgroups of `H` whose factors `K_{2i+1}/K_{2i}` are `p`-soluble and whose factors
`K_{2i+2}/K_{2i+1}` are direct products of nonabelian simple groups of order divisible by `p`. -/
def WilsonSeries (p : ℕ) {H : Type} [Group H] (K : Subgroup H) (a : ℕ) : Prop :=
  ∃ S : ℕ → Subgroup H, S 0 = ⊥ ∧ S (2 * a + 1) = K ∧ (∀ i, (S i).Normal) ∧
    (∀ i < 2 * a + 1, S i ≤ S (i + 1)) ∧
    (∀ i ≤ a, PSolFactor p (S (2 * i)) (S (2 * i + 1))) ∧
    (∀ i < a, SpFactor p (S (2 * i + 1)) (S (2 * i + 2)))

theorem le_of_series {H : Type} [Group H] {S : ℕ → Subgroup H} {n : ℕ}
    (hmono : ∀ i < n, S i ≤ S (i + 1)) : ∀ i ≤ n, S i ≤ S n := by
  intro i hi
  induction n with
  | zero => rw [Nat.le_zero.mp hi]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact (ih (fun j hj => hmono j (by omega)) (by omega)).trans (hmono n (by omega))
    · rw [h]

theorem pSolFactor_bot {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (h : IsPSolvable p K) : PSolFactor p ⊥ K :=
  ⟨inferInstance, isPSolvable_quotient h _⟩

theorem pSolFactor_of_solFactor {H : Type} [Group H] [Finite H] {A B : Subgroup H}
    (h : SolFactor A B) : PSolFactor p A B := by
  obtain ⟨_, h⟩ := h
  exact ⟨inferInstance, isPSolvable_of_isSolvable h⟩

theorem pSolFactor_comap {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']
    (π : H →* H') (K : Subgroup H) {A B : Subgroup H'} (hAB : A ≤ B) (hBK : B ≤ K.map π)
    (h : PSolFactor p A B) : PSolFactor p (K ⊓ A.comap π) (K ⊓ B.comap π) := by
  obtain ⟨_, h⟩ := h
  obtain ⟨hn, ⟨e⟩⟩ := section_comap π K hAB hBK
  exact ⟨hn, isPSolvable_of_mulEquiv e.symm h⟩

theorem spFactor_comap {H H' : Type} [Group H] [Group H'] (π : H →* H') (K : Subgroup H)
    {A B : Subgroup H'} (hAB : A ≤ B) (hBK : B ≤ K.map π)
    (h : SpFactor p A B) : SpFactor p (K ⊓ A.comap π) (K ⊓ B.comap π) := by
  obtain ⟨_, h⟩ := h
  obtain ⟨hn, ⟨e⟩⟩ := section_comap π K hAB hBK
  exact ⟨hn, IsSpProd.of_equiv e h⟩

/-- **Theorem 2\* of Wilson.** -/
theorem exists_wilsonSeries [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) :
    ∀ (a : ℕ) {H : Type} [Group H] [Finite H] {K : Subgroup H} [K.Normal] (Q : Sylow p K)
      (t : H), (∀ q ∈ Q, (t * (q : H)) ^ (p ^ a) = 1) → WilsonSeries p K a := by
  intro a
  induction a with
  | zero =>
    intro H _ _ K _ Q t hexp
    simp only [pow_zero, pow_one] at hexp
    have ht : t = 1 := by simpa using hexp 1 Q.one_mem
    have hQ : (Q : Subgroup K) = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      have := hexp q hq
      rw [ht, one_mul] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    have hcop : Nat.Coprime p (Nat.card K) := by
      have h1 := Q.card_eq_multiplicity
      rw [hQ, Subgroup.card_bot] at h1
      refine (Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun hdvd => ?_
      have h2 : (Nat.card K).factorization p ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd hp.out Nat.card_pos.ne' hdvd).ne'
      have h3 := (Nat.pow_eq_one).mp h1.symm
      rcases h3 with h3 | h3
      · exact hp.out.one_lt.ne' h3
      · exact h2 h3
    refine ⟨fun i => if i = 0 then ⊥ else K, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · intro i; dsimp only; split_ifs <;> infer_instance
    · intro i hi; dsimp only; split_ifs <;> simp_all
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [mul_zero, zero_add, if_true, one_ne_zero, if_false]
      exact pSolFactor_bot (isPSolvable_of_coprime hcop)
    · intro i hi; omega
  | succ a ih =>
    intro H _ _ K hKn Q t hexp
    classical
    obtain ⟨K₁, K₂, hK₁n, hK₂n, hK₁₂, hK₂X, hK₁p, hsp, hsol⟩ := lemma4 hCFSG Q t a hexp
    set Aset : Set H := {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)}
    set N := normalClosure Aset
    set π := QuotientGroup.mk' N
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
    set Kb := K.map π
    have hKbn : Kb.Normal := hKn.map π hπ
    let Qb : Sylow p Kb := Q.mapSurjective (π.subgroupMap_surjective K)
    have hexpb : ∀ q ∈ Qb, (π t * (q : H ⧸ N)) ^ (p ^ a) = 1 := by
      intro qb hqb
      obtain ⟨q, hq, rfl⟩ := mem_map.mp hqb
      show (π t * π q) ^ (p ^ a) = 1
      rw [← map_mul, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (subset_normalClosure ⟨q, hq, rfl⟩)
    obtain ⟨L, hL0, hLtop, hLn, hLmono, hLp, hLs⟩ := ih Qb (π t) hexpb
    have hLK : ∀ i ≤ 2 * a + 1, L i ≤ Kb := fun i hi => hLtop ▸ le_of_series hLmono i hi
    have hcomap0 : L 0 = ⊥ := hL0
    have hNle : ∀ i, N ≤ (L i).comap π := fun i n hn => by
      show π n ∈ L i
      rw [show π n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]; exact one_mem _
    have hX : K ⊓ (L 0).comap π = K ⊓ N := by
      rw [hL0, MonoidHom.comap_bot, QuotientGroup.ker_mk']

    let S : ℕ → Subgroup H := fun i =>
      if i = 0 then ⊥ else if i = 1 then K₁ else if i = 2 then K₂ else K ⊓ (L (i - 2)).comap π
    have hS3 : ∀ i, 3 ≤ i → S i = K ⊓ (L (i - 2)).comap π := by
      intro i hi
      simp only [S]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    refine ⟨S, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS3 _ (by omega), show 2 * (a + 1) + 1 - 2 = 2 * a + 1 by omega, hLtop]
      exact inf_eq_left.mpr (Subgroup.le_comap_map π K)
    · intro i
      simp only [S]
      split_ifs
      · infer_instance
      · exact hK₁n
      · exact hK₂n
      · exact Subgroup.normal_inf_normal _ _
    · intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | h3
      · simp [S]
      · simpa [S] using hK₁₂
      · simp only [S, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, if_true,
          if_false, show 2 + 1 - 2 = 1 by omega]
        exact hK₂X.trans (inf_le_inf_left _ (hNle 1))
      · rw [hS3 i h3, hS3 (i + 1) (by omega)]
        refine inf_le_inf_left _ (Subgroup.comap_mono ?_)
        rw [show i + 1 - 2 = (i - 2) + 1 by omega]
        exact hLmono _ (by omega)
    · intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h2
      · simp only [S, mul_zero, zero_add, if_true, one_ne_zero, if_false]
        exact pSolFactor_bot hK₁p
      · -- the soluble factor `(K ∩ N)/K₂` merges with the first factor from `H/N`
        simp only [S, show 2 * 1 = 2 by rfl, show (2 : ℕ) ≠ 0 by omega,
          show (2 : ℕ) ≠ 1 by omega, if_true, if_false, show 2 + 1 = 3 by rfl,
          show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
          show 3 - 2 = 1 by rfl]
        have h1 := pSolFactor_comap π K (hLmono 0 (by omega)) (hLK 1 (by omega))
          (by simpa using hLp 0 (by omega))
        rw [hX] at h1
        haveI : (K ⊓ N).Normal := Subgroup.normal_inf_normal K N
        exact pSolFactor_trans hK₂X (inf_le_inf_left _ (hNle 1))
          (pSolFactor_of_solFactor hsol) h1
      · rw [hS3 _ (by omega), hS3 _ (by omega)]
        have h1 := pSolFactor_comap π K (hLmono (2 * (i - 1)) (by omega))
          (hLK (2 * (i - 1) + 1) (by omega)) (hLp (i - 1) (by omega))
        rw [show 2 * i - 2 = 2 * (i - 1) by omega, show 2 * i + 1 - 2 = 2 * (i - 1) + 1 by omega]
        exact h1
    · intro i hi
      rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | h1
      · simpa [S] using hsp
      · rw [hS3 _ (by omega), hS3 _ (by omega)]
        have h2 := spFactor_comap π K (hLmono (2 * (i - 1) + 1) (by omega))
          (hLK (2 * (i - 1) + 2) (by omega)) (hLs (i - 1) (by omega))
        rw [show 2 * i + 1 - 2 = 2 * (i - 1) + 1 by omega,
          show 2 * i + 2 - 2 = 2 * (i - 1) + 2 by omega]
        exact h2

end Theorem2Star

/-- **Compact torsion groups.** Let p be a prime, H a finite group, K a normal subgroup of H, Q a Sylow p-subgroup of K,
and t ∈ H with (tq)^(p^a) = 1 for every q ∈ Q. Then K has a series 1 = K₀ ≤ K₁ ≤ ⋯ ≤ K_{2a+1} = K of subgroups
normal in H in which K_{2i+1}/K_{2i} is p-soluble and K_{2i+2}/K_{2i+1} is a direct product of nonabelian simple
groups of order divisible by p. If instead (tq)^(p^(a+1)) = 1 for all q ∈ Q and N is the normal closure in H of the
elements (tq)^(p^a), there are subgroups K₁ ≤ K₂ ≤ K ∩ N, normal in H, with K₁ p-soluble, K₂/K₁ a direct product of
nonabelian simple groups of order divisible by p, and (K ∩ N)/K₂ soluble.

Source: J. S. Wilson, On the structure of compact torsion groups, Monatsh. Math. 96 (1983), 57–66, Theorem 2* and
Lemma 4(ii). https://eudml.org/doc/178137

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem wilson_theorem2star [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {p : ℕ}
    [Fact p.Prime] {H : Type} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    (Q : Sylow p K) (t : H) (a : ℕ) (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ a) = 1) :
    ∃ S : ℕ → Subgroup H, S 0 = ⊥ ∧ S (2 * a + 1) = K ∧ (∀ i, (S i).Normal) ∧
      (∀ i < 2 * a + 1, S i ≤ S (i + 1)) ∧
      (∀ i ≤ a, ∃ _ : ((S (2 * i)).subgroupOf (S (2 * i + 1))).Normal,
        IsPSolvable p (S (2 * i + 1) ⧸ (S (2 * i)).subgroupOf (S (2 * i + 1)))) ∧
      (∀ i < a, ∃ _ : ((S (2 * i + 1)).subgroupOf (S (2 * i + 2))).Normal,
        IsSpProd p (S (2 * i + 2) ⧸ (S (2 * i + 1)).subgroupOf (S (2 * i + 2)))) :=
  exists_wilsonSeries hCFSG a Q t hexp

end CFSGOutside.Wilson
