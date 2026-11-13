import CFSGOutside.MaWallsWangZhou.CodePerfect
import CFSGOutside.Corpus.WalterSplit
import CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutside.Corpus.ElementaryOfClauses

/-!
# Ma-Walls-Wang-Zhou (2020): Theorem 1.1 and the simple code-perfect groups

X. Ma, G. L. Walls, K. Wang, S. Zhou, *Subgroup perfect codes in Cayley graphs*, SIAM J. Discrete Math. 34
(2020) 1909-1921, DOI 10.1137/19m1258013. Theorem 1.1 is proved without the corpus. Corollary 1.4 (simple
code-perfect groups) is conditional on Walter's theorem and the order of the Ree groups, stated as classes in
`CFSGOutside.Corpus`. The Ree group `²G₂(3^f)`, `J₁` and the order `|²G₂(q)|` are the copies of the corpus
definitions in `CFSGOutside.Corpus.Open` and `CFSGOutside.Corpus.Blueprint`.
-/

namespace CFSGOutside.MaWallsWangZhou

open Matrix
open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.Blueprint
open scoped MatrixGroups

/-- **Perfect codes in Cayley graphs.** Call a finite group G code-perfect if every subgroup H is a perfect code in some
Cayley graph Cay(G, S) with S inverse-closed and 1 ∉ S, that is, H is independent and every vertex outside H is
adjacent to exactly one vertex of H. A finite group is code-perfect if and only if it has no element of order 4. A
finite simple group is code-perfect if and only if it is cyclic of prime order, PSL(2, 2^e) with e ≥ 2, PSL(2, q)
with q ≡ ±3 (mod 8) and q ≥ 5, the Ree group ²G₂(3^f) with f odd and f ≥ 3, or J₁.

Source: X. Ma, G. L. Walls, K. Wang, S. Zhou, Subgroup perfect codes in Cayley graphs, SIAM J. Discrete Math. 34
(2020), 1909–1921, Theorem 1.1 and Corollary 1.4. https://doi.org/10.1137/19m1258013

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem codePerfect_iff (G : Type*) [Group G] [Finite G] :
    CodePerfect G ↔ ∀ g : G, orderOf g ≠ 4 := by
  constructor
  · intro h g hg
    exact not_isPerfectCodeOf_of_orderOf_eq_four hg (h _)
  · intro h H
    haveI := Fintype.ofFinite G
    obtain ⟨T, h1, hinv, huniq⟩ := exists_transversal (H := H) h
    exact isPerfectCodeOf_of_transversal H T h1 hinv huniq

lemma orderOf_ne_four_of_mulEquiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (h : ∀ k : K, orderOf k ≠ 4) (g : G) : orderOf g ≠ 4 := by
  rw [← MulEquiv.orderOf_eq e]; exact h _

/-- In a finite group whose Sylow 2-subgroups have exponent 2 there is no element of order 4. -/
lemma orderOf_ne_four_of_sylow {K : Type*} [Group K] [Finite K]
    (h : ∀ T : Sylow 2 K, ∀ t ∈ (T : Subgroup K), t ^ 2 = 1) (g : K) : orderOf g ≠ 4 := by
  intro hg
  have hp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have := h T g (hT (Subgroup.mem_zpowers g))
  have := orderOf_le_of_pow_eq_one (by norm_num) this
  omega

/-- 2×2 matrices over a field of characteristic 2 with determinant 1: `M⁴ = 1 → M² = 1`. -/
lemma sq_eq_one_of_pow_four {F : Type*} [Field F] [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (h4 : M ^ 4 = 1) : M ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set t := M.trace
  have hCH : M * M = t • M + 1 := by
    have : M * M = t • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two, t] <;>
        ring
    rw [this, hdet, one_smul, sub_eq_add_neg, CharTwo.neg_eq]
  have hM4 : M ^ 4 = (t ^ 3) • M + (t ^ 2 + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e0 : M ^ 4 = (M * M) * (M * M) := by rw [show 4 = 2 + 2 from rfl, pow_add, sq]
    have e1 : (t • M + 1) * (t • M + 1) = (t * t) • (M * M) + (2 * t) • M + 1 := by
      rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, mul_one, one_mul, one_mul]
      module
    rw [e0, hCH, e1, h2, zero_mul, zero_smul, add_zero, hCH]
    module
  have htr : t ^ 4 = 0 := by
    have := congrArg Matrix.trace (h4.symm.trans hM4)
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul] at this
    rw [show ((2 : ℕ) : F) = 0 by exact_mod_cast h2] at this
    linear_combination -this
  have ht : t = 0 := pow_eq_zero_iff (by norm_num) |>.mp htr
  rw [sq, hCH, ht, zero_smul, zero_add]

/-- `PSL(2, F)`, `F` of characteristic 2, has no element of order 4. -/
lemma psl2_charTwo_orderOf_ne_four {F : Type*} [Field F] [CharP F 2] (x : PSL(2, F)) :
    orderOf x ≠ 4 := by
  intro hx
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have hx4 : ((A ^ 4 : SL(2, F)) : PSL(2, F)) = 1 := by
    rw [QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
  rw [QuotientGroup.eq_one_iff] at hx4
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx4
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hA4 : (A : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hrA, hr1, map_one]
  have hA2 := sq_eq_one_of_pow_four (A : Matrix (Fin 2) (Fin 2) F) A.2 hA4
  have : ((A : PSL(2, F))) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : A ^ 2 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, hA2]; rfl)
    rw [this, QuotientGroup.mk_one]
  have := orderOf_le_of_pow_eq_one (by norm_num) this
  omega

lemma walterJ1_eq_goldschmidtJ1 : walterJ1 = goldschmidtJ1 := rfl

/-- Walter's theorem with the Ree case as an order: a finite nonabelian simple group with an abelian
Sylow 2-subgroup is `PSL(2, 2^f)`, `PSL(2, q)` with `q ≡ ±3 (mod 8)`, of Ree order, or `J₁`. -/
lemma walter_order_form [WalterSplit] [CardOfReeTitsModelTwistedG2]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = ordRee (3 ^ (2 * m + 1))) ∨
    Nonempty (G ≃* walterJ1) := by
  rcases WalterSplit.walter_split G hnonab P hP with h | h | ⟨f, -, -, hR⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨-, a, ha, hfa, hcard⟩ := CardOfReeTitsModelTwistedG2.card_of_reeTitsModel_twistedG2 hR
    exact Or.inr (Or.inr (Or.inl ⟨a, ha, hfa ▸ hcard⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **Corollary 1.4.** *A (finite) simple group is code-perfect if and only if it is isomorphic to
(a) a cyclic group of prime order; (b) `PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`,
`q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group `²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

As in the corpus's statement of Walter's theorem, (d) is expressed by the order
`|G| = |²G₂(3^(2n+1))|`, and `J₁` is the copy of the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem simple_codePerfect_iff [WalterSplit] [CardOfReeTitsModelTwistedG2] [ElementaryOfClauses]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nat.card G = ordRee (3 ^ (2 * n + 1))) ∨
      Nonempty (G ≃* walterJ1) := by
  rw [codePerfect_iff]
  constructor
  · intro hno4
    by_cases hab : ∀ a b : G, a * b = b * a
    · -- abelian: cyclic of prime order
      left
      letI : CommGroup G := { ‹Group G› with mul_comm := hab }
      have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
      haveI : Fact (Nat.card G).Prime := ⟨hp⟩
      refine ⟨Nat.card G, hp, ⟨mulEquivOfPrimeCardEq (p := Nat.card G) rfl ?_⟩⟩
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    · push Not at hab
      right
      obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
      have hsq : ∀ y ∈ (P : Subgroup G), y ^ 2 = 1 := by
        intro y hy
        obtain ⟨k, hk⟩ := (P.isPGroup' ⟨y, hy⟩)
        have hdvd : orderOf y ∣ 2 ^ k := by
          rw [← Subgroup.orderOf_mk y hy]; exact orderOf_dvd_of_pow_eq_one hk
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        have hi1 : i ≤ 1 := by
          by_contra hi2
          have h4 : 4 ∣ orderOf y := by
            rw [hi]; exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ i))
          exact hno4 _ (orderOf_pow_orderOf_div (orderOf_pos y).ne' h4)
        rw [← orderOf_dvd_iff_pow_eq_one, hi]
        exact Nat.pow_dvd_pow 2 hi1
      have hcomm : IsMulCommutative (P : Subgroup G) :=
        ⟨⟨fun a b => Subtype.ext (by
          have hab := hsq _ ((P : Subgroup G).mul_mem a.2 b.2)
          have ha2 := hsq _ a.2
          have hb2 := hsq _ b.2
          rw [sq] at hab ha2 hb2
          change (a : G) * b = b * a
          rw [mul_eq_one_iff_eq_inv.mp hab, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ha2,
            inv_eq_of_mul_eq_one_right hb2])⟩⟩
      obtain ⟨a, b, hab'⟩ := hab
      exact walter_order_form G ⟨a, b, hab'⟩ P hcomm
  · rintro (⟨p, hp, ⟨e⟩⟩ | ⟨f, -, ⟨e⟩⟩ | h | h | h) g
    · intro hg
      have hcard : Nat.card G = p := by
        rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]
      have hdvd : orderOf g ∣ p := hcard ▸ orderOf_dvd_natCard g
      rw [hg] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> [omega; (subst h; norm_num at hp)]
    · exact orderOf_ne_four_of_mulEquiv e psl2_charTwo_orderOf_ne_four g
    all_goals
      refine orderOf_ne_four_of_sylow
        (fun T => (ElementaryOfClauses.elementary_of_clauses ?_ T).2.1) g
      first
      | exact Or.inl h
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inr (walterJ1_eq_goldschmidtJ1 ▸ h))

/-- **Corollary 1.4**, with clause (d) as an isomorphism. *A (finite) simple group is
code-perfect if and only if it is isomorphic to (a) a cyclic group of prime order; (b)
`PSL(2, 2^e)`, `e ≥ 2`; (c) `PSL(2, q)`, `q ≡ ±3 (mod 8)`, `q ≥ 5`; (d) a Ree group
`²G₂(3^(2n+1))`, `n ≥ 1`; or (e) `J₁`.*

Clause (d) is `ReeTitsModel G .twistedG2 3 f` with `f = 2n+1` odd and `f ≥ 3`, which means `G`
is isomorphic to the copy of the corpus's model of the small Ree group `²G₂(3^f)`. `J₁` is the copy of
the corpus's matrix group `walterJ1 ≤ GL₇(𝔽₁₁)`. -/
theorem simple_codePerfect_iff_ree [WalterSplit] [CardOfReeTitsModelTwistedG2] [ElementaryOfClauses]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    CodePerfect G ↔
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      (∃ e : ℕ, 2 ≤ e ∧ Nonempty (G ≃* PSL(2, GaloisField 2 e))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel G .twistedG2 3 f) ∨
      Nonempty (G ≃* walterJ1) := by
  rw [simple_codePerfect_iff]
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · -- a simple group of Ree order: it is not abelian, its Sylow 2-subgroups are elementary
      -- abelian, so Walter's theorem in model form applies
      obtain ⟨n, hn, hcard⟩ := h
      have hT := fun T : Sylow 2 G =>
        ElementaryOfClauses.elementary_of_clauses (Or.inr (Or.inl ⟨n, hn, hcard⟩)) T
      obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
      have hnonab : ∃ a b : G, a * b ≠ b * a := by
        by_contra hc
        push Not at hc
        letI : CommGroup G := { ‹Group G› with mul_comm := hc }
        have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
        rw [hcard] at hp
        have h3 : 3 ∣ ordRee (3 ^ (2 * n + 1)) :=
          Dvd.dvd.mul_right (Dvd.dvd.mul_right
            (dvd_pow (dvd_pow_self 3 (by omega)) (by norm_num)) _) _
        have h3' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
        have hge : 3 ^ 3 * (3 ^ 3 + 1) * (3 - 1) ≤ ordRee (3 ^ (2 * n + 1)) := by
          have hq : 3 ≤ 3 ^ (2 * n + 1) := Nat.le_self_pow (by omega) 3
          unfold ordRee
          gcongr
        omega
      rcases WalterSplit.walter_split G hnonab P (hT P).1 with h1 | h1 | h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | ⟨f, -, -, hR⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨-, a, ha, hfa, hcard⟩ := CardOfReeTitsModelTwistedG2.card_of_reeTitsModel_twistedG2 hR
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, hfa ▸ hcard⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSGOutside.MaWallsWangZhou
