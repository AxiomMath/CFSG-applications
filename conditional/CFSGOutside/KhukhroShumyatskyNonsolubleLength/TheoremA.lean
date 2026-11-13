
import CFSGOutside.KhukhroShumyatskyNonsolubleLength.Statement
import CFSGOutside.Common.UpperNonsolubleSeries

/-!
# Khukhro–Shumyatsky, Theorem 1.1(a), with the paper's literal definitions

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*,
Israel J. Math. **207** (2015), arXiv:1310.2434.

This file is the definitional crosswalk for `CFSG.Applications.NonsolubleLength`.

* `PaperSeries X P`: a normal series `1 = G₀ ≤ G₁ ≤ ⋯ ≤ G_n = X` (every `G_i` normal in `X`, `n`
  arbitrary) all of whose factors `G_{i+1}/G_i` satisfy `P`; `PaperSeries.count s Q` is the number
  of factors that do *not* satisfy `Q`.
* `paperNonsolubleLength X` (§1 of the paper, first sentence of the definition): the minimum number
  of nonsoluble factors in a normal series each of whose factors is soluble or a direct product of
  nonabelian simple groups.
* `paperTwoLength X` (§1, "Recall that…"): the least number of `2`-factors in a normal series each
  of whose factors is a `2`-group or a `2'`-group.  (A trivial factor is both; it is counted as a
  `2'`-factor, which is the only reading under which "least number" is meaningful.)
* `paperMaxTwoLength X`: `L₂`, the maximum of `paperTwoLength H` over soluble subgroups `H`.
* `upperTwoSeries X`: the upper `2`-series `1 ≤ O_{2'}(X) ≤ O_{2',2}(X) ≤ O_{2',2,2'}(X) ≤ ⋯`;
  each term is the largest normal subgroup `N` of `X` above the previous term `U` with `N/U` of odd
  order, resp. a `2`-group (the preimage of `O_{2'}(X/U)`, resp. `O_2(X/U)`).

Crosswalk theorems:
* `paperNonsolubleLength_eq`: `paperNonsolubleLength X = nonsolubleLength X`;
* `paperTwoLength_eq`: `paperTwoLength X = twoLength X`;
* `paperMaxTwoLength_eq`: `paperMaxTwoLength X = maxTwoLength X`;
* `twoLengthLE_iff_upperTwoSeries`: `l₂(X) ≤ l ↔ O_{2',2,…,2'}(X) = X` (`2l+1` steps), so
  `twoLength_eq_upperTwoSeries`: the `2`-length is the number of `2`-steps in the upper `2`-series;
* `paperNonsolubleLength_eq_upperSeries`: `λ(X)` is the number of semisimple steps in the upper
  nonsoluble series `1 ≤ R(X) ≤ … ` (`CFSGOutside.UpperNonsolubleSeries`).

Main results in literal paper terms: `theorem_1_1_a`, `corollary_1_2`.
-/

section

namespace CFSGOutside.KhukhroShumyatskyNonsolubleLength

open Subgroup CFSGOutside.NonsolubleLength

universe u


section Counting

variable {X : Type u} [Group X]

lemma card_filter_Ico_succ (p : ℕ → Prop) [DecidablePred p] {j n : ℕ} (h : j < n) :
    ((Finset.Ico j n).filter p).card =
      ((Finset.Ico (j + 1) n).filter p).card + if p j then 1 else 0 := by
  have hI : Finset.Ico j n = insert j (Finset.Ico (j + 1) n) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hI, Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

open Classical in
/-- Factors `j, j+1, …, n-1` failing `Q`. -/
lemma count_eq {P Q : Subgroup X → Subgroup X → Prop} (s : PaperSeries X P) :
    s.count Q = ((Finset.Ico 0 s.n).filter fun i => ¬ Q (s.G i) (s.G (i + 1))).card := by
  rw [PaperSeries.count, Finset.range_eq_Ico]

end Counting

/-! ### Nonsoluble series with an arbitrary bottom term -/

section NSeriesPrepend

variable {X : Type u} [Group X] [Finite X]

/-- The one-term series `X = G₀ = G₁`. -/
def NSeries.topSeries : NSeries X ⊤ 0 where
  G _ := ⊤
  normal _ := normal_top
  mono _ _ := le_rfl
  zero := rfl
  top := rfl
  sol i _ := solubleFactor_iff.2 ⟨0, le_rfl⟩
  semisimple i hi := absurd hi (Nat.not_lt_zero _)

/-- Prepend a soluble factor `N/M` at the bottom. -/
def NSeries.consSol {M N : Subgroup X} [hM : M.Normal] {h : ℕ} (t : NSeries X N h) (hMN : M ≤ N)
    (hs : SolubleFactor M N) : NSeries X M h where
  G i := match i with
    | 0 => M
    | j + 1 => t.G (j + 1)
  normal i := match i with
    | 0 => hM
    | j + 1 => t.normal (j + 1)
  mono i hi := match i with
    | 0 => hMN.trans (by have := t.mono 0 (by omega); rwa [t.zero] at this)
    | j + 1 => t.mono (j + 1) hi
  zero := rfl
  top := t.top
  sol i hi := match i with
    | 0 => by
      show SolubleFactor M (t.G 1)
      haveI := t.normal 0
      haveI := t.normal 1
      obtain ⟨a, ha⟩ := solubleFactor_iff.1 (t.sol 0 (Nat.zero_le _))
      obtain ⟨b, hb⟩ := solubleFactor_iff.1 hs
      refine solubleFactor_iff.2 ⟨b + a, ?_⟩
      rw [dA_add]
      exact (dA_mono b (ha.trans t.zero.le)).trans hb
    | j + 1 => t.sol (j + 1) hi
  semisimple i hi := t.semisimple i hi

/-- Prepend a semisimple factor `N/M` at the bottom (as `M ≤ M ≤ N`). -/
def NSeries.consSS {M N : Subgroup X} [hM : M.Normal] {h : ℕ} (t : NSeries X N h) (hMN : M ≤ N)
    (hs : SemisimpleFactor M N) : NSeries X M (h + 1) where
  G i := match i with
    | 0 => M
    | 1 => M
    | j + 2 => t.G j
  normal i := match i with
    | 0 => hM
    | 1 => hM
    | j + 2 => t.normal j
  mono i hi := match i with
    | 0 => le_rfl
    | 1 => by show M ≤ t.G 0; rw [t.zero]; exact hMN
    | j + 2 => t.mono j (by omega)
  zero := rfl
  top := t.top
  sol i hi := match i with
    | 0 => solubleFactor_iff.2 ⟨0, le_rfl⟩
    | j + 1 => t.sol j (by omega)
  semisimple i hi := match i with
    | 0 => by show SemisimpleFactor M (t.G 0); rw [t.zero]; exact hs
    | j + 1 => t.semisimple j (by omega)

end NSeriesPrepend

/-! ### Crosswalk for the nonsoluble length -/

lemma sInf_eq_of_bounds {A B : Set ℕ} (h1 : ∀ a ∈ A, ∃ b ∈ B, b ≤ a)
    (h2 : ∀ b ∈ B, ∃ a ∈ A, a ≤ b) : sInf A = sInf B := by
  rcases Set.eq_empty_or_nonempty B with hB | hB
  · have hA : A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun a ha => by
      obtain ⟨b, hb, -⟩ := h1 a ha
      rw [hB] at hb
      exact hb
    rw [hA, hB]
  · obtain ⟨b₀, hb₀⟩ := hB
    obtain ⟨a₀, ha₀, -⟩ := h2 b₀ hb₀
    apply le_antisymm
    · obtain ⟨a, ha, hab⟩ := h2 _ (Nat.sInf_mem ⟨b₀, hb₀⟩)
      exact (Nat.sInf_le ha).trans hab
    · obtain ⟨b, hb, hba⟩ := h1 _ (Nat.sInf_mem ⟨a₀, ha₀⟩)
      exact (Nat.sInf_le hb).trans hba

section NonsolubleCrosswalk

variable {X : Type u} [Group X] [Finite X]

open Classical in
/-- From a paper series, the tail starting at `G_j` is a nonsoluble series with as many
semisimple blocks as there are nonsoluble factors among `G_{i+1}/G_i`, `j ≤ i < n`. -/
lemma nseries_of_paperSeries (s : PaperSeries X SolOrSemisimple) :
    ∀ m j, j + m = s.n → Nonempty (NSeries X (s.G j)
      ((Finset.Ico j s.n).filter fun i => ¬ SolubleFactor (s.G i) (s.G (i + 1))).card) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    subst hj
    simp only [add_zero, Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    rw [s.top]
    exact ⟨NSeries.topSeries⟩
  | succ m ih =>
    intro j hj
    obtain ⟨t⟩ := ih (j + 1) (by omega)
    have hjn : j < s.n := by omega
    rw [card_filter_Ico_succ _ hjn]
    haveI := s.normal j (by omega)
    rcases s.factor j hjn with hsol | hss
    · rw [if_neg (not_not.2 hsol), add_zero]
      exact ⟨NSeries.consSol t (s.mono j hjn) hsol⟩
    · by_cases hsol : SolubleFactor (s.G j) (s.G (j + 1))
      · rw [if_neg (not_not.2 hsol), add_zero]
        exact ⟨NSeries.consSol t (s.mono j hjn) hsol⟩
      · rw [if_pos hsol]
        exact ⟨NSeries.consSS t (s.mono j hjn) hss⟩

lemma nonsolubleLengthLE_of_paperSeries (s : PaperSeries X SolOrSemisimple) :
    NonsolubleLengthLE X (s.count SolubleFactor) := by
  obtain ⟨t⟩ := nseries_of_paperSeries s s.n 0 (by omega)
  rw [count_eq]
  exact ⟨t.cast s.zero⟩

/-- A nonsoluble series of length `h` is a paper series with at most `h` nonsoluble factors. -/
lemma exists_paperSeries_of_nonsolubleLengthLE {h : ℕ} (H : NonsolubleLengthLE X h) :
    ∃ s : PaperSeries X SolOrSemisimple, s.count SolubleFactor ≤ h := by
  classical
  obtain ⟨t⟩ := H
  refine ⟨{ n := 2 * h + 1, G := t.G, normal := fun i _ => t.normal i, mono := t.mono,
            zero := t.zero, top := t.top, factor := fun i hi => ?_ }, ?_⟩
  · rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (by rw [← two_mul]; exact t.sol j (by omega))
    · exact Or.inr (t.semisimple j (by omega))
  · rw [PaperSeries.count]
    refine (Finset.card_le_card (t := (Finset.range h).image fun j => 2 * j + 1) ?_).trans
      Finset.card_image_le |>.trans (by simp)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_image, Finset.mem_range]
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact absurd (by rw [← two_mul]; exact t.sol j (by omega)) hi.2
    · exact ⟨j, by omega, rfl⟩

/-- **Crosswalk.** The paper's nonsoluble length (minimum number of nonsoluble factors over all
normal series with soluble or semisimple factors) equals `nonsolubleLength`, defined with the
alternating series `1 = G₀ ≤ ⋯ ≤ G_{2h+1} = X`. -/
theorem paperNonsolubleLength_eq : paperNonsolubleLength X = nonsolubleLength X := by
  unfold paperNonsolubleLength nonsolubleLength
  apply sInf_eq_of_bounds
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, nonsolubleLengthLE_of_paperSeries s, le_rfl⟩
  · intro h hh
    obtain ⟨s, hs⟩ := exists_paperSeries_of_nonsolubleLengthLE hh
    exact ⟨_, ⟨s, rfl⟩, hs⟩

/-- `λ(X)` is the number of semisimple steps of the upper nonsoluble series
`1 ≤ R(X) = M₁ ≤ L₁ ≤ M₂ ≤ ⋯` (`M_{k+1}/L_k = R(X/L_k)`, `L_k/M_k = E(X/M_k)`). -/
theorem paperNonsolubleLength_eq_upperSeries (G : Type) [Group G] [Finite G] :
    paperNonsolubleLength G =
      sInf {l | UpperNonsolubleSeries.upperSeries G (2 * l + 1) = ⊤} := by
  rw [paperNonsolubleLength_eq, nonsolubleLength]
  congr 1
  ext l
  exact UpperNonsolubleSeries.nonsolubleLengthLE_iff_upperSeries

end NonsolubleCrosswalk

/-! ### Factors through indices -/

section Index

variable {X : Type u} [Group X] [Finite X]

lemma oddOrderFactor_iff {A B : Subgroup X} [A.Normal] :
    OddOrderFactor A B ↔ Odd (A.relIndex B) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨inferInstance, h⟩⟩

lemma twoGroupFactor_iff {A B : Subgroup X} [A.Normal] :
    TwoGroupFactor A B ↔ ∃ k, A.relIndex B = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨fun ⟨_, h⟩ => IsPGroup.iff_card.1 h, fun h => ⟨inferInstance, IsPGroup.iff_card.2 h⟩⟩

/-- The numerical properties used for the two kinds of factors. -/
def IsTwoPow (n : ℕ) : Prop := ∃ k, n = 2 ^ k

/-- A property of numbers closed under products and divisors. -/
structure MulDvdClosed (p : ℕ → Prop) : Prop where
  one : p 1
  mul : ∀ a b, p a → p b → p (a * b)
  dvd : ∀ a b, a ∣ b → p b → p a

lemma mulDvdClosed_odd : MulDvdClosed Odd :=
  ⟨odd_one, fun _ _ => Odd.mul, fun _ _ h hb => Odd.of_dvd_nat hb h⟩

lemma mulDvdClosed_twoPow : MulDvdClosed IsTwoPow :=
  ⟨⟨0, rfl⟩, fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ => ⟨i + j, by rw [hi, hj, pow_add]⟩,
    fun _ _ h ⟨j, hj⟩ => by
      rw [hj] at h
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
      exact ⟨i, rfl⟩⟩

lemma relIndex_trans {p : ℕ → Prop} (hp : MulDvdClosed p) {A B C : Subgroup X} (hAB : A ≤ B)
    (hBC : B ≤ C) (h1 : p (A.relIndex B)) (h2 : p (B.relIndex C)) : p (A.relIndex C) := by
  rw [← relIndex_mul_relIndex A B C hAB hBC]
  exact hp.mul _ _ h1 h2

/-- If `B/A` has property `p` and `A ≤ U` with `U` normal, then so does `(B ⊔ U)/U`. -/
lemma relIndex_sup {p : ℕ → Prop} (hp : MulDvdClosed p) {A B U : Subgroup X} [U.Normal]
    (hAU : A ≤ U) (h : p (A.relIndex B)) : p (U.relIndex (B ⊔ U)) := by
  rw [relIndex_sup_right]
  exact hp.dvd _ _ (relIndex_dvd_of_le_left B hAU) h

lemma relIndex_sup_sup {p : ℕ → Prop} (hp : MulDvdClosed p) {U N₁ N₂ : Subgroup X} [N₁.Normal]
    (h₁ : U ≤ N₁) (hp₁ : p (U.relIndex N₁)) (hp₂ : p (U.relIndex N₂)) :
    p (U.relIndex (N₁ ⊔ N₂)) := by
  rw [← relIndex_mul_relIndex U N₁ (N₁ ⊔ N₂) h₁ le_sup_left, sup_comm N₁ N₂,
    relIndex_sup_right]
  exact hp.mul _ _ hp₁ (hp.dvd _ _ (relIndex_dvd_of_le_left N₂ h₁) hp₂)

end Index

/-! ### Two-series with an arbitrary bottom term, and the crosswalk for the `2`-length -/

section TwoCrosswalk

variable {X : Type u} [Group X] [Finite X]

/-- A series `N = G₀ ≤ ⋯ ≤ G_{2l+1} = X` of normal subgroups, alternately `2'`- and `2`-factors. -/
structure TwoSeriesFrom (X : Type u) [Group X] (N : Subgroup X) (l : ℕ) where
  G : ℕ → Subgroup X
  normal : ∀ i, (G i).Normal
  mono : ∀ i < 2 * l + 1, G i ≤ G (i + 1)
  zero : G 0 = N
  top : G (2 * l + 1) = ⊤
  odd : ∀ i ≤ l, OddOrderFactor (G (2 * i)) (G (2 * i + 1))
  two : ∀ i < l, TwoGroupFactor (G (2 * i + 1)) (G (2 * i + 2))

def TwoSeriesFrom.toTwoSeries {l : ℕ} (s : TwoSeriesFrom X ⊥ l) : TwoSeries X l :=
  { s with }

def TwoSeriesFrom.topSeries : TwoSeriesFrom X ⊤ 0 where
  G _ := ⊤
  normal _ := normal_top
  mono _ _ := le_rfl
  zero := rfl
  top := rfl
  odd i _ := oddOrderFactor_self _
  two i hi := absurd hi (Nat.not_lt_zero _)

def TwoSeriesFrom.consOdd {M N : Subgroup X} [hM : M.Normal] {l : ℕ} (t : TwoSeriesFrom X N l)
    (hMN : M ≤ N) (hs : OddOrderFactor M N) : TwoSeriesFrom X M l where
  G i := match i with
    | 0 => M
    | j + 1 => t.G (j + 1)
  normal i := match i with
    | 0 => hM
    | j + 1 => t.normal (j + 1)
  mono i hi := match i with
    | 0 => hMN.trans (by have := t.mono 0 (by omega); rwa [t.zero] at this)
    | j + 1 => t.mono (j + 1) hi
  zero := rfl
  top := t.top
  odd i hi := match i with
    | 0 => by
      show OddOrderFactor M (t.G 1)
      haveI := t.normal 0
      have h0 : OddOrderFactor (t.G 0) (t.G 1) := t.odd 0 (Nat.zero_le _)
      rw [← t.zero] at hs hMN
      rw [oddOrderFactor_iff] at hs h0 ⊢
      exact relIndex_trans mulDvdClosed_odd hMN (t.mono 0 (by omega)) hs h0
    | j + 1 => t.odd (j + 1) hi
  two i hi := t.two i hi

def TwoSeriesFrom.consTwo {M N : Subgroup X} [hM : M.Normal] {l : ℕ} (t : TwoSeriesFrom X N l)
    (hMN : M ≤ N) (hs : TwoGroupFactor M N) : TwoSeriesFrom X M (l + 1) where
  G i := match i with
    | 0 => M
    | 1 => M
    | j + 2 => t.G j
  normal i := match i with
    | 0 => hM
    | 1 => hM
    | j + 2 => t.normal j
  mono i hi := match i with
    | 0 => le_rfl
    | 1 => by show M ≤ t.G 0; rw [t.zero]; exact hMN
    | j + 2 => t.mono j (by omega)
  zero := rfl
  top := t.top
  odd i hi := match i with
    | 0 => oddOrderFactor_self _
    | j + 1 => t.odd j (by omega)
  two i hi := match i with
    | 0 => by show TwoGroupFactor M (t.G 0); rw [t.zero]; exact hs
    | j + 1 => t.two j (by omega)

open Classical in
lemma twoSeries_of_paperSeries (s : PaperSeries X TwoOrOdd) :
    ∀ m j, j + m = s.n → Nonempty (TwoSeriesFrom X (s.G j)
      ((Finset.Ico j s.n).filter fun i => ¬ OddOrderFactor (s.G i) (s.G (i + 1))).card) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    subst hj
    simp only [add_zero, Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    rw [s.top]
    exact ⟨TwoSeriesFrom.topSeries⟩
  | succ m ih =>
    intro j hj
    obtain ⟨t⟩ := ih (j + 1) (by omega)
    have hjn : j < s.n := by omega
    rw [card_filter_Ico_succ _ hjn]
    haveI := s.normal j (by omega)
    by_cases hodd : OddOrderFactor (s.G j) (s.G (j + 1))
    · rw [if_neg (not_not.2 hodd), add_zero]
      exact ⟨t.consOdd (s.mono j hjn) hodd⟩
    · rw [if_pos hodd]
      exact ⟨t.consTwo (s.mono j hjn) ((s.factor j hjn).resolve_right hodd)⟩

lemma twoLengthLE_of_paperSeries (s : PaperSeries X TwoOrOdd) :
    TwoLengthLE X (s.count OddOrderFactor) := by
  obtain ⟨t⟩ := twoSeries_of_paperSeries s s.n 0 (by omega)
  rw [count_eq]
  exact ⟨({ t with zero := t.zero.trans s.zero } : TwoSeriesFrom X ⊥ _).toTwoSeries⟩

lemma exists_paperSeries_of_twoLengthLE {l : ℕ} (H : TwoLengthLE X l) :
    ∃ s : PaperSeries X TwoOrOdd, s.count OddOrderFactor ≤ l := by
  classical
  obtain ⟨t⟩ := H
  refine ⟨{ n := 2 * l + 1, G := t.G, normal := fun i _ => t.normal i, mono := t.mono,
            zero := t.zero, top := t.top, factor := fun i hi => ?_ }, ?_⟩
  · rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inr (by rw [← two_mul]; exact t.odd j (by omega))
    · exact Or.inl (t.two j (by omega))
  · rw [PaperSeries.count]
    refine (Finset.card_le_card (t := (Finset.range l).image fun j => 2 * j + 1) ?_).trans
      Finset.card_image_le |>.trans (by simp)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_image, Finset.mem_range]
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact absurd (by rw [← two_mul]; exact t.odd j (by omega)) hi.2
    · exact ⟨j, by omega, rfl⟩

/-- **Crosswalk.** The paper's `2`-length (least number of `2`-factors in a normal series with
`2`- and `2'`-factors) equals `twoLength`, defined with alternating series. -/
theorem paperTwoLength_eq : paperTwoLength X = twoLength X := by
  unfold paperTwoLength twoLength
  apply sInf_eq_of_bounds
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, twoLengthLE_of_paperSeries s, le_rfl⟩
  · intro l hl
    obtain ⟨s, hs⟩ := exists_paperSeries_of_twoLengthLE hl
    exact ⟨_, ⟨s, rfl⟩, hs⟩

/-- **Crosswalk.** `L₂` in the paper's sense equals `maxTwoLength`. -/
theorem paperMaxTwoLength_eq : paperMaxTwoLength X = maxTwoLength X := by
  rw [paperMaxTwoLength, maxTwoLength]
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, paperTwoLength_eq]

end TwoCrosswalk

/-! ### The upper `2`-series -/

section Upper

variable {X : Type u} [Group X] [Finite X]

/-- The largest normal subgroup `N ≥ U` of `X` such that `|N/U|` has property `p`. -/
noncomputable def relCore (p : ℕ → Prop) (U : Subgroup X) : Subgroup X :=
  sSup {N | N.Normal ∧ U ≤ N ∧ p (U.relIndex N)}

lemma relCore_mem {p : ℕ → Prop} (hp : MulDvdClosed p) (U : Subgroup X) [U.Normal] :
    (relCore p U).Normal ∧ U ≤ relCore p U ∧ p (U.relIndex (relCore p U)) := by
  set S := {N : Subgroup X | N.Normal ∧ U ≤ N ∧ p (U.relIndex N)}
  have hU : U ∈ S := ⟨inferInstance, le_rfl, by rw [relIndex_self]; exact hp.one⟩
  have hsup : ∀ N₁ ∈ S, ∀ N₂ ∈ S, N₁ ⊔ N₂ ∈ S := by
    rintro N₁ ⟨h₁, hU₁, hp₁⟩ N₂ ⟨h₂, -, hp₂⟩
    exact ⟨Subgroup.sup_normal N₁ N₂, hU₁.trans le_sup_left, relIndex_sup_sup hp hU₁ hp₁ hp₂⟩
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  obtain ⟨t, ht⟩ := (Set.toFinite S).exists_finset_coe
  have key : t.sup id ⊔ U ∈ S := by
    refine Finset.sup_induction (p := fun N => N ⊔ U ∈ S) (by rw [bot_sup_eq]; exact hU) ?_ ?_
    · intro a ha b hb
      have := hsup _ ha _ hb
      rwa [show a ⊔ U ⊔ (b ⊔ U) = a ⊔ b ⊔ U by
        rw [sup_assoc, sup_comm U, sup_assoc, sup_idem, ← sup_assoc]] at this
    · intro b hb
      have hb' : b ∈ S := by rw [← ht]; exact hb
      rwa [id, sup_eq_left.2 hb'.2.1]
  have heq : t.sup id ⊔ U = relCore p U := by
    show t.sup id ⊔ U = sSup S
    rw [← ht, ← Finset.sup_id_eq_sSup]
    exact sup_eq_left.2 (Finset.le_sup_of_le (b := U) (by rw [← Finset.mem_coe, ht]; exact hU) le_rfl)
  rw [← heq]
  exact key

lemma le_relCore {p : ℕ → Prop} {U N : Subgroup X} [N.Normal] (hUN : U ≤ N)
    (h : p (U.relIndex N)) : N ≤ relCore p U :=
  le_sSup ⟨inferInstance, hUN, h⟩

/-- The terms of the upper `2`-series, with their normality:
`U₀ = 1`, `U_{2i+1}/U_{2i} = O_{2'}(X/U_{2i})`, `U_{2i+2}/U_{2i+1} = O_2(X/U_{2i+1})`. -/
noncomputable def upperTwoSeriesN (X : Type u) [Group X] [Finite X] :
    ℕ → {N : Subgroup X // N.Normal}
  | 0 => ⟨⊥, normal_bot⟩
  | j + 1 =>
    haveI := (upperTwoSeriesN X j).2
    if j % 2 = 0 then ⟨relCore Odd (upperTwoSeriesN X j).1, (relCore_mem mulDvdClosed_odd _).1⟩
    else ⟨relCore IsTwoPow (upperTwoSeriesN X j).1, (relCore_mem mulDvdClosed_twoPow _).1⟩

/-- The upper `2`-series `1 ≤ O_{2'}(X) ≤ O_{2',2}(X) ≤ O_{2',2,2'}(X) ≤ ⋯`. -/
noncomputable def upperTwoSeries (X : Type u) [Group X] [Finite X] (j : ℕ) : Subgroup X :=
  (upperTwoSeriesN X j).1

instance upperTwoSeries_normal (j : ℕ) : (upperTwoSeries X j).Normal := (upperTwoSeriesN X j).2

lemma upperTwoSeries_even (i : ℕ) :
    upperTwoSeries X (2 * i + 1) = relCore Odd (upperTwoSeries X (2 * i)) := by
  show (upperTwoSeriesN X (2 * i + 1)).1 = _
  dsimp only [upperTwoSeriesN]
  rw [if_pos (by omega)]
  rfl

lemma upperTwoSeries_odd (i : ℕ) :
    upperTwoSeries X (2 * i + 2) = relCore IsTwoPow (upperTwoSeries X (2 * i + 1)) := by
  show (upperTwoSeriesN X (2 * i + 1 + 1)).1 = _
  dsimp only [upperTwoSeriesN]
  rw [if_neg (by omega)]
  rfl

lemma oddOrderFactor_upperTwoSeries (i : ℕ) :
    upperTwoSeries X (2 * i) ≤ upperTwoSeries X (2 * i + 1) ∧
      OddOrderFactor (upperTwoSeries X (2 * i)) (upperTwoSeries X (2 * i + 1)) := by
  rw [upperTwoSeries_even, oddOrderFactor_iff]
  exact (relCore_mem mulDvdClosed_odd _).2

lemma twoGroupFactor_upperTwoSeries (i : ℕ) :
    upperTwoSeries X (2 * i + 1) ≤ upperTwoSeries X (2 * i + 2) ∧
      TwoGroupFactor (upperTwoSeries X (2 * i + 1)) (upperTwoSeries X (2 * i + 2)) := by
  rw [upperTwoSeries_odd, twoGroupFactor_iff]
  exact (relCore_mem mulDvdClosed_twoPow _).2

lemma upperTwoSeries_le_succ (j : ℕ) : upperTwoSeries X j ≤ upperTwoSeries X (j + 1) := by
  rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [← two_mul]; exact (oddOrderFactor_upperTwoSeries i).1
  · exact (twoGroupFactor_upperTwoSeries i).1

/-- Every alternating `2`-series lies termwise below the upper `2`-series. -/
lemma le_upperTwoSeries {l : ℕ} (s : TwoSeries X l) :
    ∀ j ≤ 2 * l + 1, s.G j ≤ upperTwoSeries X j := by
  intro j
  induction j with
  | zero => intro _; rw [s.zero]; exact bot_le
  | succ j ih =>
    intro hj
    have hA := ih (by omega)
    haveI := s.normal j
    haveI := s.normal (j + 1)
    refine le_trans (le_sup_left : s.G (j + 1) ≤ s.G (j + 1) ⊔ upperTwoSeries X j) ?_
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [← two_mul] at hA ⊢
      haveI := s.normal (2 * i)
      haveI := s.normal (2 * i + 1)
      rw [upperTwoSeries_even]
      have h := oddOrderFactor_iff.1 (s.odd i (by omega))
      exact le_relCore le_sup_right (relIndex_sup mulDvdClosed_odd hA h)
    · rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega, upperTwoSeries_odd]
      haveI := s.normal (2 * i + 1)
      haveI := s.normal (2 * i + 2)
      have h := twoGroupFactor_iff.1 (s.two i (by omega))
      exact le_relCore le_sup_right (relIndex_sup mulDvdClosed_twoPow hA h)

/-- **Upper `2`-series.** `l₂(X) ≤ l` iff the upper `2`-series reaches `X` after `l` `2`-steps,
i.e. `O_{2',2,2',…,2,2'}(X) = X` (`2l+1` terms). -/
theorem twoLengthLE_iff_upperTwoSeries {l : ℕ} :
    TwoLengthLE X l ↔ upperTwoSeries X (2 * l + 1) = ⊤ := by
  constructor
  · rintro ⟨s⟩
    rw [eq_top_iff, ← s.top]
    exact le_upperTwoSeries s _ le_rfl
  · intro h
    exact ⟨{ G := upperTwoSeries X
             normal := upperTwoSeries_normal
             mono := fun i _ => upperTwoSeries_le_succ i
             zero := rfl
             top := h
             odd := fun i _ => (oddOrderFactor_upperTwoSeries i).2
             two := fun i _ => (twoGroupFactor_upperTwoSeries i).2 }⟩

end Upper

/-! ### The main results in the paper's literal terms -/

/-- **Nonsoluble length of groups.** Let G be a finite group and λ(G) its nonsoluble length, the least number of
nonsoluble factors in a normal series of G whose factors are soluble or direct products of nonabelian simple groups.
Then λ(G) ≤ 2L₂ + 1, where L₂ is the maximum 2-length of a soluble subgroup of G, and λ(G) is at most the maximum
Fitting height of a soluble subgroup of G. For an odd prime p, the non-p-soluble length of G is at most the maximum
p-length of a p-soluble subgroup of G.

Source: E. I. Khukhro and P. Shumyatsky, Nonsoluble and non-p-soluble length of finite groups, Israel J. Math. 207
(2015), 507–525, Theorem 1.1 and Corollary 1.2. https://doi.org/10.1007/s11856-015-1180-x

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_1_1_a [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] : paperNonsolubleLength G ≤ 2 * paperMaxTwoLength G + 1 := by
  rw [paperNonsolubleLength_eq, paperMaxTwoLength_eq]
  exact nonsolubleLength_le_two_mul_maxTwoLength_add_one hCFSG G

/-- **Theorem 1.1(a)**, unpacked: if every soluble subgroup of `G` has a normal series with
`2`- and `2'`-factors having at most `l` factors of even order, then `G` has a normal series with
soluble or semisimple factors having at most `2l+1` nonsoluble factors. -/
theorem theorem_1_1_a_series [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] (l : ℕ)
    (h : ∀ H : Subgroup G, Group.IsSolvable H →
      ∃ s : PaperSeries H TwoOrOdd, s.count OddOrderFactor ≤ l) :
    ∃ s : PaperSeries G SolOrSemisimple, s.count SolubleFactor ≤ 2 * l + 1 := by
  refine exists_paperSeries_of_nonsolubleLengthLE
    (nonsolubleLengthLE_of_twoLengthLE hCFSG G l fun H hH => ?_)
  obtain ⟨s, hs⟩ := h H hH
  exact twoLengthLE_mono hs (twoLengthLE_of_paperSeries s)

/-- **Corollary 1.2 (Khukhro–Shumyatsky).** `λ(G)` (paper's definition) does not exceed the
maximum Fitting height of soluble subgroups of `G` (Fitting height = least length of a normal
series with nilpotent factors, `FittingSeries`). -/
theorem corollary_1_2 [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] : paperNonsolubleLength G ≤ maxFittingHeight G := by
  rw [paperNonsolubleLength_eq]
  exact nonsolubleLength_le_maxFittingHeight hCFSG G

end CFSGOutside.KhukhroShumyatskyNonsolubleLength
