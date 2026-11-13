
import CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix
import CFSGOutside.Corpus.Schreier

/-!
# Wielandt: an 8-transitive permutation group contains the alternating group

**Paper.** H. Wielandt, *Über den Transitivitätsgrad von Permutationsgruppen*,
Math. Z. **74** (1960), 297–298, DOI 10.1007/BF01180490.

**Satz 1** (verbatim): *𝔊 sei eine weder alternierende noch symmetrische Permutationsgruppe.
Die äußere Automorphismengruppe jeder einfachen Untergruppe von 𝔊 sei auflösbar. Dann ist 𝔊
höchstens siebenfach transitiv.*

**Claims formalized.**
* `wielandt_satz1`: Satz 1 in the paper's form, with the paper's local hypothesis (`Out(T)`
  solvable for every simple subgroup `T ≤ G`) and no classification hypothesis: if `G ≤ Sym(Ω)`
  is neither `Alt(Ω)` nor `Sym(Ω)` and `k`-transitive with `k ≤ |Ω|`, then `k ≤ 7`.
* `wielandt_hilfssatz`: Hilfssatz (2) in the paper's form (under the same local hypothesis).
* `alternatingGroup_le_of_outer`: the working form (an 8-transitive `G` of degree `≥ 8` contains
  `Alt(Ω)`), assuming `Out(T)` solvable only for the *nonabelian* simple subgroups `T ≤ G`.
* `wielandt_eight_transitive`: the unconditional corollary, from the classification statement
  `hCFSG : TauCeti.ClassificationStatement.{0}` (proved in the corpus as
  `CFSGComparator.classification`, not imported here to keep the import closure small) through
  Schreier's conjecture for the catalogue (the class `CFSGOutside.Corpus.Schreier`).

The only automorphism groups used are `Out(N)` for `N` the socle of a pointwise stabiliser of
five points, a simple subgroup of `G`; so no `Out` outside `G` is needed.

**CFSG components reused**, as classes in `CFSGOutside.Corpus` that the clean build proves.
* (for the corollary only) `Schreier`, Schreier's conjecture for groups in the CFSG catalogue
  (`CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`), together with `hCFSG` (every finite
  simple group is in the catalogue);
* `AlternatingGroupLeOfNontrivialSupportLeSix`
  (`CFSG.FiveTransitive.SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six`: a
  5-transitive group of degree `≥ 8` containing a nontrivial element of support `≤ 6` contains `Alt`);
* the copy of `CFSG.ComponentClassification.OuterAutomorphisms.Outer` (`Out(T) = Aut(T)/Inn(T)`);
  `solvable_of_equiv` (`Out` respects isomorphism) and `isPretransitive_of_normal_ne_bot` are
  proved here;
* Burnside's theorem on minimal normal subgroups of 2-transitive groups
  (`burnside_minimal_normal`, `burnside_minimal_normal_unique`), copied verbatim from the
  formalization of Cameron's 2-transitive socle theorem (same campaign, not in this repository); it uses only
  Mathlib.

**Proof route** (the classical argument).  Suppose `n = |Ω| ≥ 11` (for `n ≤ 10`, 8-transitivity is
`(n-2)`-transitivity and Mathlib's `IsMultiplyPretransitive.alternatingGroup_le` applies).  For a
`d`-subset `Δ` (`d = 5, 6`) let `M` be its setwise and `H ⊴ M` its pointwise stabiliser; `M`
induces `Sym(Δ)` (non-solvable) and `H` is `(8-d)`-transitive on `X = Ω ∖ Δ`.
1. If `M` is not faithful on `X`, a nontrivial element supported in `Δ` gives `Alt(Ω) ≤ G`.
2. Otherwise let `N` be the unique minimal normal subgroup of `H` (Burnside); it is
   characteristic in `H`, hence normal in `M`.
3. If `N` is nonabelian simple, `C_H(N) = 1` forces `C_M(N) = 1`, so `M/N ↪ Out(N)`, which is
   solvable (local hypothesis: `N` is a simple subgroup of `G`); then `Sym(Δ)`, a quotient of
   `M/H`, is solvable: contradiction.
4. If `N` is abelian it is regular of exponent `p`, so `|X| = p^b`; when `H` is 3-transitive
   (`d = 5`), `p = 2`; when `b = 1`, `M ≤ AGL(1,p)` is solvable: contradiction again.
5. Hence `n - 5 = 2^a` and `n - 6 = q^b` with `b ≥ 2`, i.e. `2^a = q^b + 1`, impossible.
-/

section

namespace CFSGOutside.Wielandt

open MulAction

/-- A nontrivial normal subgroup of a faithful primitive group is transitive, as
`CFSG.GroupActions.isPretransitive_of_normal_ne_bot` states it. -/
private theorem isPretransitive_of_normal_ne_bot
    {G Ω : Type*} [Group G] [MulAction G Ω] [Nonempty Ω]
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    MulAction.IsPretransitive N Ω := by
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  have hnotfixed : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := hfixed.symm ▸ Set.mem_univ x
    exact (hx a).trans (hx b).symm
  exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hnotfixed

section Burnside

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]

/-- An element of `G` fixing every point is trivial. -/
private theorem eq_one_of_forall_smul_eq {g : G} (h : ∀ x : Ω, g • x = x) : g = 1 :=
  FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun x => by rw [h x, one_smul]

/-- A subgroup centralised by a transitive subgroup acts semiregularly. -/
private theorem eq_one_of_transitive_centralizer {K C : Subgroup G}
    (hCK : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k) (hC : ∀ x y : Ω, ∃ c ∈ C, c • x = y)
    {k : G} (hk : k ∈ K) {x : Ω} (hx : k • x = x) : k = 1 := by
  refine eq_one_of_forall_smul_eq (Ω := Ω) fun y => ?_
  obtain ⟨c, hc, rfl⟩ := hC x y
  rw [← mul_smul, hCK c hc k hk, mul_smul, hx]

/-- **Order lemma.** Let `G` be 2-transitive and let `K ≤ G` act semiregularly, such that every
`G`-conjugate of `K` is contained in `K` or centralises `K`. Then all nontrivial elements of `K`
have the same order. -/
theorem orderOf_eq_of_semiregular (h2 : IsMultiplyPretransitive G Ω 2) {K : Subgroup G}
    (hconj : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) ∨
      (∀ k ∈ K, ∀ k' ∈ K, Commute (g * k * g⁻¹) k'))
    (hfree : ∀ k ∈ K, ∀ x : Ω, k • x = x → k = 1) (x : Ω)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    orderOf a = orderOf b := by
  have hax : x ≠ a • x := fun h => ha1 (hfree a ha x h.symm)
  have hbx : x ≠ b • x := fun h => hb1 (hfree b hb x h.symm)
  obtain ⟨g, hg0, hg1⟩ := MulAction.is_two_pretransitive_iff.mp h2 hax hbx
  have hginv : g⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact hg0.symm
  set a' := g * a * g⁻¹ with ha'
  have ha'x : a' • x = b • x := by
    rw [ha', mul_smul, mul_smul, hginv, hg1]
  -- `a'` and `b` commute
  have hcomm : Commute b⁻¹ a' := by
    rcases hconj g with h | h
    · have : b⁻¹ * a' = 1 := hfree _ (K.mul_mem (K.inv_mem hb) (h a ha)) x (by
        rw [mul_smul, ha'x, inv_smul_smul])
      rw [(inv_mul_eq_one.mp this).symm]; exact (Commute.refl b).inv_left
    · exact (h a ha b hb).symm.inv_left
  have hfix : (b⁻¹ * a') • x = x := by rw [mul_smul, ha'x, inv_smul_smul]
  have hpow : ∀ n : ℕ, a' ^ n • x = b ^ n • x := by
    intro n
    have h1 : (b⁻¹ * a') ^ n • x = x := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
    rw [hcomm.mul_pow, inv_pow, mul_smul, inv_smul_eq_iff] at h1
    exact h1
  have ha'pow : ∀ n : ℕ, a' ^ n = g * a ^ n * g⁻¹ := fun n => by
    rw [ha', conj_pow]
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro han
    refine hfree _ (K.pow_mem hb n) x ?_
    rw [← hpow n, ha'pow, han, mul_one, mul_inv_cancel, one_smul]
  · intro hbn
    refine hfree _ (K.pow_mem ha n) x ?_
    have := hpow n
    rw [hbn, one_smul, ha'pow, mul_smul, mul_smul, hginv] at this
    rw [← smul_left_cancel_iff g, this, hg0]

/-- A finite nontrivial group all of whose nontrivial elements have the same order has prime
exponent. -/
theorem exists_prime_pow_eq_one {K : Subgroup G} [Finite K] (hK : K ≠ ⊥)
    (hord : ∀ a ∈ K, ∀ b ∈ K, a ≠ 1 → b ≠ 1 → orderOf a = orderOf b) :
    ∃ p : ℕ, p.Prime ∧ ∀ a ∈ K, a ^ p = 1 := by
  have : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hK
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Finite.one_lt_card (α := K)))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpdvd
  have hc1 : (c : G) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc
    exact hp.ne_one hc.symm
  refine ⟨p, hp, fun a ha => ?_⟩
  by_cases ha1 : a = 1
  · rw [ha1, one_pow]
  · rw [← orderOf_dvd_iff_pow_eq_one, hord a ha c c.2 ha1 hc1, Subgroup.orderOf_coe, hc]

/-- **Key lemma (the `k ≥ 2` step of Burnside's theorem).** Let `G` act faithfully and
2-transitively on `Ω`, and let `K ≠ 1` be a subgroup that is not normal, such that every
`G`-conjugate of `K` is contained in `K` or centralises `K`. Then `K` acts semiregularly. -/
theorem semiregular_of_conj_le_or_commute (h2 : IsMultiplyPretransitive G Ω 2)
    {K : Subgroup G} (hK : K ≠ ⊥)
    (hconj : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) ∨
      (∀ k ∈ K, ∀ k' ∈ K, Commute (g * k * g⁻¹) k'))
    (hnn : ∃ g : G, ∃ k ∈ K, g * k * g⁻¹ ∉ K) :
    ∀ k ∈ K, ∀ x : Ω, k • x = x → k = 1 := by
  classical
  set C := Subgroup.centralizer (K : Set G)
  have hCK : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k := fun c hc k hk =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  -- conjugates not inside `K` lie in `C`
  have hconjC : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) ∨ (∀ k ∈ K, g * k * g⁻¹ ∈ C) := by
    intro g
    refine (hconj g).imp id fun h k hk => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun k' hk' => (h k hk k' hk').symm.eq
  -- a point moved by `K`
  obtain ⟨k₀, hk₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK
  obtain ⟨α, hα⟩ : ∃ α : Ω, (k₀ : G) • α ≠ α := by
    by_contra h
    push Not at h
    exact hk₀1 (Subtype.ext (eq_one_of_forall_smul_eq (Ω := Ω) h))
  -- Step 1: `Ω = Kα ∪ Cα`
  have hcover : ∀ y : Ω, (∃ k ∈ K, k • α = y) ∨ (∃ c ∈ C, c • α = y) := by
    intro y
    by_cases hy : y = α
    · exact Or.inl ⟨1, K.one_mem, by rw [one_smul, hy]⟩
    obtain ⟨g, hg0, hg1⟩ := MulAction.is_two_pretransitive_iff.mp h2 hα.symm (Ne.symm hy)
    have hginv : g⁻¹ • α = α := by rw [inv_smul_eq_iff]; exact hg0.symm
    have hy' : (g * (k₀ : G) * g⁻¹) • α = y := by rw [mul_smul, mul_smul, hginv, hg1]
    rcases hconjC g with h | h
    · exact Or.inl ⟨_, h _ k₀.2, hy'⟩
    · exact Or.inr ⟨_, h _ k₀.2, hy'⟩
  -- Step 2: `K` or `C` is transitive on `Ω`
  have htrans : (∀ y : Ω, ∃ k ∈ K, k • α = y) ∨ (∀ y : Ω, ∃ c ∈ C, c • α = y) := by
    by_contra h
    rw [not_or, not_forall, not_forall] at h
    obtain ⟨⟨z, hz⟩, ⟨y, hy⟩⟩ := h
    obtain ⟨c, hc, rfl⟩ := (hcover z).resolve_left hz
    obtain ⟨k, hk, rfl⟩ := (hcover y).resolve_right hy
    rcases hcover ((k * c) • α) with ⟨k', hk', hw⟩ | ⟨c', hc', hw⟩
    · apply hz ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', ?_⟩
      rw [mul_smul, hw, ← mul_smul, inv_mul_cancel_left]
    · apply hy ⟨c⁻¹ * c', C.mul_mem (C.inv_mem hc) hc', ?_⟩
      rw [mul_smul, hw, hCK c hc k hk, ← mul_smul, inv_mul_cancel_left]
  -- Step 3: `C` is transitive on `Ω`
  have hCtrans : ∀ x y : Ω, ∃ c ∈ C, c • x = y := by
    have base : ∀ β : Ω, (∀ y : Ω, ∃ c ∈ C, c • β = y) → ∀ x y : Ω, ∃ c ∈ C, c • x = y := by
      intro β hβ x y
      obtain ⟨c₁, hc₁, rfl⟩ := hβ x
      obtain ⟨c₂, hc₂, rfl⟩ := hβ y
      exact ⟨c₂ * c₁⁻¹, C.mul_mem hc₂ (C.inv_mem hc₁), by rw [mul_smul, inv_smul_smul]⟩
    rcases htrans with hK' | hC'
    · obtain ⟨g, k₁, hk₁, hg⟩ := hnn
      have hgC : ∀ k ∈ K, g * k * g⁻¹ ∈ C :=
        (hconjC g).resolve_left fun h => hg (h k₁ hk₁)
      refine base (g • α) fun y => ?_
      obtain ⟨k, hk, hky⟩ := hK' (g⁻¹ • y)
      refine ⟨g * k * g⁻¹, hgC k hk, ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hky, smul_inv_smul]
    · exact base α hC'
  intro k hk x hx
  exact eq_one_of_transitive_centralizer hCK hCtrans hk hx


variable [Finite G]

private theorem nonempty_of_ne_bot {N : Subgroup G} (hN : N ≠ ⊥) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  apply hN
  rw [eq_bot_iff]
  intro n _
  rw [Subgroup.mem_bot]
  exact eq_one_of_forall_smul_eq (Ω := Ω) fun x => (IsEmpty.false x).elim

/-- A nontrivial normal subgroup of a 2-transitive group is transitive. -/
private theorem transitive_of_normal (h2 : IsMultiplyPretransitive G Ω 2) {N : Subgroup G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : ∀ x y : Ω, ∃ n ∈ N, n • x = y := by
  have := nonempty_of_ne_bot (Ω := Ω) hN1
  have : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive h2
  have := isPretransitive_of_normal_ne_bot (Ω := Ω) N hN1
  intro x y
  obtain ⟨n, hn⟩ := exists_smul_eq N x y
  exact ⟨n, n.2, hn⟩

/-- A nontrivial group of prime exponent has a nontrivial central element. -/
private theorem exists_central_of_exponent {M : Subgroup G} (hM : M ≠ ⊥) {p : ℕ}
    (hp : p.Prime) (hexp : ∀ a ∈ M, a ^ p = 1) :
    ∃ z ∈ M, z ≠ 1 ∧ ∀ m ∈ M, z * m = m * z := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM
  have hP : IsPGroup p M := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (by simpa using hexp g g.2)⟩
  have := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center M)
  refine ⟨z.1.1, z.1.2, fun h => hz (Subtype.ext (Subtype.ext h)), fun m hm => ?_⟩
  have h' := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨m, hm⟩)
  simp only [Subgroup.coe_mul] at h'
  exact h'.symm

/-- **Burnside's theorem** (Burnside 1911, §154; Dixon–Mortimer, Thm 4.1B).
A minimal normal subgroup `N` of a finite group `G` acting faithfully and 2-transitively is
either regular and elementary abelian, or nonabelian simple with trivial centraliser in `G`. -/
theorem burnside_minimal_normal (h2 : IsMultiplyPretransitive G Ω 2)
    (N : Subgroup G) (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    (∃ p : ℕ, p.Prime ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ a ∈ N, a ^ p = 1) ∧
        ∀ x y : Ω, ∃! n : N, (n : G) • x = y) ∨
    (IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧
        Subgroup.centralizer (N : Set G) = ⊥) := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨x₀⟩ := nonempty_of_ne_bot (Ω := Ω) hN1
  have htr := transitive_of_normal h2 hN hN1
  have hnormconj : ∀ g : G, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g n hn => hN.conj_mem n hn g
  by_cases hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
  · -- abelian case: `N` is regular and elementary abelian
    left
    have hfree : ∀ k ∈ N, ∀ x : Ω, k • x = x → k = 1 := fun k hk x hx =>
      eq_one_of_transitive_centralizer (K := N) (C := N) (fun c hc k hk => hab k hk c hc) htr hk hx
    obtain ⟨p, hp, hexp⟩ := exists_prime_pow_eq_one hN1 fun a ha b hb ha1 hb1 =>
      orderOf_eq_of_semiregular h2 (fun g => Or.inl fun k hk => hnormconj g k hk) hfree x₀
        ha hb ha1 hb1
    refine ⟨p, hp, hab, hexp, fun x y => ?_⟩
    obtain ⟨n, hn, hxy⟩ := htr x y
    refine ⟨⟨n, hn⟩, hxy, fun m hm => ?_⟩
    have : n⁻¹ * (m : G) = 1 := hfree _ (N.mul_mem (N.inv_mem hn) m.2) x (by
      rw [mul_smul, hm, ← hxy, inv_smul_smul])
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  right
  push Not at hab
  obtain ⟨a, ha, b, hb, hab⟩ := hab
  have hnc : ∃ a b : N, a * b ≠ b * a :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  -- the centraliser of `N` is trivial
  have hC : Subgroup.centralizer (N : Set G) = ⊥ := by
    by_contra hC
    set C := Subgroup.centralizer (N : Set G)
    have hCn : C.Normal := inferInstance
    have hCtr := transitive_of_normal h2 hCn hC
    have hfree : ∀ k ∈ N, ∀ x : Ω, k • x = x → k = 1 := fun k hk x hx =>
      eq_one_of_transitive_centralizer (K := N) (C := C)
        (fun c hc k hk => Subgroup.mem_centralizer_iff.mp hc k hk) hCtr hk hx
    obtain ⟨p, hp, hexp⟩ := exists_prime_pow_eq_one hN1 fun a ha b hb ha1 hb1 =>
      orderOf_eq_of_semiregular h2 (fun g => Or.inl fun k hk => hnormconj g k hk) hfree x₀
        ha hb ha1 hb1
    obtain ⟨z, hzN, hz1, hzc⟩ := exists_central_of_exponent hN1 hp hexp
    have hmeet : N ⊓ C = N := by
      rcases hmin (N ⊓ C) inferInstance inf_le_left with h | h
      · exfalso
        have hz : z ∈ N ⊓ C :=
          ⟨hzN, Subgroup.mem_centralizer_iff.mpr fun m hm => (hzc m hm).symm⟩
        rw [h, Subgroup.mem_bot] at hz
        exact hz1 hz
      · exact h
    exact hab (Subgroup.mem_centralizer_iff.mp (inf_eq_left.mp hmeet hb) a ha)
  refine ⟨?_, hnc, hC⟩
  -- simplicity: a minimal `N`-invariant subgroup `K` of `N`
  set S : Set (Subgroup G) := {M | M ≤ N ∧ M ≠ ⊥ ∧ ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M}
  have hNS : N ∈ S := ⟨le_rfl, hN1, fun n hn m hm => N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)⟩
  obtain ⟨K, hKS, hKmin⟩ := Set.Finite.exists_minimalFor (fun M : Subgroup G => Nat.card M) S
    (Set.toFinite _) ⟨N, hNS⟩
  have hKle : ∀ M ∈ S, M ≤ K → M = K := fun M hM hMK =>
    Subgroup.eq_of_le_of_card_ge hMK (hKmin hM (Subgroup.card_le_of_le hMK))
  obtain ⟨hKN, hK1, hKnorm⟩ := hKS
  by_cases hKG : ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ K
  · -- `K` is normal in `G`, hence `K = N` and `N` is simple
    have hKN' : K = N := (hmin K ⟨fun k hk g => hKG g k hk⟩ hKN).resolve_left hK1
    have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN1
    refine { eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
    by_cases hH1 : H = ⊥
    · exact Or.inl hH1
    right
    have hHS : H.map N.subtype ∈ S := by
      refine ⟨Subgroup.map_subtype_le H, ?_, ?_⟩
      · exact (Subgroup.map_eq_bot_iff_of_injective H N.subtype_injective).not.mpr hH1
      · rintro n hn _ ⟨h, hh, rfl⟩
        exact ⟨⟨n, hn⟩ * h * ⟨n, hn⟩⁻¹, hH.conj_mem h hh ⟨n, hn⟩, rfl⟩
    have hHK := hKle _ hHS (hKN'.symm ▸ Subgroup.map_subtype_le H)
    rw [eq_top_iff]
    intro h _
    have hh : (h : G) ∈ H.map N.subtype := by rw [hHK, hKN']; exact h.2
    obtain ⟨h', hh', he⟩ := Subgroup.mem_map.mp hh
    rwa [← Subtype.ext he]
  -- otherwise `K` is not normal: we derive a contradiction
  exfalso
  push Not at hKG
  obtain ⟨g₀, k₀, hk₀, hg₀⟩ := hKG
  -- every conjugate of `K` is `K` or centralises `K`
  have hconj : ∀ g : G, (∀ k ∈ K, g * k * g⁻¹ ∈ K) ∨
      (∀ k ∈ K, ∀ k' ∈ K, Commute (g * k * g⁻¹) k') := by
    intro g
    set K' := K.map (MulAut.conj g).toMonoidHom
    have hmemK' : ∀ k ∈ K, g * k * g⁻¹ ∈ K' := fun k hk => ⟨k, hk, rfl⟩
    have hK'norm : ∀ n ∈ N, ∀ m ∈ K', n * m * n⁻¹ ∈ K' := by
      rintro n hn _ ⟨k, hk, rfl⟩
      have hn' : g⁻¹ * n * g ∈ N := by simpa using hnormconj g⁻¹ n hn
      refine ⟨(g⁻¹ * n * g) * k * (g⁻¹ * n * g)⁻¹, hKnorm _ hn' k hk, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    by_cases h : K ⊓ K' = ⊥
    · right
      intro k hk k' hk'
      have hxN : g * k * g⁻¹ ∈ N := hnormconj g k (hKN hk)
      have hxK' := hmemK' k hk
      have hc : g * k * g⁻¹ * k' * (g * k * g⁻¹)⁻¹ * k'⁻¹ ∈ K ⊓ K' := by
        refine ⟨K.mul_mem (hKnorm _ hxN k' hk') (K.inv_mem hk'), ?_⟩
        have := K'.mul_mem hxK' (hK'norm k' (hKN hk') _ (K'.inv_mem hxK'))
        show _ ∈ K'
        simpa only [mul_assoc] using this
      rw [h, Subgroup.mem_bot, ← commutatorElement_def] at hc
      exact commutatorElement_eq_one_iff_commute.mp hc
    · left
      have hKK' : K ⊓ K' = K :=
        hKle _ ⟨inf_le_left.trans hKN, h, fun n hn m hm =>
          ⟨hKnorm n hn m hm.1, hK'norm n hn m hm.2⟩⟩ inf_le_left
      have hcard : Nat.card K' = Nat.card K :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      have heq : K = K' := Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp hKK') hcard.le
      intro k hk
      rw [heq]
      exact hmemK' k hk
  -- the key lemma: `K` is semiregular, hence of prime exponent
  have hfree := semiregular_of_conj_le_or_commute h2 hK1 hconj ⟨g₀, k₀, hk₀, hg₀⟩
  obtain ⟨p, hp, hexp⟩ := exists_prime_pow_eq_one hK1 fun a ha b hb ha1 hb1 =>
    orderOf_eq_of_semiregular h2 hconj hfree x₀ ha hb ha1 hb1
  obtain ⟨z, hzK, hz1, hzc⟩ := exists_central_of_exponent hK1 hp hexp
  -- so `Z(K) = K` by minimality: `K` is abelian
  set Z := K ⊓ Subgroup.centralizer (K : Set G)
  have hZS : Z ∈ S := by
    refine ⟨inf_le_left.trans hKN, fun h => ?_, fun n hn m hm => ⟨hKnorm n hn m hm.1, ?_⟩⟩
    · have hz : z ∈ Z := ⟨hzK, Subgroup.mem_centralizer_iff.mpr fun m hm => (hzc m hm).symm⟩
      rw [h, Subgroup.mem_bot] at hz
      exact hz1 hz
    · show n * m * n⁻¹ ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := Subgroup.mem_centralizer_iff.mp hm.2 (n⁻¹ * h * n)
        (by simpa using hKnorm n⁻¹ (N.inv_mem hn) h hh)
      calc h * (n * m * n⁻¹) = n * ((n⁻¹ * h * n) * m) * n⁻¹ := by group
        _ = n * (m * (n⁻¹ * h * n)) * n⁻¹ := by rw [h1]
        _ = n * m * n⁻¹ * h := by group
  have hKZ : K ≤ Z := (hKle Z hZS inf_le_left).ge
  have hKab : ∀ k ∈ K, ∀ k' ∈ K, Commute k k' := fun k hk k' hk' =>
    (Subgroup.mem_centralizer_iff.mp (hKZ hk).2 k' hk').symm
  -- the normal closure of `K` is abelian and equals `N`: contradiction
  have hgen : ∀ x ∈ Group.conjugatesOfSet (K : Set G),
      ∀ y ∈ Group.conjugatesOfSet (K : Set G), x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, hkx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨k', hk', hky⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hkx
    obtain ⟨h, rfl⟩ := isConj_iff.mp hky
    have key : Commute k ((g⁻¹ * h) * k' * (g⁻¹ * h)⁻¹) := by
      rcases hconj (g⁻¹ * h) with hc | hc
      · exact hKab k hk _ (hc k' hk')
      · exact (hc k' hk' k hk).symm
    have e : g * ((g⁻¹ * h) * k' * (g⁻¹ * h)⁻¹) * g⁻¹ = h * k' * h⁻¹ := by group
    have := key.map (MulAut.conj g).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e] at this
    exact this.eq
  have hAN : Subgroup.normalClosure (K : Set G) ≤ N := Subgroup.normalClosure_le_normal hKN
  have hA1 : Subgroup.normalClosure (K : Set G) ≠ ⊥ := fun h =>
    hK1 (eq_bot_iff.mpr (fun k hk => h ▸ Subgroup.subset_normalClosure hk))
  have hAeq := (hmin _ inferInstance hAN).resolve_left hA1
  letI := Subgroup.closureCommGroupOfComm (k := Group.conjugatesOfSet (K : Set G))
    fun x hx y hy _ => hgen x hx y hy
  have ha' : a ∈ Subgroup.closure (Group.conjugatesOfSet (K : Set G)) := by
    rw [← hAeq] at ha; exact ha
  have hb' : b ∈ Subgroup.closure (Group.conjugatesOfSet (K : Set G)) := by
    rw [← hAeq] at hb; exact hb
  exact hab (congrArg Subtype.val (mul_comm (⟨a, ha'⟩ :
    Subgroup.closure (Group.conjugatesOfSet (K : Set G))) ⟨b, hb'⟩))

/-- The minimal normal subgroup of a finite 2-transitive group is unique. -/
theorem burnside_minimal_normal_unique (h2 : IsMultiplyPretransitive G Ω 2)
    {N M : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hNmin : ∀ L : Subgroup G, L.Normal → L ≤ N → L = ⊥ ∨ L = N)
    (hM : M.Normal) (hM1 : M ≠ ⊥)
    (hMmin : ∀ L : Subgroup G, L.Normal → L ≤ M → L = ⊥ ∨ L = M) : M = N := by
  rcases hNmin (M ⊓ N) inferInstance inf_le_right with h | h
  · exfalso
    have hMC : M ≤ Subgroup.centralizer (N : Set G) := fun m hm =>
      Subgroup.mem_centralizer_iff.mpr fun n hn =>
        (Subgroup.commute_of_normal_of_disjoint M N hM hN (disjoint_iff.mpr h) m n hm hn).eq.symm
    rcases burnside_minimal_normal h2 N hN hN1 hNmin with ⟨p, -, hab, -, hreg⟩ | ⟨-, -, hC⟩
    · -- the centraliser of a regular abelian group is itself
      have hMN : M ≤ N := by
        intro c hc
        obtain ⟨x⟩ := nonempty_of_ne_bot (Ω := Ω) hN1
        obtain ⟨⟨n, hn⟩, hnx, -⟩ := hreg x (c • x)
        have hcn : n⁻¹ * c ∈ Subgroup.centralizer (N : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr
            fun m hm => hab m hm n hn)) (hMC hc)
        have := eq_one_of_transitive_centralizer (Ω := Ω) (K := Subgroup.centralizer (N : Set G))
          (C := N) (fun c hc k hk => (Subgroup.mem_centralizer_iff.mp hk c hc).symm)
          (fun x y => by
            obtain ⟨⟨n, hn⟩, hnx, -⟩ := hreg x y
            exact ⟨n, hn, hnx⟩) hcn (x := x) (by rw [mul_smul, ← hnx, inv_smul_smul])
        rw [inv_mul_eq_one] at this
        exact this ▸ hn
      exact hM1 (by rw [← h, inf_eq_left.mpr hMN])
    · exact hM1 (eq_bot_iff.mpr (hC ▸ hMC))
  · have hNM : N ≤ M := inf_eq_right.mp h
    exact ((hMmin N hN hNM).resolve_left hN1).symm

end Burnside

open CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

/-! ### `Out` respects isomorphism (as in `CFSG.ComponentClassification.OuterAutomorphisms`) -/

theorem congr_conj {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) (element : G) :
    MulAut.congr equivalence (MulAut.conj element) = MulAut.conj (equivalence element) := by
  apply MulEquiv.ext
  intro member
  change equivalence (element * equivalence.symm member * element⁻¹) =
    equivalence element * member * (equivalence element)⁻¹
  rw [map_mul, map_mul, map_inv, equivalence.apply_symm_apply]

theorem inner_map_congr {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (inner G).map (MulAut.congr equivalence).toMonoidHom = inner H := by
  ext automorphism
  constructor
  · rintro ⟨lift, ⟨element, rfl⟩, rfl⟩
    exact ⟨equivalence element, (congr_conj equivalence element).symm⟩
  · rintro ⟨element, rfl⟩
    refine ⟨MulAut.conj (equivalence.symm element), ⟨equivalence.symm element, rfl⟩, ?_⟩
    exact (congr_conj equivalence (equivalence.symm element)).trans
      (congrArg MulAut.conj (equivalence.apply_symm_apply element))

theorem solvable_of_equiv {G H : Type*} [Group G] [Group H] (groupEquivalence : G ≃* H)
    [Group.IsSolvable (Outer G)] : Group.IsSolvable (Outer H) :=
  Group.isSolvable_of_surjective
    (QuotientGroup.congr (inner G) (inner H) (MulAut.congr groupEquivalence)
      (inner_map_congr groupEquivalence)).surjective

/-! ### Arithmetic: `2 ^ a - 1` is not a proper prime power -/

/-- If `q` is prime and `b ≥ 2`, then `q ^ b + 1` is not a power of two. -/
theorem two_pow_ne_prime_pow_add_one {q a b : ℕ} (hq : q.Prime) (hb : 2 ≤ b) :
    2 ^ a ≠ q ^ b + 1 := by
  intro h
  have hq2 : q ≠ 2 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have : 0 < 2 ^ b := by positivity
      omega
    · have h1 : 2 ∣ 2 ^ a := dvd_pow_self 2 ha.ne'
      have h2 : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
      omega
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hqodd with ⟨k, hk⟩
    omega
  have hqb : q ^ 2 ≤ q ^ b := Nat.pow_le_pow_right (by omega) hb
  have hq9 : 9 ≤ q ^ 2 := by nlinarith
  rcases Nat.even_or_odd b with ⟨c, hc⟩ | hbodd
  · obtain ⟨y, hy⟩ : Odd (q ^ c) := hqodd.pow
    have hsq : q ^ b = (q ^ c) ^ 2 := by rw [← pow_mul, hc]; ring_nf
    rw [hsq, hy] at h
    have ha : 2 ≤ a := by
      by_contra ha
      interval_cases a <;> nlinarith
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [pow_add] at h
    have : 4 * 2 ^ d = 4 * (y ^ 2 + y) + 2 := by nlinarith
    omega
  · have hdvd : q + 1 ∣ 2 ^ a := by
      have := Odd.nat_add_dvd_pow_add_pow q 1 hbodd
      simpa [one_pow, h] using this
    obtain ⟨e, he, hqe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    obtain ⟨c, hc⟩ := hbodd
    have hmod : q ^ 2 ≡ 1 [MOD 2 ^ (e + 1)] := by
      obtain ⟨k, hk⟩ := hqodd
      have hq1 : q ^ 2 = 1 + (q + 1) * (q - 1) := by
        have : 1 ≤ q := by omega
        zify [this]
        ring
      rw [hq1, hqe]
      have : q - 1 = 2 * k := by omega
      rw [this]
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd' (by omega)]
      refine ⟨k, ?_⟩
      rw [Nat.add_sub_cancel_left, pow_succ]
      ring
    have hqbm : q ^ b ≡ q [MOD 2 ^ (e + 1)] := by
      have := (hmod.pow c).mul_left q
      rw [one_pow, mul_one, ← pow_mul, ← pow_succ'] at this
      rwa [hc]
    have hlt : q + 1 < 2 ^ a := by
      have : q < q ^ b := by
        calc q < q ^ 2 := by nlinarith
          _ ≤ q ^ b := hqb
      omega
    have hea : e + 1 ≤ a := by
      by_contra hea
      have : a ≤ e := by omega
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
      omega
    have h1 : 2 ^ (e + 1) ∣ 2 ^ a := pow_dvd_pow 2 hea
    have h2 : (q ^ b + 1) % 2 ^ (e + 1) = (q + 1) % 2 ^ (e + 1) := (hqbm.add_right 1)
    rw [← h, Nat.mod_eq_zero_of_dvd h1, hqe,
      Nat.mod_eq_of_lt (by rw [pow_succ]; omega)] at h2
    have : 0 < 2 ^ e := by positivity
    omega

/-! ### The local hypothesis on `Out` -/

/-- **Transport of the local hypothesis.**  Suppose `Out(T)` is solvable for every nonabelian
simple subgroup `T` of `G`, and let `ι : K →* G` be injective.  Then `Out(N)` is solvable for
every nonabelian simple subgroup `N` of `K`, because `ι(N) ≅ N` is a simple subgroup of `G`. -/
theorem outer_solvable_of_injective {G K : Type*} [Group G] [Group K]
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    (ι : K →* G) (hι : Function.Injective ι) (N : Subgroup K) [IsSimpleGroup N]
    (hnc : ∃ a b : N, a * b ≠ b * a) : Group.IsSolvable (Outer N) := by
  let e : N ≃* N.map ι := Subgroup.equivMapOfInjective N ι hι
  haveI : Nontrivial (N.map ι) := e.injective.nontrivial
  haveI : IsSimpleGroup (N.map ι) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective
  haveI := hOut (N.map ι) inferInstance (by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩)
  exact solvable_of_equiv e.symm

/-- The classification statement gives the local hypothesis: for a simple subgroup `T` of a finite
group `G : Type`, `T` is in the CFSG catalogue, so `Out(T)` is solvable (Schreier). -/
theorem outer_solvable_of_classification [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    {G : Type} [Group G] [Finite G] (T : Subgroup G) [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Group.IsSolvable (Outer T) :=
  CFSGOutside.Corpus.Schreier.schreierFor_inCatalog_holds T hnc
    (TauCeti.classificationStatement_iff.1 hCFSG T)

/-! ### Abstract group theory: a 2-transitive normal subgroup with nonsolvable top -/

section Abstract

variable {M X : Type} [Group M] [MulAction M X] [FaithfulSMul M X]

private theorem exists_moved {c : M} (hc : c ≠ 1) : ∃ x : X, c • x ≠ x := by
  by_contra hall
  push Not at hall
  exact hc (FaithfulSMul.eq_of_smul_eq_smul (fun x => by rw [hall, one_smul]))

private theorem exists_not_mem [Fintype X] (s : Finset X) (hs : s.card < Fintype.card X) :
    ∃ z : X, z ∉ s := by
  by_contra hall
  push Not at hall
  have : (Finset.univ : Finset X) ⊆ s := fun x _ => hall x
  have := Finset.card_le_card this
  rw [Finset.card_univ] at this
  omega

/-- An element centralising a subgroup that is 2-transitive on at least three points is trivial. -/
private theorem eq_one_of_commute_two_transitive [Fintype X] [DecidableEq X] (H : Subgroup M)
    (hX : 3 ≤ Fintype.card X)
    (h2 : ∀ x y x' y' : X, x ≠ y → x' ≠ y' → ∃ h ∈ H, h • x = x' ∧ h • y = y')
    (c : M) (hc : ∀ h ∈ H, c * h = h * c) : c = 1 := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_moved (X := X) hne
  obtain ⟨y, hy⟩ := exists_not_mem ({x, c • x} : Finset X)
    (lt_of_le_of_lt (Finset.card_le_two) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨h, hH, hhx, hhy⟩ := h2 x (c • x) x y (Ne.symm hx) (Ne.symm hy.1)
  have : h • (c • x) = c • (h • x) := by rw [smul_smul, smul_smul, hc h hH]
  rw [hhx, hhy] at this
  exact hy.2 this

/-- **Non-abelian case.** If `N ≤ H` is a nonabelian simple normal subgroup of `M` with trivial
centraliser in `M`, then `M/H` is a quotient of a subgroup of `Out(N)`, hence solvable once
`Out(N)` is.  Only `Out(N)` for this one `N` is used. -/
theorem solvable_quotient_of_simple
    [Finite M] (H : Subgroup M) [H.Normal] (N : Subgroup M) [N.Normal] (hNH : N ≤ H)
    (hOut : Group.IsSolvable (Outer N))
    (hC : ∀ c : M, (∀ n ∈ N, c * n = n * c) → c = 1) : Group.IsSolvable (M ⧸ H) := by
  let ψ : M →* Outer N := (QuotientGroup.mk' (inner N)).comp MulAut.conjNormal
  have hker : ψ.ker ≤ H := by
    intro m hm
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hm
    obtain ⟨n, hn⟩ := hm
    have hcent : (n : M)⁻¹ * m = 1 := hC _ (fun x hx => by
      have h' : (n : M) * x * (n : M)⁻¹ = m * x * m⁻¹ := by
        have := congrArg (fun f : MulAut N => ((f ⟨x, hx⟩ : N) : M)) hn
        simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
      calc (n : M)⁻¹ * m * x = (n : M)⁻¹ * (m * x * m⁻¹) * m := by group
        _ = (n : M)⁻¹ * ((n : M) * x * (n : M)⁻¹) * m := by rw [h']
        _ = x * ((n : M)⁻¹ * m) := by group)
    have : m = n := (inv_mul_eq_one.1 hcent).symm
    exact hNH (this ▸ n.2)
  haveI := hOut
  haveI : Group.IsSolvable ψ.range :=
    Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype) Subtype.coe_injective
  let f : M ⧸ ψ.ker →* M ⧸ H := QuotientGroup.map _ _ (MonoidHom.id M) hker
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk m, rfl⟩
  have hg : Function.Surjective
      (f.comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom) :=
    hf.comp (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  exact Group.isSolvable_of_surjective hg

private theorem eq_one_of_fix (N : Subgroup M)
    (htr : ∀ x y : X, ∃ n ∈ N, n • x = y) {c : M}
    (hc : ∀ n ∈ N, c * n = n * c) {x : X} (hx : c • x = x) : c = 1 := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨n, hn, rfl⟩ := htr x y
  rw [one_smul, smul_smul, hc n hn, ← smul_smul, hx]

private theorem eq_of_smul_eq (N : Subgroup M) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (htr : ∀ x y : X, ∃ n ∈ N, n • x = y) {a b : M} (ha : a ∈ N) (hb : b ∈ N) {x : X}
    (h : a • x = b • x) : a = b := by
  have := eq_one_of_fix N htr (c := b⁻¹ * a)
    (fun n hn => by
      rw [mul_assoc, hcomm a ha n hn, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm b hb n hn, mul_assoc, mul_inv_cancel,
        mul_one])
    (x := x) (by rw [← smul_smul, h, smul_smul, inv_mul_cancel, one_smul])
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- **Abelian case of prime degree.** If `M` has an abelian transitive normal subgroup of prime
order, then `M` is solvable (it embeds in `AGL(1, q)`). -/
theorem solvable_of_prime_regular [Nonempty X] (N : Subgroup M) [N.Normal]
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (htr : ∀ x y : X, ∃ n ∈ N, n • x = y) (hp : (Nat.card N).Prime) :
    Group.IsSolvable M := by
  haveI : Fact (Nat.card N).Prime := ⟨hp⟩
  haveI : IsCyclic N := isCyclic_of_prime_card rfl
  let φ : M →* MulAut N := MulAut.conjNormal
  have hcr : ∀ a b : φ.range, a * b = b * a := by
    rintro ⟨f, -⟩ ⟨g, -⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨i, hi⟩ := MonoidHom.map_cyclic f.toMonoidHom
    obtain ⟨j, hj⟩ := MonoidHom.map_cyclic g.toMonoidHom
    have hi' : ∀ y, f y = y ^ i := hi
    have hj' : ∀ y, g y = y ^ j := hj
    change f (g x) = g (f x)
    rw [hi', hj', hj', hi', ← zpow_mul, ← zpow_mul, mul_comm]
  haveI : Group.IsSolvable φ.range := Group.isSolvable_of_comm hcr
  haveI : Group.IsSolvable N := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2))
  apply Group.isSolvable_of_ker_le_range N.subtype φ.rangeRestrict
  intro m hm
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hm
  have hcent : ∀ n ∈ N, m * n = n * m := by
    intro n hn
    have := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : M)) hm
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc m * n = m * n * m⁻¹ * m := by group
      _ = n * m := by rw [this]
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, hnx⟩ := htr x (m • x)
  have : m = n := by
    have h1 := eq_one_of_fix N htr (c := n⁻¹ * m)
      (fun k hk => by
        rw [mul_assoc, hcent k hk, ← mul_assoc, ← mul_assoc]
        congr 1
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm n hn k hk, mul_assoc, mul_inv_cancel,
          mul_one])
      (x := x) (by rw [← smul_smul, ← hnx, smul_smul, inv_mul_cancel, one_smul])
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  exact ⟨⟨n, hn⟩, this.symm⟩

/-- **Abelian case under 3-transitivity.** A regular abelian normal subgroup of exponent `p`
of a group whose subgroup `H` is 3-transitive on at least four points has `p = 2`. -/
theorem prime_eq_two_of_three_transitive [Fintype X] [DecidableEq X] (H : Subgroup M)
    (N : Subgroup M) [N.Normal] (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (htr : ∀ x y : X, ∃ n ∈ N, n • x = y) {p : ℕ} (hp : p.Prime) (hexp : ∀ a ∈ N, a ^ p = 1)
    (hX : 4 ≤ Fintype.card X)
    (h3 : ∀ x y z x' y' z' : X, x ≠ y → x ≠ z → y ≠ z → x' ≠ y' → x' ≠ z' → y' ≠ z' →
      ∃ h ∈ H, h • x = x' ∧ h • y = y' ∧ h • z = z') : p = 2 := by
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x⟩ := this
  obtain ⟨y, hy⟩ := exists_not_mem ({x} : Finset X) (by simp; omega)
  simp only [Finset.mem_singleton] at hy
  obtain ⟨n, hn, hnx⟩ := htr x y
  have hn1 : n ≠ 1 := by rintro rfl; exact hy (by rw [← hnx, one_smul])
  have hnn : n * n = 1 := by
    by_contra hnn
    set z := n⁻¹ • x with hz
    have hzx : z ≠ x := by
      intro h
      have h' : n⁻¹ • x = x := h
      apply hy
      rw [← hnx]
      exact (inv_smul_eq_iff.1 h').symm
    have hzy : z ≠ y := by
      intro h
      apply hnn
      apply eq_one_of_fix N htr (c := n * n) (x := x)
      · intro k hk
        rw [mul_assoc, hcomm n hn k hk, ← mul_assoc, hcomm n hn k hk, mul_assoc]
      · rw [← smul_smul, hnx, ← h, hz, smul_inv_smul]
    obtain ⟨w, hw⟩ := exists_not_mem ({x, y, z} : Finset X)
      (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    obtain ⟨h, hH, hhx, hhy, hhz⟩ := h3 x y z x y w (Ne.symm hy) (Ne.symm hzx) (Ne.symm hzy)
      (Ne.symm hy) (Ne.symm hw.1) (Ne.symm hw.2.1)
    have hconj : h * n * h⁻¹ = n := by
      apply eq_of_smul_eq N hcomm htr (Subgroup.Normal.conj_mem ‹_› n hn h) hn (x := x)
      have : h⁻¹ • x = x := by rw [inv_smul_eq_iff, hhx]
      rw [← smul_smul, ← smul_smul, this, hnx, hhy]
    have : h • z = z := by
      have e1 : h * n⁻¹ = n⁻¹ * h := by
        have : h * n⁻¹ * h⁻¹ = n⁻¹ := by
          rw [show h * n⁻¹ * h⁻¹ = (h * n * h⁻¹)⁻¹ by group, hconj]
        calc h * n⁻¹ = h * n⁻¹ * h⁻¹ * h := by group
          _ = n⁻¹ * h := by rw [this]
      rw [hz, smul_smul, e1, ← smul_smul, hhx]
    exact hw.2.2 (hhz.symm.trans this)
  have hord : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hnn])
  rcases (Nat.dvd_prime Nat.prime_two).1 hord with h1 | h2
  · exact absurd (orderOf_eq_one_iff.1 h1) hn1
  · have : 2 ∣ p := h2 ▸ orderOf_dvd_of_pow_eq_one (hexp n hn)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

/-- **The socle of the 2-transitive normal subgroup `H`.**  Burnside's theorem applied to the
unique minimal normal subgroup of `H`; uniqueness makes it characteristic in `H`, hence normal
in `M`. -/
theorem exists_socle [Finite M] [Fintype X] [DecidableEq X] (H : Subgroup M) [H.Normal]
    (hX : 3 ≤ Fintype.card X)
    (h2 : ∀ x y x' y' : X, x ≠ y → x' ≠ y' → ∃ h ∈ H, h • x = x' ∧ h • y = y') :
    ∃ N : Subgroup M, N.Normal ∧ N ≤ H ∧
      ((∃ p : ℕ, p.Prime ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ a ∈ N, a ^ p = 1) ∧
          ∀ x y : X, ∃ n ∈ N, n • x = y) ∨
        (IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧
          ∀ c ∈ H, (∀ n ∈ N, c * n = n * c) → c = 1)) := by
  classical
  have h2H : IsMultiplyPretransitive H X 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨h, hH, h1, h2⟩ := h2 a b c d hab hcd
    exact ⟨⟨h, hH⟩, h1, h2⟩
  have : Finite (Subgroup H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  have hHtop : (⊤ : Subgroup H) ≠ ⊥ := by
    have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨x⟩ := this
    obtain ⟨y, hy⟩ := exists_not_mem ({x} : Finset X) (by simp; omega)
    simp only [Finset.mem_singleton] at hy
    obtain ⟨h, hH, hhx, -⟩ := h2 x y y x (Ne.symm hy) hy
    intro hbot
    have : (⟨h, hH⟩ : H) = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top _)
    have : h = 1 := congrArg Subtype.val this
    exact hy (by rw [← hhx, this, one_smul])
  obtain ⟨N0, ⟨hN0n, hN01⟩, hN0min⟩ := Set.Finite.exists_minimalFor
    (fun K : Subgroup H => Nat.card K) {K : Subgroup H | K.Normal ∧ K ≠ ⊥}
    (Set.toFinite _) ⟨⊤, inferInstance, hHtop⟩
  have hmin : ∀ K : Subgroup H, K.Normal → K ≤ N0 → K = ⊥ ∨ K = N0 := by
    intro K hK hKN
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    exact Or.inr (Subgroup.eq_of_le_of_card_ge hKN
      (hN0min ⟨hK, hK1⟩ (Subgroup.card_le_of_le hKN)))
  -- `N0` is invariant under every automorphism of `H`
  have hchar : ∀ φ : MulAut H, N0.map φ.toMonoidHom = N0 := by
    intro φ
    apply burnside_minimal_normal_unique h2H hN0n hN01 hmin
      (hN0n.map φ.toMonoidHom φ.surjective)
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]; exact hN01
    · intro L hL hLle
      have hL' : L.map φ.symm.toMonoidHom ≤ N0 := by
        rintro _ ⟨l, hl, rfl⟩
        obtain ⟨n, hn, hnl⟩ := hLle hl
        have : φ.symm l = n := by
          rw [← hnl]; exact φ.symm_apply_apply n
        rw [MulEquiv.coe_toMonoidHom, this]; exact hn
      rcases hmin _ (hL.map _ φ.symm.surjective) hL' with h | h
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective).1 h
      · right
        apply le_antisymm hLle
        rintro _ ⟨n, hn, rfl⟩
        rw [← h] at hn
        obtain ⟨l, hl, rfl⟩ := hn
        simpa using hl
  let N : Subgroup M := N0.map H.subtype
  have hNH : N ≤ H := Subgroup.map_subtype_le N0
  have hNn : N.Normal := by
    constructor
    rintro _ ⟨a, ha, rfl⟩ m
    have hmem : MulAut.conjNormal m a ∈ N0 := by
      rw [← hchar (MulAut.conjNormal m)]
      exact ⟨a, ha, rfl⟩
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  refine ⟨N, hNn, hNH, ?_⟩
  rcases burnside_minimal_normal h2H N0 hN0n hN01 hmin with ⟨p, hp, hab, hexp, hreg⟩ |
      ⟨hsimple, hnc, hC⟩
  · left
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hab a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hexp a ha)
    · intro x y
      obtain ⟨⟨n, hn⟩, hnx, -⟩ := hreg x y
      exact ⟨n, ⟨n, hn, rfl⟩, hnx⟩
  · right
    let e : N0 ≃* N := Subgroup.equivMapOfInjective N0 H.subtype H.subtype_injective
    haveI : Nontrivial N0 := (Subgroup.nontrivial_iff_ne_bot N0).2 hN01
    haveI : Nontrivial N := e.injective.nontrivial
    refine ⟨IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective, ?_, ?_⟩
    · obtain ⟨a, b, hab⟩ := hnc
      exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
    · intro c hc hcomm
      have : (⟨c, hc⟩ : H) ∈ Subgroup.centralizer (N0 : Set H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact Subtype.ext (hcomm n ⟨n, hn, rfl⟩).symm
      rw [hC] at this
      exact congrArg Subtype.val (Subgroup.mem_bot.1 this)

/-- If `N ≤ H` is normal in `M` and `C_H(N) = 1`, with `H ⊴ M` 2-transitive on `|X| ≥ 3` points,
then `C_M(N) = 1`: for `c ∈ C_M(N)`, each commutator `[c, h]` (`h ∈ H`) lies in `C_H(N) = 1`, so
`c` centralises `H`, hence `c = 1`. -/
theorem eq_one_of_centralizes_socle [Fintype X] [DecidableEq X] (H : Subgroup M) [H.Normal]
    (hX : 3 ≤ Fintype.card X)
    (h2 : ∀ x y x' y' : X, x ≠ y → x' ≠ y' → ∃ h ∈ H, h • x = x' ∧ h • y = y')
    (N : Subgroup M) (hNn : N.Normal) (hCH : ∀ c ∈ H, (∀ n ∈ N, c * n = n * c) → c = 1)
    (c : M) (hc : ∀ n ∈ N, c * n = n * c) : c = 1 := by
  apply eq_one_of_commute_two_transitive H hX h2 c
  intro h hh
  have hk : c * h * c⁻¹ * h⁻¹ ∈ H :=
    H.mul_mem ((inferInstance : H.Normal).conj_mem h hh c) (H.inv_mem hh)
  have hkc : ∀ n ∈ N, c * h * c⁻¹ * h⁻¹ * n = n * (c * h * c⁻¹ * h⁻¹) := by
    intro n hn
    have h1 : h⁻¹ * n * h ∈ N := by simpa using hNn.conj_mem n hn h⁻¹
    have e1 : c⁻¹ * (h⁻¹ * n * h) = (h⁻¹ * n * h) * c⁻¹ := by
      calc c⁻¹ * (h⁻¹ * n * h) = c⁻¹ * ((h⁻¹ * n * h) * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * (h⁻¹ * n * h)) * c⁻¹ := by rw [hc _ h1]
        _ = (h⁻¹ * n * h) * c⁻¹ := by group
    have e2 := hc n hn
    calc c * h * c⁻¹ * h⁻¹ * n = c * h * (c⁻¹ * (h⁻¹ * n * h)) * h⁻¹ := by group
      _ = c * h * ((h⁻¹ * n * h) * c⁻¹) * h⁻¹ := by rw [e1]
      _ = c * n * h * c⁻¹ * h⁻¹ := by group
      _ = n * c * h * c⁻¹ * h⁻¹ := by rw [e2]
      _ = n * (c * h * c⁻¹ * h⁻¹) := by group
  have := hCH _ hk hkc
  calc c * h = (c * h * c⁻¹ * h⁻¹) * (h * c) := by group
    _ = h * c := by rw [this, one_mul]

/-- **Key lemma.** Let `M` act faithfully on `X` (`|X| ≥ 3`) with a normal subgroup `H` that is
2-transitive on `X`.  Assuming `Out(N)` solvable for the nonabelian simple subgroups `N` of `M`,
either `M/H` is solvable, or `|X| = p ^ b`
with `p` prime and `b ≥ 2`; moreover `p = 2` when `H` is 3-transitive and `|X| ≥ 4`. -/
theorem solvable_quotient_or_prime_power
    (hS : ∀ T : Subgroup M, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    [Finite M] [Fintype X] [DecidableEq X] (H : Subgroup M) [H.Normal]
    (hX : 3 ≤ Fintype.card X)
    (h2 : ∀ x y x' y' : X, x ≠ y → x' ≠ y' → ∃ h ∈ H, h • x = x' ∧ h • y = y') :
    Group.IsSolvable (M ⧸ H) ∨
      ∃ p b : ℕ, p.Prime ∧ 2 ≤ b ∧ Fintype.card X = p ^ b ∧
        ((4 ≤ Fintype.card X ∧ ∀ x y z x' y' z' : X, x ≠ y → x ≠ z → y ≠ z → x' ≠ y' →
          x' ≠ z' → y' ≠ z' → ∃ h ∈ H, h • x = x' ∧ h • y = y' ∧ h • z = z') → p = 2) := by
  obtain ⟨N, hNn, hNH, hcase⟩ := exists_socle H hX h2
  rcases hcase with ⟨p, hp, hab, hexp, htr⟩ | ⟨hsimple, hnc, hCH⟩
  · have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨x0⟩ := this
    -- `N` is regular, so `|N| = |X|`
    have hcard : Nat.card N = Fintype.card X := by
      rw [← Nat.card_eq_fintype_card]
      apply Nat.card_eq_of_bijective (fun n : N => (n : M) • x0)
      refine ⟨fun a b h => Subtype.ext (eq_of_smul_eq N hab htr a.2 b.2 h), fun y => ?_⟩
      obtain ⟨n, hn, hny⟩ := htr x0 y
      exact ⟨⟨n, hn⟩, hny⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p N := fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (by simpa using hexp g g.2)⟩
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hpg
    rw [hcard] at hb
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · left
      interval_cases b
      · simp at hb; omega
      · haveI := hNn
        have hNp : (Nat.card N).Prime := by rw [hcard, hb, pow_one]; exact hp
        haveI : Nonempty X := ⟨x0⟩
        haveI := solvable_of_prime_regular N hab htr hNp
        exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective H)
    · right
      refine ⟨p, b, hp, hb2, hb, fun ⟨hX4, h3⟩ => ?_⟩
      haveI := hNn
      exact prime_eq_two_of_three_transitive H N hab htr hp hexp hX4 h3
  · left
    haveI := hNn
    exact solvable_quotient_of_simple H N hNH (hS N hsimple hnc)
      (eq_one_of_centralizes_socle H hX h2 N hNn hCH)

end Abstract

/-! ### The permutation-group set-up: stabilisers of a `d`-subset -/

section Geometry

open Equiv

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The setwise stabiliser of `D` in `Sym(Ω)`. -/
def setStab (D : Set Ω) : Subgroup (Perm Ω) where
  carrier := {g | ∀ x, g x ∈ D ↔ x ∈ D}
  mul_mem' := fun {a b} ha hb x => by
    simp only [Set.mem_setOf_eq, Perm.mul_apply] at *
    rw [ha, hb]
  one_mem' := fun x => by simp
  inv_mem' := fun {a} ha x => by
    have := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
    exact this.symm

/-- `G` is `k`-transitive for every `k ≤ m`, phrased for tuples indexed by any finite type. -/
def TransUpTo (G : Subgroup (Perm Ω)) (m : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ m → ∀ a b : ι → Ω, Function.Injective a →
    Function.Injective b → ∃ g ∈ G, ∀ i, g (a i) = b i

theorem transUpTo_of_isMultiplyPretransitive (G : Subgroup (Perm Ω)) {m : ℕ}
    (hm : m ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω m) :
    TransUpTo G m := by
  intro ι _ hι a b ha hb
  haveI := hG
  have hk : MulAction.IsMultiplyPretransitive G Ω (Fintype.card ι) :=
    MulAction.isMultiplyPretransitive_of_le hι (by rw [Nat.card_eq_fintype_card]; exact hm)
  let eq := Fintype.equivFin ι
  let ea : Fin (Fintype.card ι) ↪ Ω := ⟨a ∘ eq.symm, ha.comp eq.symm.injective⟩
  let eb : Fin (Fintype.card ι) ↪ Ω := ⟨b ∘ eq.symm, hb.comp eq.symm.injective⟩
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.1 hk) ea eb
  refine ⟨g, g.2, fun i => ?_⟩
  have := DFunLike.congr_fun hg (eq i)
  simpa [ea, eb, Function.Embedding.smul_apply, Subgroup.smul_def, Perm.smul_def] using this

variable (G : Subgroup (Perm Ω)) (D : Set Ω)

/-- The action of the setwise stabiliser on the complement of `D`. -/
@[reducible] def outAction : MulAction (G ⊓ setStab D : Subgroup (Perm Ω)) {x : Ω // x ∉ D} where
  smul m x := ⟨(m : Perm Ω) x, fun h => x.2 (((Subgroup.mem_inf.1 m.2).2 x).1 h)⟩
  one_smul x := rfl
  mul_smul a b x := rfl

/-- The action of the setwise stabiliser on `D`. -/
@[reducible] def inAction : MulAction (G ⊓ setStab D : Subgroup (Perm Ω)) {x : Ω // x ∈ D} where
  smul m x := ⟨(m : Perm Ω) x, ((Subgroup.mem_inf.1 m.2).2 x).2 x.2⟩
  one_smul x := rfl
  mul_smul a b x := rfl

/-- The action of the setwise stabiliser on `D`, as a homomorphism to `Sym(D)`. -/
def restrictHom : (G ⊓ setStab D : Subgroup (Perm Ω)) →* Perm {x : Ω // x ∈ D} :=
  @MulAction.toPermHom _ _ _ (inAction G D)

variable {G D}

theorem restrictHom_apply (m : (G ⊓ setStab D : Subgroup (Perm Ω))) (x : {x : Ω // x ∈ D}) :
    (restrictHom G D m x : Ω) = (m : Perm Ω) x := rfl

/-- An element of `G` fixing `D` pointwise lies in the kernel of `restrictHom`. -/
theorem mem_ker_of_fix {g : Perm Ω} (hg : g ∈ G) (hfix : ∀ x ∈ D, g x = x) :
    ∃ hm : g ∈ G ⊓ setStab D, (⟨g, hm⟩ : (G ⊓ setStab D : Subgroup (Perm Ω))) ∈
      (restrictHom G D).ker := by
  have hs : g ∈ setStab D := by
    intro x
    constructor
    · intro hx
      have : g (g x) = g x := hfix _ hx
      rw [g.injective this] at hx
      exact hx
    · intro hx; rw [hfix x hx]; exact hx
  refine ⟨Subgroup.mem_inf.2 ⟨hg, hs⟩, ?_⟩
  rw [MonoidHom.mem_ker]
  ext ⟨x, hx⟩
  simp only [restrictHom_apply, Perm.coe_one, id_eq]
  exact hfix x hx

end Geometry

section Geometry2

open Equiv

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)}

theorem TransUpTo.mono {m k : ℕ} (h : TransUpTo G m) (hk : k ≤ m) : TransUpTo G k :=
  fun ι _ hι => h ι (hι.trans hk)

private theorem injective_two {a b : Ω} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem injective_three {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- An element of `G` fixing the `d`-set `range e` pointwise and moving a given `k`-tuple outside
it to another one. -/
theorem exists_ker_tuple {d k : ℕ} (e : Fin d → Ω) (he : Function.Injective e)
    (hT : TransUpTo G (d + k)) (c c' : Fin k → Ω) (hc : Function.Injective c)
    (hc' : Function.Injective c') (hcD : ∀ j, c j ∉ Set.range e)
    (hc'D : ∀ j, c' j ∉ Set.range e) :
    ∃ m : (G ⊓ setStab (Set.range e) : Subgroup (Perm Ω)),
      m ∈ (restrictHom G (Set.range e)).ker ∧ ∀ j, (m : Perm Ω) (c j) = c' j := by
  obtain ⟨g, hg, hgi⟩ := hT (Fin d ⊕ Fin k) (by simp) (Sum.elim e c) (Sum.elim e c')
    (Function.Injective.sumElim he hc (fun i j h => hcD j ⟨i, h⟩))
    (Function.Injective.sumElim he hc' (fun i j h => hc'D j ⟨i, h⟩))
  obtain ⟨hm, hker⟩ := mem_ker_of_fix (D := Set.range e) hg (by
    rintro x ⟨i, rfl⟩
    simpa using hgi (Sum.inl i))
  exact ⟨⟨g, hm⟩, hker, fun j => by simpa using hgi (Sum.inr j)⟩

/-- The setwise stabiliser of a `d`-set induces the full symmetric group on it. -/
theorem restrictHom_surjective {d : ℕ} (e : Fin d → Ω) (he : Function.Injective e)
    (hT : TransUpTo G d) : Function.Surjective (restrictHom G (Set.range e)) := by
  intro σ
  let b : Fin d → Ω := fun i => (σ ⟨e i, ⟨i, rfl⟩⟩ : Ω)
  have hb : Function.Injective b := by
    intro i j hij
    have := σ.injective (Subtype.ext hij)
    exact he (congrArg Subtype.val this)
  obtain ⟨g, hg, hgi⟩ := hT (Fin d) (by simp) e b he hb
  have hs : g ∈ setStab (Set.range e) := by
    intro x
    constructor
    · intro h
      set y := σ⁻¹ ⟨g x, h⟩ with hy
      obtain ⟨i, hi⟩ := y.2
      have hy' : (⟨e i, ⟨i, rfl⟩⟩ : {x // x ∈ Set.range e}) = y := Subtype.ext hi
      have : g (e i) = g x := by
        rw [hgi i]
        simp only [b]
        rw [hy', hy]
        exact congrArg Subtype.val (σ.apply_symm_apply _)
      exact ⟨i, g.injective this⟩
    · rintro ⟨i, rfl⟩
      rw [hgi i]
      exact (σ _).2
  refine ⟨⟨g, Subgroup.mem_inf.2 ⟨hg, hs⟩⟩, ?_⟩
  ext ⟨x, i, rfl⟩
  exact hgi i

/-- **The local step.**  Let `G ≤ Sym(Ω)` be `(d+2)`-transitive, `5 ≤ d ≤ 6`, `|Ω| ≥ d + 3`, and
let `Δ` be a `d`-subset.  Then either `Alt(Ω) ≤ G`, or `|Ω| - d = p ^ b` with `p` prime, `b ≥ 2`,
and `p = 2` if `G` is moreover `(d+3)`-transitive and `|Ω| - d ≥ 4`. -/
theorem local_step [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    (hS : ∀ T : Subgroup G, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    {d : ℕ} (hd5 : 5 ≤ d) (hd6 : d ≤ 6) (e : Fin d → Ω) (he : Function.Injective e)
    (hT : TransUpTo G (d + 2)) (hn : d + 3 ≤ Fintype.card Ω) (h8 : 8 ≤ Fintype.card Ω) :
    alternatingGroup Ω ≤ G ∨
      ∃ p b : ℕ, p.Prime ∧ 2 ≤ b ∧ Fintype.card Ω - d = p ^ b ∧
        (TransUpTo G (d + 3) → 4 ≤ Fintype.card Ω - d → p = 2) := by
  classical
  set D : Set Ω := Set.range e with hD
  let M := (G ⊓ setStab D : Subgroup (Perm Ω))
  letI : MulAction M {x : Ω // x ∉ D} := outAction G D
  have hcardD : Fintype.card {x : Ω // x ∈ D} = d := by
    calc Fintype.card {x : Ω // x ∈ D} = Fintype.card (Fin d) :=
          Fintype.card_congr (Equiv.ofInjective e he).symm
      _ = d := Fintype.card_fin d
  have hcardX : Fintype.card {x : Ω // x ∉ D} = Fintype.card Ω - d := by
    rw [Fintype.card_subtype_compl, hcardD]
  by_cases hF : ∀ m : M, (∀ x : {x : Ω // x ∉ D}, m • x = x) → m = 1
  · haveI : FaithfulSMul M {x : Ω // x ∉ D} := ⟨fun {m1 m2} h => by
      have := hF (m2⁻¹ * m1) (fun x => by rw [mul_smul, h, inv_smul_smul])
      exact (inv_mul_eq_one.1 this).symm⟩
    let H := (restrictHom G D).ker
    have h2 : ∀ x y x' y' : {x : Ω // x ∉ D}, x ≠ y → x' ≠ y' →
        ∃ h ∈ H, h • x = x' ∧ h • y = y' := by
      intro x y x' y' hxy hxy'
      obtain ⟨m, hm, hmc⟩ := exists_ker_tuple (k := 2) e he hT ![x.1, y.1] ![x'.1, y'.1]
        (injective_two fun h => hxy (Subtype.ext h))
        (injective_two fun h => hxy' (Subtype.ext h))
        (fun j => by fin_cases j; exacts [x.2, y.2])
        (fun j => by fin_cases j; exacts [x'.2, y'.2])
      exact ⟨m, hm, Subtype.ext (by simpa using hmc 0 : (m : Perm Ω) x.1 = x'.1),
        Subtype.ext (by simpa using hmc 1 : (m : Perm Ω) y.1 = y'.1)⟩
    have hX3 : 3 ≤ Fintype.card {x : Ω // x ∉ D} := by rw [hcardX]; omega
    have hSM : ∀ T : Subgroup M, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
        Group.IsSolvable (Outer T) := fun T hT hnc => by
      haveI := hT
      exact outer_solvable_of_injective hS (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left) T hnc
    rcases solvable_quotient_or_prime_power hSM H hX3 h2 with hsol | ⟨p, b, hp, hb, hcard, h2p⟩
    · exfalso
      have hsurj := restrictHom_surjective e he (hT.mono (by omega))
      let f : M ⧸ H →* Perm {x : Ω // x ∈ D} := QuotientGroup.lift H (restrictHom G D) le_rfl
      have hf : Function.Surjective f := fun σ => by
        obtain ⟨m, hm⟩ := hsurj σ
        exact ⟨QuotientGroup.mk m, by rw [QuotientGroup.lift_mk]; exact hm⟩
      haveI := hsol
      apply Equiv.Perm.not_isSolvable {x : Ω // x ∈ D}
      · rw [Cardinal.mk_fintype, hcardD]; exact_mod_cast hd5
      · exact Group.isSolvable_of_surjective hf
    · right
      refine ⟨p, b, hp, hb, hcardX ▸ hcard, fun hT3 h4 => h2p ⟨hcardX ▸ h4, ?_⟩⟩
      intro x y z x' y' z' hxy hxz hyz hxy' hxz' hyz'
      obtain ⟨m, hm, hmc⟩ := exists_ker_tuple (k := 3) e he hT3 ![x.1, y.1, z.1]
        ![x'.1, y'.1, z'.1]
        (injective_three (fun h => hxy (Subtype.ext h)) (fun h => hxz (Subtype.ext h))
          (fun h => hyz (Subtype.ext h)))
        (injective_three (fun h => hxy' (Subtype.ext h)) (fun h => hxz' (Subtype.ext h))
          (fun h => hyz' (Subtype.ext h)))
        (fun j => by fin_cases j; exacts [x.2, y.2, z.2])
        (fun j => by fin_cases j; exacts [x'.2, y'.2, z'.2])
      exact ⟨m, hm, Subtype.ext (by simpa using hmc 0 : (m : Perm Ω) x.1 = x'.1),
        Subtype.ext (by simpa using hmc 1 : (m : Perm Ω) y.1 = y'.1),
        Subtype.ext (by simpa using hmc 2 : (m : Perm Ω) z.1 = z'.1)⟩
  · -- a nontrivial element fixing `Ω ∖ Δ` pointwise has support of size at most 6
    left
    push Not at hF
    obtain ⟨m, hmfix, hm1⟩ := hF
    have hg : (m : Perm Ω) ∈ G := (Subgroup.mem_inf.1 m.2).1
    have hgne : (m : Perm Ω) ≠ 1 := fun h => hm1 (Subtype.ext h)
    have hsupp : (m : Perm Ω).support ⊆ Finset.univ.image e := by
      intro x hx
      rw [Perm.mem_support] at hx
      by_contra hxD
      have hxD' : x ∉ D := by
        rintro ⟨i, rfl⟩
        exact hxD (Finset.mem_image_of_mem e (Finset.mem_univ i))
      exact hx (congrArg Subtype.val (hmfix ⟨x, hxD'⟩))
    have hcard : (m : Perm Ω).support.card ≤ 6 := by
      calc (m : Perm Ω).support.card ≤ (Finset.univ.image e).card := Finset.card_le_card hsupp
        _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
        _ ≤ 6 := by simp [hd6]
    have h5 : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
        ∃ q : G, ∀ i, q • a i = b i := by
      intro a b ha hb
      obtain ⟨g, hg, hgi⟩ := hT (Fin 5) (by simp; omega) a b ha hb
      exact ⟨⟨g, hg⟩, fun i => by
        simp only [Subgroup.smul_def, Perm.smul_def]; exact hgi i⟩
    exact CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix.alternatingGroup_le_of_nontrivial_support_le_six
      G h8 h5 hg hgne hcard

/-- **Wielandt's Hilfssatz (2), working form.**  Let `G ≤ Sym(Ω)` be 7-transitive with
`|Ω| ≥ 8`, let `Δ = range e` be a 5-set, and assume `Out(T)` solvable for every nonabelian simple
subgroup `T ≤ G`.  Then either `Alt(Ω) ≤ G`, or the pointwise stabiliser `G_(Δ)` contains a
subgroup `N`, normalised by the setwise stabiliser `G_{Δ}`, which is abelian of prime exponent,
transitive on `Ω ∖ Δ` and not cyclic. -/
theorem hilfssatz [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    (hS : ∀ T : Subgroup G, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    (e : Fin 5 → Ω) (he : Function.Injective e)
    (hG : MulAction.IsMultiplyPretransitive G Ω 7) (h8 : 8 ≤ Fintype.card Ω) :
    alternatingGroup Ω ≤ G ∨
      ∃ (N : Subgroup (Perm Ω)) (p : ℕ), p.Prime ∧ N ≤ G ∧
        (∀ a ∈ N, ∀ i, a (e i) = e i) ∧
        (∀ m ∈ G, (∀ z, m z ∈ Set.range e ↔ z ∈ Set.range e) → ∀ a ∈ N, m * a * m⁻¹ ∈ N) ∧
        (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ a ∈ N, a ^ p = 1) ∧
        (∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y') ∧
        ¬ IsCyclic N := by
  classical
  have hT : TransUpTo G 7 := transUpTo_of_isMultiplyPretransitive G (by omega) hG
  set D : Set Ω := Set.range e with hD
  let M := (G ⊓ setStab D : Subgroup (Perm Ω))
  letI : MulAction M {x : Ω // x ∉ D} := outAction G D
  have hcardD : Fintype.card {x : Ω // x ∈ D} = 5 := by
    calc Fintype.card {x : Ω // x ∈ D} = Fintype.card (Fin 5) :=
          Fintype.card_congr (Equiv.ofInjective e he).symm
      _ = 5 := Fintype.card_fin 5
  have hcardX : Fintype.card {x : Ω // x ∉ D} = Fintype.card Ω - 5 := by
    rw [Fintype.card_subtype_compl, hcardD]
  by_cases hF : ∀ m : M, (∀ x : {x : Ω // x ∉ D}, m • x = x) → m = 1
  · haveI : FaithfulSMul M {x : Ω // x ∉ D} := ⟨fun {m1 m2} h => by
      have := hF (m2⁻¹ * m1) (fun x => by rw [mul_smul, h, inv_smul_smul])
      exact (inv_mul_eq_one.1 this).symm⟩
    let H := (restrictHom G D).ker
    have h2 : ∀ x y x' y' : {x : Ω // x ∉ D}, x ≠ y → x' ≠ y' →
        ∃ h ∈ H, h • x = x' ∧ h • y = y' := by
      intro x y x' y' hxy hxy'
      obtain ⟨m, hm, hmc⟩ := exists_ker_tuple (k := 2) e he hT ![x.1, y.1] ![x'.1, y'.1]
        (injective_two fun h => hxy (Subtype.ext h))
        (injective_two fun h => hxy' (Subtype.ext h))
        (fun j => by fin_cases j; exacts [x.2, y.2])
        (fun j => by fin_cases j; exacts [x'.2, y'.2])
      exact ⟨m, hm, Subtype.ext (by simpa using hmc 0 : (m : Perm Ω) x.1 = x'.1),
        Subtype.ext (by simpa using hmc 1 : (m : Perm Ω) y.1 = y'.1)⟩
    have hX3 : 3 ≤ Fintype.card {x : Ω // x ∉ D} := by rw [hcardX]; omega
    -- `M / H` maps onto `Sym(Δ) ≅ S₅`, so it is not solvable
    have hnot : ¬ Group.IsSolvable (M ⧸ H) := by
      intro hsol
      have hsurj := restrictHom_surjective e he (hT.mono (by omega))
      let f : M ⧸ H →* Perm {x : Ω // x ∈ D} := QuotientGroup.lift H (restrictHom G D) le_rfl
      have hf : Function.Surjective f := fun σ => by
        obtain ⟨m, hm⟩ := hsurj σ
        exact ⟨QuotientGroup.mk m, by rw [QuotientGroup.lift_mk]; exact hm⟩
      apply Equiv.Perm.not_isSolvable {x : Ω // x ∈ D}
      · rw [Cardinal.mk_fintype, hcardD]; norm_num
      · exact Group.isSolvable_of_surjective hf
    obtain ⟨N0, hN0n, hN0H, hcase⟩ := exists_socle H hX3 h2
    rcases hcase with ⟨p, hp, hab, hexp, htr⟩ | ⟨hsimple, hnc, hCH⟩
    · right
      refine ⟨N0.map M.subtype, p, hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rintro _ ⟨m, -, rfl⟩
        exact (Subgroup.mem_inf.1 m.2).1
      · rintro _ ⟨m, hm, rfl⟩ i
        have h1 := hN0H hm
        rw [MonoidHom.mem_ker] at h1
        have := congrArg (fun f : Perm {x : Ω // x ∈ D} => (f ⟨e i, ⟨i, rfl⟩⟩ : Ω)) h1
        simpa [restrictHom_apply] using this
      · rintro g hg hgD _ ⟨m, hm, rfl⟩
        let gM : M := ⟨g, Subgroup.mem_inf.2 ⟨hg, hgD⟩⟩
        exact ⟨gM * m * gM⁻¹, hN0n.conj_mem m hm gM, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hab a ha b hb)
      · rintro _ ⟨a, ha, rfl⟩
        exact congrArg Subtype.val (hexp a ha)
      · intro y y' hy hy'
        obtain ⟨m, hm, hmy⟩ := htr ⟨y, hy⟩ ⟨y', hy'⟩
        exact ⟨m, ⟨m, hm, rfl⟩, congrArg Subtype.val hmy⟩
      · -- a cyclic `N` would have prime order, and then `M ≤ AGL(1, p)` would be solvable
        intro hcyc
        haveI := hN0n
        let φ : N0 ≃* N0.map M.subtype :=
          Subgroup.equivMapOfInjective N0 M.subtype M.subtype_injective
        haveI : IsCyclic N0 := isCyclic_of_surjective φ.symm.toMonoidHom φ.symm.surjective
        have hdvd : Monoid.exponent N0 ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (by simpa using hexp g g.2)
        rw [IsCyclic.exponent_eq_card] at hdvd
        have : Nonempty {x : Ω // x ∉ D} := Fintype.card_pos_iff.1 (by omega)
        obtain ⟨x0⟩ := this
        have hcard : Fintype.card {x : Ω // x ∉ D} ≤ Nat.card N0 := by
          rw [← Nat.card_eq_fintype_card]
          refine Nat.card_le_card_of_surjective (fun n : N0 => (n : M) • x0) fun y => ?_
          obtain ⟨n, hn, hny⟩ := htr x0 y
          exact ⟨⟨n, hn⟩, hny⟩
        have hNp : (Nat.card N0).Prime := by
          rcases (Nat.dvd_prime hp).1 hdvd with h | h
          · omega
          · exact h ▸ hp
        haveI : Nonempty {x : Ω // x ∉ D} := ⟨x0⟩
        haveI := solvable_of_prime_regular N0 hab htr hNp
        exact hnot (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective H))
    · exfalso
      haveI := hN0n
      exact hnot (solvable_quotient_of_simple H N0 hN0H
        (outer_solvable_of_injective hS (Subgroup.inclusion inf_le_left)
          (Subgroup.inclusion_injective inf_le_left) N0 hnc)
        (eq_one_of_centralizes_socle H hX3 h2 N0 hN0n hCH))
  · left
    push Not at hF
    obtain ⟨m, hmfix, hm1⟩ := hF
    have hg : (m : Perm Ω) ∈ G := (Subgroup.mem_inf.1 m.2).1
    have hgne : (m : Perm Ω) ≠ 1 := fun h => hm1 (Subtype.ext h)
    have hsupp : (m : Perm Ω).support ⊆ Finset.univ.image e := by
      intro x hx
      rw [Perm.mem_support] at hx
      by_contra hxD
      have hxD' : x ∉ D := by
        rintro ⟨i, rfl⟩
        exact hxD (Finset.mem_image_of_mem e (Finset.mem_univ i))
      exact hx (congrArg Subtype.val (hmfix ⟨x, hxD'⟩))
    have hcard : (m : Perm Ω).support.card ≤ 6 := by
      calc (m : Perm Ω).support.card ≤ (Finset.univ.image e).card := Finset.card_le_card hsupp
        _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
        _ ≤ 6 := by simp
    have h5 : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
        ∃ q : G, ∀ i, q • a i = b i := by
      intro a b ha hb
      obtain ⟨g, hg, hgi⟩ := hT (Fin 5) (by simp) a b ha hb
      exact ⟨⟨g, hg⟩, fun i => by
        simp only [Subgroup.smul_def, Perm.smul_def]; exact hgi i⟩
    exact CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix.alternatingGroup_le_of_nontrivial_support_le_six
      G h8 h5 hg hgne hcard

end Geometry2

/-! ### Wielandt's theorem -/

/-- A subgroup of `Sym(Ω)` containing `Alt(Ω)` is `Alt(Ω)` or `Sym(Ω)` (`Alt` has index 2).  So
"neither alternating nor symmetric" is the same as "does not contain `Alt(Ω)`". -/
theorem eq_alternatingGroup_or_eq_top_of_le {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (hΩ : 2 ≤ Fintype.card Ω) {G : Subgroup (Equiv.Perm Ω)} (h : alternatingGroup Ω ≤ G) :
    G = alternatingGroup Ω ∨ G = ⊤ := by
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hmul := Subgroup.relIndex_mul_index h
  rw [alternatingGroup.index_eq_two] at hmul
  rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ hmul) with h1 | h2
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · rw [h2] at hmul
    exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 (by omega)) h)

/-- **Wielandt (1960), local form.**  If the outer automorphism group of every nonabelian simple
subgroup of `G` is solvable, a permutation group `G` of degree `n ≥ 8` that is 8-transitive
contains the alternating group.  No classification hypothesis. -/
theorem alternatingGroup_le_of_outer [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω))
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    (hn : 8 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 8) :
    alternatingGroup Ω ≤ G := by
  classical
  by_cases hsmall : Fintype.card Ω ≤ 10
  · haveI := hG
    apply IsMultiplyPretransitive.alternatingGroup_le Ω G
    exact MulAction.isMultiplyPretransitive_of_le (n := 8)
      (by rw [Nat.card_eq_fintype_card]; omega) (by rw [Nat.card_eq_fintype_card]; omega)
  have hT : TransUpTo G 8 := transUpTo_of_isMultiplyPretransitive G hn hG
  have emb : ∀ k : ℕ, k ≤ Fintype.card Ω → ∃ e : Fin k → Ω, Function.Injective e :=
    fun k hk => ⟨fun i => (Fintype.equivFin Ω).symm (Fin.castLE hk i),
      (Fintype.equivFin Ω).symm.injective.comp (Fin.castLE_injective hk)⟩
  by_contra hAlt
  obtain ⟨e5, he5⟩ := emb 5 (by omega)
  obtain ⟨e6, he6⟩ := emb 6 (by omega)
  rcases local_step hOut (d := 5) le_rfl (by norm_num) e5 he5 (hT.mono (by norm_num)) (by omega)
      hn with h | ⟨p, a, hp, -, h5, h5two⟩
  · exact hAlt h
  rcases local_step hOut (d := 6) (by norm_num) le_rfl e6 he6 hT (by omega) hn with
      h | ⟨q, b, hq, hb, h6, -⟩
  · exact hAlt h
  have hp2 : p = 2 := h5two hT (by omega)
  subst hp2
  exact two_pow_ne_prime_pow_add_one hq hb (a := a) (by omega)


/-- **Wielandt (1960), Satz 1**, in the paper's form.  Let `G` be a permutation group that is
neither alternating nor symmetric, such that the outer automorphism group of every simple
subgroup of `G` is solvable.  Then `G` is at most 7-transitive: if `G` is `k`-transitive on
`k ≤ n` points, then `k ≤ 7`. -/
theorem wielandt_satz1 [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hAlt : G ≠ alternatingGroup Ω) (hSym : G ≠ ⊤)
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → Group.IsSolvable (Outer T))
    {k : ℕ} (hk : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k) :
    k ≤ 7 := by
  by_contra h7
  haveI := hG
  have h8 : MulAction.IsMultiplyPretransitive G Ω 8 :=
    MulAction.isMultiplyPretransitive_of_le (show 8 ≤ k by omega)
      (by rw [Nat.card_eq_fintype_card]; omega)
  exact (eq_alternatingGroup_or_eq_top_of_le (by omega)
    (alternatingGroup_le_of_outer G (fun T hT _ => hOut T hT) (by omega) h8)).elim hAlt hSym

/-- **Wielandt (1960), Hilfssatz (2)**, in the paper's form.  Let `G` be a 7-transitive
permutation group of degree `n` that is neither alternating nor symmetric, and (the standing
hypothesis of Satz 1, used in step (b) of the proof) such that the outer automorphism group of
every simple subgroup of `G` is solvable.  Let `𝔥` be the largest subgroup of `G` fixing each of
the points `e 0, …, e 4`.  Then `𝔥` contains a normal subgroup `𝔐` that is transitive and regular
on the remaining `n - 5` points, elementary abelian, but not cyclic. -/
theorem wielandt_hilfssatz [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hAlt : G ≠ alternatingGroup Ω) (hSym : G ≠ ⊤)
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → Group.IsSolvable (Outer T))
    (hn : 7 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 7)
    (e : Fin 5 → Ω) (he : Function.Injective e) :
    ∃ 𝔐 : Subgroup (Equiv.Perm Ω),
      -- `𝔐 ≤ 𝔥 = {g ∈ G | g (e i) = e i for all i}`
      𝔐 ≤ G ∧ (∀ a ∈ 𝔐, ∀ i, a (e i) = e i) ∧
      -- `𝔐` is normal in `𝔥`
      (∀ h ∈ G, (∀ i, h (e i) = e i) → ∀ a ∈ 𝔐, h * a * h⁻¹ ∈ 𝔐) ∧
      -- transitive and regular on the remaining `n - 5` points
      (∀ x y, x ∉ Set.range e → y ∉ Set.range e → ∃! a, a ∈ 𝔐 ∧ a x = y) ∧
      -- elementary abelian, but not cyclic
      (∀ a ∈ 𝔐, ∀ b ∈ 𝔐, a * b = b * a) ∧ (∃ p : ℕ, p.Prime ∧ ∀ a ∈ 𝔐, a ^ p = 1) ∧
      ¬ IsCyclic 𝔐 := by
  classical
  have hAG : ¬ alternatingGroup Ω ≤ G := fun h =>
    (eq_alternatingGroup_or_eq_top_of_le (by omega) h).elim hAlt hSym
  by_cases hsmall : Fintype.card Ω ≤ 9
  · exfalso
    apply hAG
    haveI := hG
    apply IsMultiplyPretransitive.alternatingGroup_le Ω G
    exact MulAction.isMultiplyPretransitive_of_le (n := 7)
      (by rw [Nat.card_eq_fintype_card]; omega) (by rw [Nat.card_eq_fintype_card]; omega)
  rcases hilfssatz (G := G) (fun T hT _ => hOut T hT) e he hG (by omega) with
      h | ⟨N, p, hp, hNG, hfix, hnorm, hcomm, hexp, htr, hcyc⟩
  · exact absurd h hAG
  refine ⟨N, hNG, hfix, fun h hh hfixh => hnorm h hh fun z => ?_, fun x y hx hy => ?_, hcomm,
    ⟨p, hp, hexp⟩, hcyc⟩
  · constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, h.injective (by rw [hfixh i, hi])⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hfixh i).symm⟩
  · obtain ⟨a, ha, hax⟩ := htr x y hx hy
    refine ⟨a, ⟨ha, hax⟩, fun b ⟨hb, hbx⟩ => ?_⟩
    ext z
    by_cases hz : z ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hz
      rw [hfix b hb i, hfix a ha i]
    · obtain ⟨c, hc, rfl⟩ := htr x z hx hz
      show (b * c) x = (a * c) x
      rw [hcomm b hb c hc, hcomm a ha c hc, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hbx, hax]

/-- **Wielandt's theorem, unconditional form** (corollary of `alternatingGroup_le_of_outer`).
Assuming the classification statement `hCFSG` (proved in the corpus as
`CFSGComparator.classification`), which gives Schreier's conjecture for every simple subgroup of
`G`, a finite 8-transitive permutation group of degree `n ≥ 8` contains the alternating group. -/
theorem wielandt_eight_transitive [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hn : 8 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 8) :
    alternatingGroup Ω ≤ G :=
  alternatingGroup_le_of_outer G (fun T hT hnc => by
    haveI := hT
    exact outer_solvable_of_classification hCFSG T hnc) hn hG

end CFSGOutside.Wielandt
