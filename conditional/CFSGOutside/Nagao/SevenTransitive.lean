
import CFSGOutside.Wielandt.EightTransitive
import CFSGOutside.Corpus.FixedDegreeCases
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-!
# Nagao: a 7-transitive permutation group contains the alternating group

**Paper.** H. Nagao, *On multiply transitive groups I*, Nagoya Math. J. **27** (1966), 15–19,
DOI 10.1017/S0027763000011818 (announced in *On a theorem of Wielandt*, Proc. Japan Acad.
**40** (1964), 793–794).

**Theorem 3** (verbatim): *Let G be a k-fold transitive group of degree n. If the outer
automorphism group of any simple subgroup of G is solvable, then k ≤ 6 unless G is S_n or A_n.*
This improves Wielandt's bound `k ≤ 7` (Math. Z. 74 (1960), Satz 1).

**Claims formalized.**
* `nagao_theorem3`: Theorem 3 in the paper's form, with the paper's local hypothesis and no
  classification hypothesis.
* `alternatingGroup_le_of_outer_seven`: the working form for `k = 7` (a 7-transitive `G` of degree
  `≥ 7` contains `Alt(Ω)`), assuming `Out(T)` solvable for the nonabelian simple subgroups `T ≤ G`.
* `nagao_seven_transitive`, `nagao_k_transitive`: the unconditional corollaries, from the
  classification statement `hCFSG : TauCeti.ClassificationStatement.{0}` (proved in the corpus as
  `CFSGComparator.classification`, not imported).

As in Nagao's proof, `Out` enters only through Wielandt's Hilfssatz (2)
(`WielandtEightTransitive.hilfssatz`), for a simple subgroup of `G`.

**CFSG / corpus components reused**, as classes in `CFSGOutside.Corpus` that the clean build proves.
* (for the corollaries only) `Schreier`, Schreier's conjecture
  (`CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`, with `hCFSG`);
* `FixedDegreeCases` (`CFSG.FiveTransitive.FullFixerSharpFive.fixed_degree_cases`: Witt's lemma +
  Jordan's theorem on sharply 5-transitive groups: the 5-point stabiliser of a 5-transitive group
  fixes 5, 6, 7 or 12 points);
* `SubgroupCardClassificationOfCardLeEighty`
  (`CFSG.FiveTransitive.subgroup_card_classification_of_card_le_eighty`, 5-transitive groups of
  degree ≤ 80), for degrees ≤ 80, with `descFactorial_dvd_card_of_isMultiplyPretransitive` proved
  here;
* `AlternatingGroupLeOfNontrivialSupportLeSix`
  (`CFSG.FiveTransitive.SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six`);
* from `CFSGOutside.Wielandt` (this campaign): Burnside's theorem on minimal
  normal subgroups of 2-transitive groups (`exists_socle`) and the stabiliser machinery
  (`setStab`, `outAction`, `restrictHom`, `exists_ker_tuple`, `restrictHom_surjective`), through
  Wielandt's Hilfssatz (2) (`hilfssatz`).

**Proof route** (Nagao §§1–3).  For `n ≤ 80` use the corpus classification.  For `n ≥ 81`:
1. *Wielandt's Hilfssatz 2* (`WielandtEightTransitive.hilfssatz`): for a 5-set `Δ`, the
   pointwise stabiliser `G_(Δ)` has a subgroup `N`, normalised by the setwise stabiliser `G_{Δ}`,
   that is abelian of prime exponent `p` and regular on `Ω ∖ Δ` (a nonabelian socle `T`, a simple
   subgroup of `G`, would make `S_5` solvable, since `Out(T)` is).
2. *`p ∈ {2,3}`* (`prime_eq_two_or_three`, Nagao's proof of Thm 2): an element `s ∈ N` with
   `s y₁ = y₂` centralises the 7-point stabiliser `V = G_(Δ ∪ {y₁,y₂})`, so `⟨s⟩` acts freely on
   the fixed points of `V` outside `Δ`; by Witt + Jordan these number `2, 3, 4` or `9`.
3. *`|N| ≤ 27`* (`card_le_twentySeven`, Nagao's Thm 1 and Proposition): conjugating `s` by a
   suitable `x ∈ G` gives `t = x s x⁻¹ ∈ G_{Δ}` of order `p` with at most `p` fixed points
   outside `Δ`; so `|C_N(t)| ≤ p`, and Nagao's lemma (`card_le_card_fix_pow`: `|N| ≤ |C_N(t)|^p`
   because `(t - 1)^p = 0` on the elementary abelian group `N`) gives `|N| ≤ p^p ≤ 27`.
4. But `|N| = n - 5 ≥ 76`.
-/

section

namespace CFSGOutside.Nagao

open Equiv CFSGOutside.Wielandt
  CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

/-! ### Nagao's lemma on nilpotent maps (group form) -/

/-- **Nagao's lemma** (Nagao 1966, §1, Lemma), for a homomorphism `ρ` of a finite group:
if `ρ^k` kills a subgroup `B`, then `|B| ≤ |ker ρ|^k`. -/
theorem card_le_card_ker_pow {A : Type} [Group A] [Finite A] (ρ : A →* A) :
    ∀ (k : ℕ) (B : Subgroup A), (∀ b ∈ B, (ρ^[k]) b = 1) →
      Nat.card B ≤ Nat.card ρ.ker ^ k := by
  intro k
  induction k with
  | zero =>
    intro B hB
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 (fun b hb => by simpa using hB b hb)
    rw [this, Subgroup.card_bot, pow_zero]
  | succ k ih =>
    intro B hB
    let f : B →* A := ρ.comp B.subtype
    have hW : ∀ w ∈ B.map ρ, (ρ^[k]) w = 1 := by
      rintro _ ⟨b, hb, rfl⟩
      rw [← Function.iterate_succ_apply]
      exact hB b hb
    have hrange : f.range = B.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Nat.card f.ker ≤ Nat.card ρ.ker := by
      apply Nat.card_le_card_of_injective (fun x : f.ker => (⟨(x : B), x.2⟩ : ρ.ker))
      intro a b h
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ρ.ker => (y : A)) h
    have hmul := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hrange] at hmul
    calc Nat.card B = Nat.card f.ker * Nat.card (B.map ρ) := hmul.symm
      _ ≤ Nat.card ρ.ker * Nat.card ρ.ker ^ k := Nat.mul_le_mul hker (ih _ hW)
      _ = Nat.card ρ.ker ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- For an abelian group of exponent `p ∈ {2, 3}` and an automorphism `c` with `c^p = 1`,
`|A| ≤ |C_A(c)|^p`. -/
theorem card_le_card_fix_pow {A : Type} [CommGroup A] [Finite A] (c : A →* A) {p : ℕ}
    (hp : p = 2 ∨ p = 3) (hc : ∀ a, (c^[p]) a = a) (hexp : ∀ a : A, a ^ p = 1) :
    Nat.card A ≤ Nat.card {a : A // c a = a} ^ p := by
  let ρ : A →* A :=
    { toFun := fun a => c a / a
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_div, ofMul_mul]
        abel }
  have hρ : ∀ a, ρ a = c a / a := fun _ => rfl
  have hkill : ∀ a ∈ (⊤ : Subgroup A), (ρ^[p]) a = 1 := by
    intro a _
    rcases hp with rfl | rfl
    · simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, hρ, map_div]
      have h2 : c (c a) = a := by simpa using hc a
      rw [h2]
      have e1 := congrArg Additive.ofMul (hexp a)
      have e2 := congrArg Additive.ofMul (hexp (c a))
      apply Additive.ofMul.injective
      simp only [ofMul_div, ofMul_pow, ofMul_one] at e1 e2 ⊢
      rw [show Additive.ofMul a - Additive.ofMul (c a) - (Additive.ofMul (c a) - Additive.ofMul a)
        = 2 • Additive.ofMul a - 2 • Additive.ofMul (c a) by abel, e1, e2, sub_zero]
    · simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, hρ, map_div]
      have h3 : c (c (c a)) = a := by simpa using hc a
      rw [h3]
      have e1 := congrArg Additive.ofMul (hexp (c a))
      have e2 := congrArg Additive.ofMul (hexp (c (c a)))
      apply Additive.ofMul.injective
      simp only [ofMul_div, ofMul_pow, ofMul_one] at e1 e2 ⊢
      rw [show Additive.ofMul a - Additive.ofMul (c (c a)) -
          (Additive.ofMul (c (c a)) - Additive.ofMul (c a)) -
          (Additive.ofMul (c (c a)) - Additive.ofMul (c a) - (Additive.ofMul (c a) -
            Additive.ofMul a)) = 3 • Additive.ofMul (c a) - 3 • Additive.ofMul (c (c a)) by abel,
        e1, e2, sub_zero]
  have hle := card_le_card_ker_pow ρ p ⊤ hkill
  rw [Subgroup.card_top] at hle
  have hmem : ∀ a, a ∈ ρ.ker ↔ c a = a := by
    intro a; rw [MonoidHom.mem_ker, hρ, div_eq_one]
  have hker : Nat.card ρ.ker = Nat.card {a : A // c a = a} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, (hmem _).1 x.2⟩
        invFun := fun x => ⟨x.1, (hmem _).2 x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rwa [hker] at hle


/-! ### Tuple helpers (Wielandt's Hilfssatz 2 itself is `WielandtEightTransitive.hilfssatz`) -/

section Hilfssatz

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `k`-transitivity for tuples indexed by any finite type of size `≤ m` (unfolded form of
`WielandtEightTransitive.TransUpTo`). -/
theorem tuple_transitive (G : Subgroup (Perm Ω)) {m : ℕ} (hm : m ≤ Fintype.card Ω)
    (hG : MulAction.IsMultiplyPretransitive G Ω m) (ι : Type) [Fintype ι]
    (hι : Fintype.card ι ≤ m) (a b : ι → Ω) (ha : Function.Injective a)
    (hb : Function.Injective b) : ∃ g ∈ G, ∀ i, g (a i) = b i := by
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

private theorem injective_two' {a b : Ω} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem injective_three' {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end Hilfssatz


/-! ### Nagao's argument -/

section Nagao

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- An element of the regular abelian group `N` fixing a point outside `Δ` is trivial. -/
theorem eq_one_of_fix_out {N : Subgroup (Perm Ω)} {e : Fin 5 → Ω}
    (hfix : ∀ a ∈ N, ∀ i, a (e i) = e i) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (htr : ∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y')
    {a : Perm Ω} (ha : a ∈ N) {z : Ω} (hz : z ∉ Set.range e) (haz : a z = z) : a = 1 := by
  ext w
  rw [Perm.one_apply]
  by_cases hw : w ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hw
    exact hfix a ha i
  · obtain ⟨b, hb, rfl⟩ := htr z w hz hw
    rw [← Perm.mul_apply, hcomm a ha b hb, Perm.mul_apply, haz]

theorem eq_of_apply_eq_out {N : Subgroup (Perm Ω)} {e : Fin 5 → Ω}
    (hfix : ∀ a ∈ N, ∀ i, a (e i) = e i) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (htr : ∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y')
    {a b : Perm Ω} (ha : a ∈ N) (hb : b ∈ N) {z : Ω} (hz : z ∉ Set.range e)
    (h : a z = b z) : a = b := by
  have := eq_one_of_fix_out hfix hcomm htr (N.mul_mem (N.inv_mem hb) ha) hz
    (by rw [Perm.mul_apply, h]; simp)
  rw [inv_mul_eq_one] at this
  exact this.symm

/-- A permutation mapping a finite set into itself permutes it. -/
theorem mem_range_iff_of_maps {e : Fin 5 → Ω} (t : Perm Ω)
    (ht : ∀ i, t (e i) ∈ Set.range e) (z : Ω) : t z ∈ Set.range e ↔ z ∈ Set.range e := by
  classical
  constructor
  · intro hz
    let D : Finset Ω := Finset.univ.image e
    have hsub : D.image t ⊆ D := by
      intro w hw
      simp only [D, Finset.mem_image, Finset.mem_univ, true_and] at hw ⊢
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hw
      exact ht i
    have heq : D.image t = D :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ t.injective])
    have : t z ∈ D.image t := by
      rw [heq]; obtain ⟨i, hi⟩ := hz
      simp only [D, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨i, hi⟩
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.1 this
    rw [t.injective hwz] at hw
    simp only [D, Finset.mem_image, Finset.mem_univ, true_and] at hw
    exact hw
  · rintro ⟨i, rfl⟩
    exact ht i

/-- **Nagao's bound** (proofs of Thm 1 and of the Proposition): if `t` normalises `N`,
`t^p = 1` (`p ∈ {2,3}` the exponent of `N`), `t` fixes a point `y₁ ∉ Δ`, and the fixed points
of `t` outside `Δ` lie in a set of size `≤ p`, then `|N| ≤ p^p`. -/
theorem card_le_of_normalizing {N : Subgroup (Perm Ω)} {e : Fin 5 → Ω} {p : ℕ}
    (hp : p = 2 ∨ p = 3)
    (hfix : ∀ a ∈ N, ∀ i, a (e i) = e i) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hexp : ∀ a ∈ N, a ^ p = 1)
    (htr : ∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y')
    (t : Perm Ω) (htN : ∀ a ∈ N, t * a * t⁻¹ ∈ N) (htp : t ^ p = 1)
    {y₁ : Ω} (hy₁ : y₁ ∉ Set.range e) (hty : t y₁ = y₁) (S : Finset Ω) (hS : S.card ≤ p)
    (hfixS : ∀ z, z ∉ Set.range e → t z = z → z ∈ S) : Nat.card N ≤ p ^ p := by
  classical
  letI : CommGroup N :=
    { (inferInstance : Group N) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let c : N →* N :=
    { toFun := fun a => ⟨t * a * t⁻¹, htN a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change t * ((a : Perm Ω) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹)
        group) }
  have hcval : ∀ a : N, ((c a : N) : Perm Ω) = t * a * t⁻¹ := fun _ => rfl
  have hiter : ∀ (k : ℕ) (a : N), (((c^[k]) a : N) : Perm Ω) = t ^ k * a * (t ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', hcval, ih, pow_succ', mul_inv_rev]
      group
  have hcp : ∀ a, (c^[p]) a = a := by
    intro a
    apply Subtype.ext
    rw [hiter, htp, one_mul, inv_one, mul_one]
  have hexpA : ∀ a : N, a ^ p = 1 := fun a => Subtype.ext (by
    have := hexp a a.2
    simpa using this)
  have h1 := card_le_card_fix_pow c hp hcp hexpA
  have h2 : Nat.card {a : N // c a = a} ≤ S.card := by
    have hmap : ∀ a : {a : N // c a = a}, (a.1 : Perm Ω) y₁ ∈ S := by
      rintro ⟨a, ha⟩
      have hta : t * a * t⁻¹ = a := congrArg Subtype.val ha
      apply hfixS
      · rintro ⟨i, hi⟩
        apply hy₁
        refine ⟨i, ?_⟩
        apply (a : Perm Ω).injective
        rw [hfix a a.2 i, hi]
      · have : t * a = a * t := by
          calc t * (a : Perm Ω) = (t * a * t⁻¹) * t := by group
            _ = a * t := by rw [hta]
        rw [← Perm.mul_apply, this, Perm.mul_apply, hty]
    have := Nat.card_le_card_of_injective (fun a : {a : N // c a = a} =>
      (⟨(a.1 : Perm Ω) y₁, hmap a⟩ : {z : Ω // z ∈ S})) (by
        intro a b hab
        apply Subtype.ext; apply Subtype.ext
        exact eq_of_apply_eq_out hfix hcomm htr a.1.2 b.1.2 hy₁ (congrArg Subtype.val hab))
    rwa [Nat.card_eq_fintype_card (α := {z : Ω // z ∈ S}), Fintype.card_coe] at this
  calc Nat.card N ≤ Nat.card {a : N // c a = a} ^ p := h1
    _ ≤ S.card ^ p := Nat.pow_le_pow_left h2 p
    _ ≤ p ^ p := Nat.pow_le_pow_left hS p

end Nagao


/-! ### Step A: the exponent of `N` is 2 or 3 (Witt + Jordan, via the corpus) -/

section ExponentBound

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

variable (G : Subgroup (Perm Ω)) (u v : Ω) in
/-- The pointwise stabiliser `G_{u,v}`. -/
def stab2 : Subgroup (Perm Ω) :=
  G ⊓ MulAction.stabilizer (Perm Ω) u ⊓ MulAction.stabilizer (Perm Ω) v

theorem mem_stab2 {G : Subgroup (Perm Ω)} {u v : Ω} {g : Perm Ω} :
    g ∈ stab2 G u v ↔ g ∈ G ∧ g u = u ∧ g v = v := by
  simp [stab2, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def, and_assoc]

variable (G : Subgroup (Perm Ω)) (u v : Ω) in
/-- The action of `G_{u,v}` on `Ω ∖ {u, v}`. -/
@[reducible] def twoAction : MulAction (stab2 G u v) {x : Ω // x ≠ u ∧ x ≠ v} where
  smul g x := ⟨(g : Perm Ω) x,
    fun h => x.2.1 ((g : Perm Ω).injective (h.trans ((mem_stab2.1 g.2).2.1).symm)),
    fun h => x.2.2 ((g : Perm Ω).injective (h.trans ((mem_stab2.1 g.2).2.2).symm))⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- **Nagao, proof of Theorem 2 (first paragraph).** If `N` is a regular abelian normal subgroup
of prime exponent `p` of the 5-point stabiliser of a 7-transitive group, then `p ∈ {2, 3}`.
The 7-point stabiliser `V` is centralised by an element `s ∈ N`; by Witt's lemma and Jordan's
theorem on sharply 5-transitive groups (corpus: `fixed_degree_cases`), `V` fixes `5, 6, 7` or
`12` points of `Ω ∖ {e₀, e₁}`, and `⟨s⟩` acts freely on those outside `Δ`. -/
theorem prime_eq_two_or_three [CFSGOutside.Corpus.FixedDegreeCases] (G : Subgroup (Perm Ω))
    (hG : MulAction.IsMultiplyPretransitive G Ω 7) (h8 : 8 ≤ Fintype.card Ω)
    {e : Fin 5 → Ω} (he : Function.Injective e) {N : Subgroup (Perm Ω)} {p : ℕ}
    (hp : p.Prime) (hfix : ∀ a ∈ N, ∀ i, a (e i) = e i)
    (hnorm : ∀ m ∈ G, (∀ z, m z ∈ Set.range e ↔ z ∈ Set.range e) → ∀ a ∈ N, m * a * m⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hexp : ∀ a ∈ N, a ^ p = 1)
    (htr : ∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y')
    {y₁ y₂ : Ω} (hy₁ : y₁ ∉ Set.range e) (hy₂ : y₂ ∉ Set.range e) (hy₁₂ : y₁ ≠ y₂)
    {s : Perm Ω} (hsN : s ∈ N) (hs : s y₁ = y₂) : p = 2 ∨ p = 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set u := e 0
  set v := e 1
  have huv : u ≠ v := fun h => absurd (he h) (by decide)
  let K := stab2 G u v
  let X2 := {x : Ω // x ≠ u ∧ x ≠ v}
  letI : MulAction K X2 := twoAction G u v
  have hne : ∀ y, y ∉ Set.range e → y ≠ u ∧ y ≠ v := fun y hy =>
    ⟨fun h => hy ⟨0, h.symm⟩, fun h => hy ⟨1, h.symm⟩⟩
  have hne' : ∀ i : Fin 3, e (Fin.natAdd 2 i) ≠ u ∧ e (Fin.natAdd 2 i) ≠ v := fun i =>
    ⟨fun h => absurd (congrArg Fin.val (he h)) (by simp),
      fun h => absurd (congrArg Fin.val (he h)) (by simp; omega)⟩
  -- `G_{u,v}` is 5-transitive on `Ω ∖ {u, v}`
  have h5 : MulAction.IsMultiplyPretransitive K X2 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    have hinj : ∀ c : Fin 5 ↪ X2,
        Function.Injective (Sum.elim ![u, v] (fun j => (c j).1)) := by
      intro c
      refine Function.Injective.sumElim ?_ (Subtype.val_injective.comp c.injective) ?_
      · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      · intro i j h; fin_cases i
        · exact (c j).2.1 h.symm
        · exact (c j).2.2 h.symm
    obtain ⟨g, hg, hgi⟩ := tuple_transitive G (by omega) hG (Fin 2 ⊕ Fin 5) (by simp)
      _ _ (hinj a) (hinj b)
    have hgK : g ∈ K := mem_stab2.2 ⟨hg, by simpa using hgi (Sum.inl 0),
      by simpa using hgi (Sum.inl 1)⟩
    refine ⟨⟨g, hgK⟩, ?_⟩
    ext j
    exact hgi (Sum.inr j)
  -- the 5-set `{e₂, e₃, e₄, y₁, y₂}` in `Ω ∖ {u, v}`
  let f : Fin 3 ⊕ Fin 2 → X2 := Sum.elim (fun i => ⟨e (Fin.natAdd 2 i), hne' i⟩)
    ![⟨y₁, hne y₁ hy₁⟩, ⟨y₂, hne y₂ hy₂⟩]
  have hf : Function.Injective f := by
    refine Function.Injective.sumElim ?_ ?_ ?_
    · intro i j hij
      have := he (congrArg Subtype.val hij)
      exact (Fin.natAdd_inj 2).1 this
    · intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd (congrArg Subtype.val hij) hy₁₂
      · exact absurd (congrArg Subtype.val hij).symm hy₁₂
      · rfl
    · intro i j h; fin_cases j
      · exact hy₁ ⟨_, (congrArg Subtype.val h)⟩
      · exact hy₂ ⟨_, (congrArg Subtype.val h)⟩
  have hs' : (Set.range f).ncard = 5 := by rw [Set.ncard_range_of_injective hf]; simp
  have hcase := CFSGOutside.Corpus.FixedDegreeCases.fixed_degree_cases h5 (Set.range f) hs'
  simp only at hcase
  -- the fixed set of the 7-point stabiliser, as a predicate on `Ω`
  let P : Ω → Prop := fun x => x ≠ u ∧ x ≠ v ∧ ∀ w ∈ G, w u = u → w v = v →
    (∀ i : Fin 3, w (e (Fin.natAdd 2 i)) = e (Fin.natAdd 2 i)) → w y₁ = y₁ → w y₂ = y₂ → w x = x
  have hfixQ : ∀ (q : fixingSubgroup K (Set.range f)), ((q : K) : Perm Ω) ∈ G ∧
      ((q : K) : Perm Ω) u = u ∧ ((q : K) : Perm Ω) v = v ∧
      (∀ i : Fin 3, ((q : K) : Perm Ω) (e (Fin.natAdd 2 i)) = e (Fin.natAdd 2 i)) ∧
      ((q : K) : Perm Ω) y₁ = y₁ ∧ ((q : K) : Perm Ω) y₂ = y₂ := by
    intro q
    obtain ⟨hG', hu', hv'⟩ := mem_stab2.1 (q : K).2
    have hq := (mem_fixingSubgroup_iff K).1 q.2
    refine ⟨hG', hu', hv', fun i => ?_, ?_, ?_⟩
    · exact congrArg Subtype.val (hq (f (Sum.inl i)) ⟨_, rfl⟩)
    · exact congrArg Subtype.val (hq (f (Sum.inr 0)) ⟨_, rfl⟩)
    · exact congrArg Subtype.val (hq (f (Sum.inr 1)) ⟨_, rfl⟩)
  have hcardP : Nat.card (CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction.Fixed (X := X2)
      (fixingSubgroup K (Set.range f))) = Nat.card {x : Ω // P x} := by
    have hmem := fun x => Set.ext_iff.1
      (CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction.fixed_eq (X := X2)
        (fixingSubgroup K (Set.range f))) x
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, fun w hw hu hv hi h1 h2 => by
          have hwK : w ∈ K := mem_stab2.2 ⟨hw, hu, hv⟩
          have hwQ : (⟨w, hwK⟩ : K) ∈ fixingSubgroup K (Set.range f) := by
            rw [mem_fixingSubgroup_iff]
            rintro _ ⟨i | i, rfl⟩
            · exact Subtype.ext (hi i)
            · fin_cases i
              · exact Subtype.ext h1
              · exact Subtype.ext h2
          have := ((hmem x.1).1 x.2) ⟨⟨w, hwK⟩, hwQ⟩
          exact congrArg Subtype.val this⟩
        invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1⟩, (hmem _).2 (by
          rintro q
          obtain ⟨hG', hu', hv', hi', h1', h2'⟩ := hfixQ q
          exact Subtype.ext (x.2.2.2 _ hG' hu' hv' hi' h1' h2'))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- `s` centralises the 7-point stabiliser
  have hwS : ∀ w ∈ G, w u = u → w v = v →
      (∀ i : Fin 3, w (e (Fin.natAdd 2 i)) = e (Fin.natAdd 2 i)) → w y₁ = y₁ → w y₂ = y₂ →
      w * s = s * w := by
    intro w hw hu hv hi h1 h2
    have hwe : ∀ i : Fin 5, w (e i) = e i := by
      intro i; fin_cases i
      exacts [hu, hv, hi 0, hi 1, hi 2]
    have hwN := hnorm w hw (mem_range_iff_of_maps w (fun i => ⟨i, (hwe i).symm⟩)) s hsN
    have : w * s * w⁻¹ = s := eq_of_apply_eq_out hfix hcomm htr hwN hsN hy₁ (by
      have : w⁻¹ y₁ = y₁ := by rw [Perm.inv_eq_iff_eq, h1]
      rw [Perm.mul_apply, Perm.mul_apply, this, hs, h2])
    calc w * s = (w * s * w⁻¹) * w := by group
      _ = s * w := by rw [this]
  have hsu : s u = u := hfix s hsN 0
  have hsv : s v = v := hfix s hsN 1
  have hsP : ∀ x, P (s x) ↔ P x := by
    intro x
    have hsu' : s x = u ↔ x = u :=
      ⟨fun h => s.injective (h.trans hsu.symm), fun h => by rw [h, hsu]⟩
    have hsv' : s x = v ↔ x = v :=
      ⟨fun h => s.injective (h.trans hsv.symm), fun h => by rw [h, hsv]⟩
    simp only [P, ne_eq, hsu', hsv']
    apply and_congr_right; intro _; apply and_congr_right; intro _
    apply forall_congr'; intro w
    apply forall_congr'; intro hw
    apply forall_congr'; intro hu
    apply forall_congr'; intro hv
    apply forall_congr'; intro hi
    apply forall_congr'; intro h1
    apply forall_congr'; intro h2
    rw [← Perm.mul_apply, hwS w hw hu hv hi h1 h2, Perm.mul_apply, s.injective.eq_iff]
  let σ : Perm {x : Ω // P x} := s.subtypePerm hsP
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one, Perm.subtypePerm_pow]
    ext x
    simp [hexp s hsN]
  have hmod := Perm.card_compl_support_modEq hσ
  -- the fixed points of `σ` are `e₂, e₃, e₄`
  have hPe : ∀ i : Fin 3, P (e (Fin.natAdd 2 i)) := fun i =>
    ⟨(hne' i).1, (hne' i).2, fun w _ _ _ hi _ _ => hi i⟩
  have hsupp : σ.supportᶜ = Finset.univ.image (fun i : Fin 3 => (⟨_, hPe i⟩ : {x // P x})) := by
    ext x
    simp only [Finset.mem_compl, Perm.mem_support, not_not, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro hx
      have hx' : s x.1 = x.1 := congrArg Subtype.val hx
      have hxD : x.1 ∈ Set.range e := by
        by_contra hxD
        have := eq_one_of_fix_out hfix hcomm htr hsN hxD hx'
        rw [this, Perm.one_apply] at hs
        exact hy₁₂ hs
      obtain ⟨j, hj⟩ := hxD
      fin_cases j
      · exact absurd hj.symm x.2.1
      · exact absurd hj.symm x.2.2.1
      · exact ⟨0, Subtype.ext hj⟩
      · exact ⟨1, Subtype.ext hj⟩
      · exact ⟨2, Subtype.ext hj⟩
    · rintro ⟨i, rfl⟩
      exact Subtype.ext (hfix s hsN _)
  have h3 : σ.supportᶜ.card = 3 := by
    rw [hsupp, Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact (Fin.natAdd_inj 2).1 (he (congrArg Subtype.val hij))
  rw [h3, ← Nat.card_eq_fintype_card, ← hcardP] at hmod
  have hp2 := hp.two_le
  have hdvd : ∀ m, 3 ≡ m [MOD p] → 3 ≤ m → p ∣ m - 3 := fun m hm h3m =>
    (Nat.modEq_iff_dvd' h3m).1 hm
  rcases hcase with h | h | h | h <;> rw [h] at hmod <;>
    have hd := hdvd _ hmod (by norm_num) <;> norm_num at hd
  · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd
  · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
  · left
    have := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hd)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  · right
    have := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using hd)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this

end ExponentBound


/-! ### Steps B and C: Nagao's Theorem 1 and Proposition, `|N| ≤ 27` -/

section SmallN

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **Nagao, Theorem 1 and the Proposition (in the setting of Theorem 3).**  With `N` as in
Wielandt's Hilfssatz and `p ∈ {2, 3}`, conjugating `s ∈ N` by a suitable `x ∈ G` gives an
element `t = x s x⁻¹` of order `p` in the setwise stabiliser of `Δ` whose fixed points outside
`Δ` are at most `p` in number; Nagao's lemma then gives `|N| ≤ p^p ≤ 27`. -/
theorem card_le_twentySeven (G : Subgroup (Perm Ω))
    (hG : MulAction.IsMultiplyPretransitive G Ω 7) (h8 : 8 ≤ Fintype.card Ω)
    {e : Fin 5 → Ω} (he : Function.Injective e) {N : Subgroup (Perm Ω)} {p : ℕ}
    (hp23 : p = 2 ∨ p = 3) (hNG : N ≤ G) (hfix : ∀ a ∈ N, ∀ i, a (e i) = e i)
    (hnorm : ∀ m ∈ G, (∀ z, m z ∈ Set.range e ↔ z ∈ Set.range e) → ∀ a ∈ N, m * a * m⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hexp : ∀ a ∈ N, a ^ p = 1)
    (htr : ∀ y y', y ∉ Set.range e → y' ∉ Set.range e → ∃ a ∈ N, a y = y')
    {y₁ y₂ : Ω} (hy₁ : y₁ ∉ Set.range e) (hy₂ : y₂ ∉ Set.range e) (hy₁₂ : y₁ ≠ y₂)
    {s : Perm Ω} (hsN : s ∈ N) (hs : s y₁ = y₂) : Nat.card N ≤ 27 := by
  classical
  have hsD : ∀ z, s z ∈ Set.range e ↔ z ∈ Set.range e :=
    mem_range_iff_of_maps s (fun i => ⟨i, (hfix s hsN i).symm⟩)
  have hs1 : s ≠ 1 := by rintro rfl; exact hy₁₂ hs
  have hy₁e : ∀ i, e i ≠ y₁ := fun i h => hy₁ ⟨i, h⟩
  have hy₂e : ∀ i, e i ≠ y₂ := fun i h => hy₂ ⟨i, h⟩
  have hy₁e' : ∀ i, y₁ ≠ e i := fun i h => hy₁e i h.symm
  have hy₂e' : ∀ i, y₂ ≠ e i := fun i h => hy₂e i h.symm
  have hinv : ∀ (x : Perm Ω) z w, x z = w → x⁻¹ w = z := fun x z w h => by rw [← h]; simp
  -- fixed points of `t = x s x⁻¹` are images under `x` of points of `Δ`
  have key : ∀ (x : Perm Ω) (z : Ω), (x * s * x⁻¹) z = z → ∃ i, z = x (e i) := by
    intro x z hz
    have h1 : s (x⁻¹ z) = x⁻¹ z := by
      apply x.injective
      rw [Perm.mul_apply, Perm.mul_apply] at hz
      rw [hz]; simp
    by_cases hxz : x⁻¹ z ∈ Set.range e
    · obtain ⟨i, hi⟩ := hxz
      exact ⟨i, by rw [hi]; simp⟩
    · exact absurd (eq_one_of_fix_out hfix hcomm htr hsN hxz h1) hs1
  have htN : ∀ x ∈ G, (∀ i, (x * s * x⁻¹) (e i) ∈ Set.range e) →
      ∀ a ∈ N, (x * s * x⁻¹) * a * (x * s * x⁻¹)⁻¹ ∈ N := fun x hx hm =>
    hnorm _ (G.mul_mem (G.mul_mem hx (hNG hsN)) (G.inv_mem hx)) (mem_range_iff_of_maps _ hm)
  have htp : ∀ (x : Perm Ω) (n : ℕ), s ^ n = 1 → (x * s * x⁻¹) ^ n = 1 := by
    intro x n h
    rw [conj_pow, h, mul_one, mul_inv_cancel]
  have hne : ∀ i j : Fin 5, i ≠ j → e i ≠ e j := fun i j h => he.ne h
  rcases hp23 with rfl | rfl
  · -- `p = 2`: Nagao's Theorem 1
    have hs2 : s y₂ = y₁ := by
      rw [← hs, ← Perm.mul_apply, ← pow_two, hexp s hsN, Perm.one_apply]
    let a : Fin 5 ⊕ Fin 2 → Ω := Sum.elim e ![y₁, y₂]
    have ha : Function.Injective a := by
      refine Function.Injective.sumElim he (injective_two' hy₁₂) ?_
      · intro i j; fin_cases j
        · exact hy₁e i
        · exact hy₂e i
    let τ0 : Perm Ω := swap (e 3) y₁ * swap (e 4) y₂
    obtain ⟨x, hxG, hx⟩ := tuple_transitive G (by omega) hG (Fin 5 ⊕ Fin 2) (by simp) a
      (τ0 ∘ a) ha (τ0.injective.comp ha)
    have hxe : ∀ i : Fin 5, i ≠ 3 → i ≠ 4 → x (e i) = e i := by
      intro i h3 h4
      have := hx (Sum.inl i)
      change x (e i) = swap (e 3) y₁ (swap (e 4) y₂ (e i)) at this
      rw [this, swap_apply_of_ne_of_ne (hne _ _ h4) (hy₂e i),
        swap_apply_of_ne_of_ne (hne _ _ h3) (hy₁e i)]
    have hx3 : x (e 3) = y₁ := by
      have := hx (Sum.inl 3)
      change x (e 3) = swap (e 3) y₁ (swap (e 4) y₂ (e 3)) at this
      rw [this, swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₂e 3), swap_apply_left]
    have hy1 : x y₁ = e 3 := by
      have := hx (Sum.inr 0)
      change x y₁ = swap (e 3) y₁ (swap (e 4) y₂ y₁) at this
      rw [this, swap_apply_of_ne_of_ne (hy₁e' 4) hy₁₂, swap_apply_right]
    have hy2 : x y₂ = e 4 := by
      have := hx (Sum.inr 1)
      change x y₂ = swap (e 3) y₁ (swap (e 4) y₂ y₂) at this
      rw [this, swap_apply_right, swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₁e 4)]
    have ht : ∀ z, (x * s * x⁻¹) z = x (s (x⁻¹ z)) := fun z => rfl
    have hfe : ∀ i : Fin 5, i ≠ 3 → i ≠ 4 → (x * s * x⁻¹) (e i) = e i := fun i h3 h4 => by
      rw [ht, hinv x _ _ (hxe i h3 h4), hfix s hsN, hxe i h3 h4]
    have ht3 : (x * s * x⁻¹) (e 3) = e 4 := by rw [ht, hinv x _ _ hy1, hs, hy2]
    have ht4 : (x * s * x⁻¹) (e 4) = e 3 := by rw [ht, hinv x _ _ hy2, hs2, hy1]
    have hte : ∀ i, (x * s * x⁻¹) (e i) ∈ Set.range e := by
      intro i
      fin_cases i
      exacts [⟨0, (hfe 0 (by decide) (by decide)).symm⟩, ⟨1, (hfe 1 (by decide) (by decide)).symm⟩,
        ⟨2, (hfe 2 (by decide) (by decide)).symm⟩, ⟨4, ht3.symm⟩, ⟨3, ht4.symm⟩]
    have hty : (x * s * x⁻¹) y₁ = y₁ := by
      rw [ht, hinv x _ _ hx3, hfix s hsN, hx3]
    have hfixS : ∀ z, z ∉ Set.range e → (x * s * x⁻¹) z = z → z ∈ ({y₁, y₂} : Finset Ω) := by
      intro z hz htz
      obtain ⟨i, rfl⟩ := key x z htz
      fin_cases i
      · exact absurd ⟨0, (hxe 0 (by decide) (by decide)).symm⟩ hz
      · exact absurd ⟨1, (hxe 1 (by decide) (by decide)).symm⟩ hz
      · exact absurd ⟨2, (hxe 2 (by decide) (by decide)).symm⟩ hz
      · show x (e 3) ∈ _
        rw [hx3]; simp
      · show x (e 4) ∈ _
        have := hx (Sum.inl 4)
        change x (e 4) = swap (e 3) y₁ (swap (e 4) y₂ (e 4)) at this
        rw [this, swap_apply_left, swap_apply_of_ne_of_ne (hy₂e' 3) (Ne.symm hy₁₂)]; simp
    have := card_le_of_normalizing (Or.inl rfl) hfix hcomm hexp htr (x * s * x⁻¹)
      (htN x hxG hte) (htp x 2 (hexp s hsN)) hy₁ hty _ Finset.card_le_two hfixS
    omega
  · -- `p = 3`: Nagao's Proposition
    set y₃ := s y₂ with hy₃def
    have hy₃ : y₃ ∉ Set.range e := fun h => hy₂ ((hsD y₂).1 h)
    have hs3 : s y₃ = y₁ := by
      rw [hy₃def, ← hs, ← Perm.mul_apply, ← Perm.mul_apply, ← pow_three', hexp s hsN,
        Perm.one_apply]
    have hy₂₃ : y₂ ≠ y₃ := by
      intro h
      exact hs1 (eq_one_of_fix_out hfix hcomm htr hsN hy₂ h.symm)
    have hy₁₃ : y₁ ≠ y₃ := by
      intro h
      have h2 : s ^ 2 = 1 := eq_one_of_fix_out hfix hcomm htr (N.pow_mem hsN 2) hy₁ (by
        rw [pow_two, Perm.mul_apply, hs, ← hy₃def, ← h])
      apply hs1
      have := hexp s hsN
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] at this
      exact this
    have hy₃e : ∀ i, e i ≠ y₃ := fun i h => hy₃ ⟨i, h⟩
    have hy₃e' : ∀ i, y₃ ≠ e i := fun i h => hy₃e i h.symm
    let a : Fin 4 ⊕ Fin 3 → Ω := Sum.elim (fun i => e (Fin.castSucc i)) ![y₁, y₂, y₃]
    have ha : Function.Injective a := by
      refine Function.Injective.sumElim (he.comp (Fin.castSucc_injective 4))
        (injective_three' hy₁₂ hy₁₃ hy₂₃) ?_
      · intro i j; fin_cases j
        · exact hy₁e _
        · exact hy₂e _
        · exact hy₃e _
    let τ0 : Perm Ω := swap (e 2) y₁ * swap (e 3) y₂ * swap (e 4) y₃
    obtain ⟨x, hxG, hx⟩ := tuple_transitive G (by omega) hG (Fin 4 ⊕ Fin 3) (by simp) a
      (τ0 ∘ a) ha (τ0.injective.comp ha)
    have hxe : ∀ i : Fin 4, i.val < 2 → x (e (Fin.castSucc i)) = e (Fin.castSucc i) := by
      intro i hi
      have := hx (Sum.inl i)
      change x (e (Fin.castSucc i)) = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃
        (e (Fin.castSucc i)))) at this
      rw [this, swap_apply_of_ne_of_ne (hne _ _ (by rw [Fin.ne_iff_vne]; simp; omega)) (hy₃e _),
        swap_apply_of_ne_of_ne (hne _ _ (by rw [Fin.ne_iff_vne]; simp; omega)) (hy₂e _),
        swap_apply_of_ne_of_ne (hne _ _ (by rw [Fin.ne_iff_vne]; simp; omega)) (hy₁e _)]
    have hx0 : x (e 0) = e 0 := hxe 0 (by decide)
    have hx1 : x (e 1) = e 1 := hxe 1 (by decide)
    have hx2 : x (e 2) = y₁ := by
      have := hx (Sum.inl 2)
      change x (e 2) = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃ (e 2))) at this
      rw [this, swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₃e 2),
        swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₂e 2), swap_apply_left]
    have hy1 : x y₁ = e 2 := by
      have := hx (Sum.inr 0)
      change x y₁ = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃ y₁)) at this
      rw [this, swap_apply_of_ne_of_ne (hy₁e' 4) hy₁₃,
        swap_apply_of_ne_of_ne (hy₁e' 3) hy₁₂, swap_apply_right]
    have hy2 : x y₂ = e 3 := by
      have := hx (Sum.inr 1)
      change x y₂ = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃ y₂)) at this
      rw [this, swap_apply_of_ne_of_ne (hy₂e' 4) hy₂₃, swap_apply_right,
        swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₁e 3)]
    have hy3 : x y₃ = e 4 := by
      have := hx (Sum.inr 2)
      change x y₃ = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃ y₃)) at this
      rw [this, swap_apply_right, swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₂e 4),
        swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₁e 4)]
    have ht : ∀ z, (x * s * x⁻¹) z = x (s (x⁻¹ z)) := fun z => rfl
    have ht0 : (x * s * x⁻¹) (e 0) = e 0 := by rw [ht, hinv x _ _ hx0, hfix s hsN, hx0]
    have ht1 : (x * s * x⁻¹) (e 1) = e 1 := by rw [ht, hinv x _ _ hx1, hfix s hsN, hx1]
    have ht2 : (x * s * x⁻¹) (e 2) = e 3 := by rw [ht, hinv x _ _ hy1, hs, hy2]
    have ht3 : (x * s * x⁻¹) (e 3) = e 4 := by rw [ht, hinv x _ _ hy2, ← hy₃def, hy3]
    have ht4 : (x * s * x⁻¹) (e 4) = e 2 := by rw [ht, hinv x _ _ hy3, hs3, hy1]
    have hte : ∀ i, (x * s * x⁻¹) (e i) ∈ Set.range e := by
      intro i
      fin_cases i
      exacts [⟨0, ht0.symm⟩, ⟨1, ht1.symm⟩, ⟨3, ht2.symm⟩, ⟨4, ht3.symm⟩, ⟨2, ht4.symm⟩]
    have hty : (x * s * x⁻¹) y₁ = y₁ := by
      rw [ht, hinv x _ _ hx2, hfix s hsN, hx2]
    have hfixS : ∀ z, z ∉ Set.range e → (x * s * x⁻¹) z = z →
        z ∈ ({y₁, y₂, x (e 4)} : Finset Ω) := by
      intro z hz htz
      obtain ⟨i, rfl⟩ := key x z htz
      fin_cases i
      · exact absurd ⟨0, hx0.symm⟩ hz
      · exact absurd ⟨1, hx1.symm⟩ hz
      · show x (e 2) ∈ _
        rw [hx2]; simp
      · show x (e 3) ∈ _
        have := hx (Sum.inl 3)
        change x (e 3) = swap (e 2) y₁ (swap (e 3) y₂ (swap (e 4) y₃ (e 3))) at this
        rw [this, swap_apply_of_ne_of_ne (hne _ _ (by decide)) (hy₃e 3), swap_apply_left,
          swap_apply_of_ne_of_ne (hy₂e' 2) (Ne.symm hy₁₂)]
        simp
      · show x (e 4) ∈ _
        simp
    have := card_le_of_normalizing (Or.inr rfl) hfix hcomm hexp htr (x * s * x⁻¹)
      (htN x hxG hte) (htp x 3 (hexp s hsN)) hy₁ hty _ Finset.card_le_three hfixS
    omega

end SmallN


/-! ### Nagao's Theorem 3 -/

/-- A `k`-transitive group on `X` has order divisible by `|X| (|X| - 1) ⋯ (|X| - k + 1)`, as
`CFSG.FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive` states it. -/
theorem descFactorial_dvd_card_of_isMultiplyPretransitive
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] (k : ℕ)
    (hk : k ≤ Fintype.card X)
    (h : MulAction.IsMultiplyPretransitive G X k) :
    (Fintype.card X).descFactorial k ∣ Nat.card G := by
  classical
  let _ : MulAction.IsMultiplyPretransitive G X k := h
  have hecard : 0 < Fintype.card (Fin k ↪ X) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_pos.mpr hk
  let e : Fin k ↪ X := Classical.choice (Fintype.card_pos_iff.mp hecard)
  have hindex := MulAction.index_stabilizer_of_transitive G e
  have hemb : Nat.card (Fin k ↪ X) = (Fintype.card X).descFactorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
  have hcard := (MulAction.stabilizer G e).card_mul_index
  rw [hindex, hemb] at hcard
  refine ⟨Nat.card (MulAction.stabilizer G e), ?_⟩
  simpa [Nat.mul_comm] using hcard.symm

/-- **Nagao (1966), Theorem 3, local form, for `k = 7`.**  If the outer automorphism group of
every nonabelian simple subgroup of `G` is solvable, a 7-transitive permutation group of degree
`n ≥ 7` contains the alternating group.  No classification hypothesis. -/
theorem alternatingGroup_le_of_outer_seven
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω))
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      Group.IsSolvable (Outer T))
    (hn : 7 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 7) :
    alternatingGroup Ω ≤ G := by
  classical
  -- degrees `≤ 9`: `G` is `(n-2)`-transitive
  by_cases hsmall : Fintype.card Ω ≤ 9
  · haveI := hG
    apply IsMultiplyPretransitive.alternatingGroup_le Ω G
    exact MulAction.isMultiplyPretransitive_of_le (n := 7)
      (by rw [Nat.card_eq_fintype_card]; omega) (by rw [Nat.card_eq_fintype_card]; omega)
  -- degrees `≤ 80`: the corpus classification of 5-transitive groups
  by_cases hmid : Fintype.card Ω ≤ 80
  · have h5 : MulAction.IsMultiplyPretransitive G Ω 5 := by
      haveI := hG
      exact MulAction.isMultiplyPretransitive_of_le (n := 7) (by norm_num)
        (by rw [Nat.card_eq_fintype_card]; omega)
    have hd := descFactorial_dvd_card_of_isMultiplyPretransitive
      G Ω 7 (by omega) hG
    have hperm : Nat.card (Perm Ω) = (Fintype.card Ω).factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rcases CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty.subgroup_card_classification_of_card_le_eighty
        _ Ω G rfl
        (by omega) hmid h5 with h | ⟨-, h⟩ | ⟨h12, h⟩ | ⟨h24, h⟩
    · have : G = ⊤ := Subgroup.eq_top_of_card_eq G (by rw [h, hperm])
      rw [this]; exact le_top
    · apply Equiv.Perm.alternatingGroup_le_of_index_le_two
      have hmul := G.index_mul_card
      rw [h, hperm] at hmul
      have h2 : 2 ∣ (Fintype.card Ω).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have hpos : 0 < (Fintype.card Ω).factorial / 2 :=
        Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) h2) (by norm_num)
      have : G.index * ((Fintype.card Ω).factorial / 2) = 2 * ((Fintype.card Ω).factorial / 2) := by
        rw [hmul, Nat.mul_div_cancel' h2]
      have := Nat.eq_of_mul_eq_mul_right hpos this
      omega
    · exfalso
      rw [h, h12] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      norm_num [Nat.descFactorial] at this
    · exfalso
      rw [h, h24] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      norm_num [Nat.descFactorial] at this
  -- degrees `≥ 81`: Wielandt's Hilfssatz and Nagao's Theorem 2
  push Not at hsmall hmid
  let e : Fin 5 → Ω := fun i => (Fintype.equivFin Ω).symm (Fin.castLE (by omega) i)
  have he : Function.Injective e :=
    (Fintype.equivFin Ω).symm.injective.comp (Fin.castLE_injective _)
  rcases hilfssatz (G := G) hOut e he hG (by omega) with
      h | ⟨N, p, hp, hNG, hfix, hnorm, hcomm, hexp, htr, -⟩
  · exact h
  exfalso
  -- two points outside `Δ` and `s ∈ N` with `s y₁ = y₂`
  obtain ⟨y₁, hy₁⟩ : ∃ y, y ∉ Finset.univ.image e := by
    by_contra hall
    push Not at hall
    have := Finset.card_le_card (fun y _ => hall y : (Finset.univ : Finset Ω) ⊆ _)
    rw [Finset.card_univ] at this
    have := this.trans Finset.card_image_le
    simp at this; omega
  obtain ⟨y₂, hy₂⟩ : ∃ y, y ∉ insert y₁ (Finset.univ.image e) := by
    by_contra hall
    push Not at hall
    have := Finset.card_le_card (fun y _ => hall y : (Finset.univ : Finset Ω) ⊆ _)
    rw [Finset.card_univ] at this
    have := this.trans ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_image_le))
    simp at this; omega
  have hy₁' : y₁ ∉ Set.range e := fun ⟨i, hi⟩ => hy₁ (by rw [← hi]; simp)
  have hy₂' : y₂ ∉ Set.range e := fun ⟨i, hi⟩ => hy₂ (by rw [← hi]; simp)
  have hy₁₂ : y₁ ≠ y₂ := fun h => hy₂ (by rw [← h]; simp)
  obtain ⟨s, hsN, hs⟩ := htr y₁ y₂ hy₁' hy₂'
  have hp23 := prime_eq_two_or_three G hG (by omega) he hp hfix hnorm hcomm hexp htr hy₁' hy₂'
    hy₁₂ hsN hs
  have hN27 := card_le_twentySeven G hG (by omega) he hp23 hNG hfix hnorm hcomm hexp htr hy₁'
    hy₂' hy₁₂ hsN hs
  -- but `N` is transitive on the `n - 5 ≥ 76` points outside `Δ`
  have hY : Fintype.card {x : Ω // x ∉ Set.range e} ≤ Nat.card N := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_le_card_of_surjective (fun a : N => (⟨(a : Perm Ω) y₁, fun ⟨i, hi⟩ => hy₁' ⟨i,
      by apply (a : Perm Ω).injective; rw [hfix a a.2 i, hi]⟩⟩ : {x : Ω // x ∉ Set.range e}))
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, hay⟩ := htr y₁ y hy₁' hy
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  have hcardD : Fintype.card {x : Ω // x ∈ Set.range e} = 5 := by
    calc Fintype.card {x : Ω // x ∈ Set.range e} = Fintype.card (Fin 5) :=
          Fintype.card_congr (Equiv.ofInjective e he).symm
      _ = 5 := Fintype.card_fin 5
  rw [Fintype.card_subtype_compl, hcardD] at hY
  omega

/-- **7-transitive permutation groups.** Let G be a k-transitive permutation group on a finite set Ω with k ≤ |Ω|, such
that every simple subgroup of G has soluble outer automorphism group. If G is neither the symmetric nor the
alternating group on Ω, then k ≤ 6. Consequently every k-transitive group of degree n with 7 ≤ k ≤ n contains the
alternating group.

Source: H. Nagao, On multiply transitive groups I, Nagoya Math. J. 27 (1966), 15–19, Theorem 3.
https://doi.org/10.1017/S0027763000011818

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem nagao_theorem3
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    {k : ℕ} (hk : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k)
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → Group.IsSolvable (Outer T))
    (hSym : G ≠ ⊤) (hAlt : G ≠ alternatingGroup Ω) : k ≤ 6 := by
  by_contra h6
  haveI := hG
  have h7 : MulAction.IsMultiplyPretransitive G Ω 7 :=
    MulAction.isMultiplyPretransitive_of_le (show 7 ≤ k by omega)
      (by rw [Nat.card_eq_fintype_card]; omega)
  exact (eq_alternatingGroup_or_eq_top_of_le (by omega)
    (alternatingGroup_le_of_outer_seven G (fun T hT _ => hOut T hT) (by omega) h7)).elim hAlt hSym

/-- **Nagao, Theorem 3 for `k = 7`, unconditional form** (corollary of
`alternatingGroup_le_of_outer_seven`).  Assuming the classification statement `hCFSG` (which
gives Schreier's conjecture for every simple subgroup of `G`), a 7-transitive permutation group
of degree `n ≥ 7` contains the alternating group. -/
theorem nagao_seven_transitive
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hn : 7 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 7) :
    alternatingGroup Ω ≤ G :=
  alternatingGroup_le_of_outer_seven G (fun T hT hnc => by
    haveI := hT
    exact outer_solvable_of_classification hCFSG T hnc) hn hG

/-- Nagao's Theorem 3 in the form `k ≤ 6`: for every `k ≥ 7`, a `k`-transitive permutation group
of degree `n ≥ k` contains the alternating group (assuming `hCFSG`). -/
theorem nagao_k_transitive
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) {k : ℕ} (hk : 7 ≤ k)
    (hn : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k) :
    alternatingGroup Ω ≤ G := by
  haveI := hG
  exact nagao_seven_transitive hCFSG G (by omega)
    (MulAction.isMultiplyPretransitive_of_le hk (by rw [Nat.card_eq_fintype_card]; exact hn))

end CFSGOutside.Nagao
