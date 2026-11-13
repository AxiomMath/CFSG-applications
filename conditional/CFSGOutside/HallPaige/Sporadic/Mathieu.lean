import CFSGOutside.HallPaige.Statements
import CFSGOutside.Corpus.HallPaige.Mathieu

/-!
# The Mathieu groups satisfy the permutation-labelling criterion

For each Mathieu group `M` we use its natural 2-transitive action (degrees 11, 12, 22, 23, 24).
The point stabilizer `H` has exactly two orbits, `{x₀}` and the rest, so we label points by
`x₀ ↦ 0`, others `↦ 1`, take `σ = 1`, and need one element `g` with `g • x₀ ≠ x₀` and
`g² • x₀ ≠ x₀`. Goodness of `H` comes from two distinct commuting involutions fixing `x₀`.

All data (Schreier transversals, words for 2-transitivity, `g`, the involutions) are words in the
two corpus generators, checked by kernel evaluation on points only.
-/

namespace CFSGOutside.HallPaige

universe u

open Equiv

section General

/-- A finite group containing two distinct commuting involutions is good. -/
theorem isGood_of_commute_involutions {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) : IsGood G := by
  classical
  set C := Subgroup.closure ({a, b} : Set G)
  have hmem : ∀ x, x = a ∨ x = b → x ∈ C := fun x hx =>
    Subgroup.subset_closure (by rcases hx with rfl | rfl <;> simp)
  have h1 : ∀ x ∈ C, Commute x a ∧ Commute x b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨Commute.refl _, hab⟩
      · exact ⟨hab.symm, Commute.refl _⟩
    | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
    | mul x y _ _ hx hy => exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
    | inv x _ hx => exact ⟨hx.1.inv_left, hx.2.inv_left⟩
  have h2 : ∀ x ∈ C, ∀ y ∈ C, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact (h1 x hx).1
      · exact (h1 x hx).2
    | one => exact Commute.one_right _
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  have h3 : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact mul_one 1
    | mul x y hxm hym hx hy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [(h2 y hym x hxm).eq]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx, hy, mul_one]
    | inv x _ hx => rw [← mul_inv_rev, hx, inv_one]
  have hp : IsPGroup 2 C := fun g =>
    ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (h3 g g.2)⟩
  obtain ⟨P₀, hP₀⟩ := hp.exists_le_sylow
  intro P
  right
  intro hcyc
  haveI : IsCyclic P₀ := isCyclic_of_surjective (Sylow.equiv P P₀).toMonoidHom
    (Sylow.equiv P P₀).surjective
  haveI : Fintype P₀ := Fintype.ofFinite _
  let a' : P₀ := ⟨a, hP₀ (hmem a (Or.inl rfl))⟩
  let b' : P₀ := ⟨b, hP₀ (hmem b (Or.inr rfl))⟩
  have hsub : ({1, a', b'} : Finset P₀) ⊆ Finset.univ.filter (fun x : P₀ => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
    rcases hx with rfl | rfl | rfl
    · exact mul_one 1
    · exact Subtype.ext ha
    · exact Subtype.ext hb
  have h1a : (1 : P₀) ≠ a' := fun h => ha1 (congrArg Subtype.val h).symm
  have h1b : (1 : P₀) ≠ b' := fun h => hb1 (congrArg Subtype.val h).symm
  have hab' : a' ≠ b' := fun h => hne (congrArg Subtype.val h)
  have hcard : ({1, a', b'} : Finset P₀).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1b]), Finset.card_pair hab']
  have := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (α := P₀) two_pos)
  omega

/-- The point stabilizer of an action is good as soon as it contains two distinct commuting
involutions. -/
theorem isGood_comap_stabilizer {G : Type*} [Group G] [Finite G] {n : ℕ}
    (ρ : G →* Perm (Fin n)) (x₀ : Fin n) {a b : G} (hax : ρ a x₀ = x₀) (hbx : ρ b x₀ = x₀)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) : IsGood ((MulAction.stabilizer (Perm (Fin n)) x₀).comap ρ) := by
  have hmem : ∀ c : G, ρ c x₀ = x₀ →
      c ∈ (MulAction.stabilizer (Perm (Fin n)) x₀).comap ρ := fun c hc => by
    simpa [MulAction.mem_stabilizer_iff, Perm.smul_def] using hc
  exact isGood_of_commute_involutions (a := ⟨a, hmem a hax⟩) (b := ⟨b, hmem b hbx⟩)
    (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hab)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hne (congrArg Subtype.val h))

/-- **The 2-transitive form of the permutation-labelling criterion.** A transitive action whose
point stabilizer is transitive on the remaining points, with an element `g` such that neither
`g • x₀` nor `g² • x₀` is `x₀`, and with two distinct commuting involutions fixing `x₀`. -/
theorem permLabelling_of_twoTransitive {G : Type u} [Group G] [Finite G] {n : ℕ}
    (ρ : G →* Perm (Fin n)) (x₀ : Fin n)
    (htrans : ∀ y, ∃ g, ρ g x₀ = y)
    (hstab : ∀ y y', y ≠ x₀ → y' ≠ x₀ → ∃ h, ρ h x₀ = x₀ ∧ ρ h y = y')
    (g : G) (hg1 : ρ g x₀ ≠ x₀) (hg2 : ρ (g * g) x₀ ≠ x₀)
    (a b : G) (hax : ρ a x₀ = x₀) (hbx : ρ b x₀ = x₀) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : PermLabelling G := by
  classical
  let lab : Fin n → Fin 2 := fun y => if y = x₀ then 0 else 1
  refine ⟨n, ρ, x₀, 2, lab, Equiv.refl _, htrans, ?_, fun _ => rfl, ?_, ?_, ⟨_, hg1⟩⟩
  · intro y y'
    by_cases hy : y = x₀ <;> by_cases hy' : y' = x₀
    · subst hy hy'
      exact ⟨fun _ => ⟨1, by simp⟩, fun _ => rfl⟩
    · subst hy
      simp only [lab, if_pos rfl, if_neg hy']
      refine ⟨fun h => absurd h (by decide), ?_⟩
      rintro ⟨h, h1, h2⟩
      exact absurd (h2.symm.trans h1) hy'
    · subst hy'
      simp only [lab, if_pos rfl, if_neg hy]
      refine ⟨fun h => absurd h (by decide), ?_⟩
      rintro ⟨h, h1, h2⟩
      exact absurd ((ρ h).injective (h2.trans h1.symm)) hy
    · simp only [lab, if_neg hy, if_neg hy', true_iff]
      exact hstab y y' hy hy'
  · intro k
    fin_cases k
    · exact ⟨1, 1, by simp [lab]⟩
    · have hg2' : ρ g (ρ g x₀) ≠ x₀ := by simpa [Perm.mul_apply] using hg2
      refine ⟨g, g, ?_, ?_, ?_⟩ <;> simp [lab, hg1, hg2']
  · exact isGood_comap_stabilizer ρ x₀ hax hbx ha hb hab ha1 hb1 hne

/-- Product of a word in two generators (`false`, `true`). -/
def wordProd {α : Type*} [Monoid α] (s : Bool → α) : List Bool → α
  | [] => 1
  | c :: w => s c * wordProd s w

theorem wordProd_mem {α : Type*} [Group α] (N : Subgroup α) (s : Bool → α)
    (hs : ∀ c, s c ∈ N) : ∀ w, wordProd s w ∈ N
  | [] => N.one_mem
  | c :: w => N.mul_mem (hs c) (wordProd_mem N s hs w)

theorem wordProd_append {α : Type*} [Monoid α] (s : Bool → α) (v w : List Bool) :
    wordProd s (v ++ w) = wordProd s v * wordProd s w := by
  induction v with
  | nil => simp [wordProd]
  | cons c v ih => simp [wordProd, ih, mul_assoc]

/-- The 2-transitive criterion for a permutation model `N ≤ Perm (Fin n)` generated by two
permutations, with all data given as words and checked by Boolean evaluation on points. -/
theorem permLabelling_of_words {G : Type u} [Group G] {n : ℕ} (N : Subgroup (Perm (Fin n)))
    (e : N ≃* G) (s : Bool → Perm (Fin n)) (hs : ∀ c, s c ∈ N) (x₀ y₁ : Fin n)
    (tr st : List (List Bool)) (wg wa wb : List Bool)
    (htr : (List.finRange n).all (fun y => wordProd s (tr.getD y.val []) x₀ == y) = true)
    (hst : (List.finRange n).all (fun y => y == x₀ ||
      (wordProd s (st.getD y.val []) x₀ == x₀ && wordProd s (st.getD y.val []) y₁ == y)) = true)
    (hy₁ : y₁ ≠ x₀)
    (hg : (wordProd s wg x₀ != x₀ && wordProd s wg (wordProd s wg x₀) != x₀) = true)
    (hinv : ((List.finRange n).all (fun x => wordProd s wa (wordProd s wa x) == x &&
      wordProd s wb (wordProd s wb x) == x &&
      wordProd s wa (wordProd s wb x) == wordProd s wb (wordProd s wa x)) &&
      wordProd s wa x₀ == x₀ && wordProd s wb x₀ == x₀ &&
      (List.finRange n).any (fun x => wordProd s wa x != x) &&
      (List.finRange n).any (fun x => wordProd s wb x != x) &&
      (List.finRange n).any (fun x => wordProd s wa x != wordProd s wb x)) = true) :
    PermLabelling G := by
  haveI : Finite G := Finite.of_equiv _ e.toEquiv
  let ρ : G →* Perm (Fin n) := N.subtype.comp e.symm.toMonoidHom
  let el : List Bool → G := fun w => e ⟨wordProd s w, wordProd_mem N s hs w⟩
  have hρ : ∀ w, ρ (el w) = wordProd s w := fun w => by simp [ρ, el]
  have hel : ∀ v w, el v * el w = el (v ++ w) := fun v w => by
    simp only [el, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [wordProd_append])
  have hel_inj : ∀ v w, el v = el w ↔ wordProd s v = wordProd s w := fun v w => by
    simp only [el, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
  have hone : el [] = 1 := by
    simp only [el, wordProd]
    exact (map_eq_one_iff e e.injective).mpr rfl
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, Bool.or_eq_true,
    Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at htr hst hg hinv
  obtain ⟨⟨⟨⟨⟨hinv, hax⟩, hbx⟩, ⟨xa, -, hxa⟩⟩, ⟨xb, -, hxb⟩⟩, ⟨xab, -, hxab⟩⟩ := hinv
  have hstab : ∀ y, y ≠ x₀ → ∃ p : G, ρ p x₀ = x₀ ∧ ρ p y₁ = y := fun y hy => by
    rcases hst y with h | h
    · exact absurd h hy
    · exact ⟨el _, by rw [hρ]; exact h.1, by rw [hρ]; exact h.2⟩
  have hperm : ∀ w w' : List Bool, (∀ x, wordProd s w x = wordProd s w' x) → el w = el w' :=
    fun w w' h => (hel_inj w w').mpr (Equiv.ext h)
  refine permLabelling_of_twoTransitive ρ x₀ (fun y => ⟨el _, by rw [hρ]; exact htr y⟩) ?_
    (el wg) (by rw [hρ]; exact hg.1) (by rw [hel, hρ, wordProd_append]; exact hg.2)
    (el wa) (el wb) (by rw [hρ]; exact hax) (by rw [hρ]; exact hbx) ?_ ?_ ?_ ?_ ?_ ?_
  · intro y y' hy hy'
    obtain ⟨p, hp0, hp1⟩ := hstab y hy
    obtain ⟨q, hq0, hq1⟩ := hstab y' hy'
    refine ⟨q * p⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq.mpr hp0.symm, hq0]
    rw [map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq.mpr hp1.symm, hq1]
  · rw [hel, ← hone]; exact hperm _ _ fun x => by
      rw [wordProd_append, Perm.mul_apply]; exact (hinv x).1.1
  · rw [hel, ← hone]; exact hperm _ _ fun x => by
      rw [wordProd_append, Perm.mul_apply]; exact (hinv x).1.2
  · rw [hel, hel]; exact hperm _ _ fun x => by
      rw [wordProd_append, wordProd_append, Perm.mul_apply, Perm.mul_apply]; exact (hinv x).2
  · intro h; rw [← hone, hel_inj] at h; exact hxa (by rw [h]; rfl)
  · intro h; rw [← hone, hel_inj] at h; exact hxb (by rw [h]; rfl)
  · intro h; rw [hel_inj] at h; exact hxab (by rw [h])

end General

section M11

/-- The two corpus generators of `M₁₁` (`false`, `true`). -/
def m11Gen (c : Bool) : Perm (Fin 11) :=
  if c then List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]
  else List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

theorem m11Gen_mem (c : Bool) : m11Gen c ∈ Corpus.Mathieu.M11 := by
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Words mapping `0` to each point. -/
def m11Tr : List (List Bool) :=
  [[],
    [true, false, true, true, true],
    [true, true],
    [true],
    [true, true, false, true, true, true],
    [true, true, true, false, true, true, true],
    [false, true, true, false, true, true, true],
    [true, true, true],
    [false, true, true, true],
    [false, true, false, true, true, true],
    [false, true]]

/-- Words fixing `0` and mapping `1` to each point `y ≠ 0`. -/
def m11St : List (List Bool) :=
  [[],
    [],
    [true, true, true, false, true, true, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, false],
    [false, true, true, true, false, true, false, true, false],
    [true, true, false, true, true, false],
    [true, true, true, false, true, false, true, false],
    [false, true, true, false, true, false, true, false, true, false],
    [true, true, false, true, false, true, false, true, false],
    [false],
    [false, true, true, false, true, false, true, true, false, true, false]]

section
variable [h0 : Corpus.Mathieu.Bridges]
include h0

/-- **`M₁₁` satisfies the permutation-labelling criterion** (natural 2-transitive action of
degree 11). -/
theorem permLabelling_M11 : PermLabelling TauCeti.SporadicName.M11.Group :=
  permLabelling_of_words _ (Classical.choice Corpus.Mathieu.Bridges.m11_nonempty_mulEquiv) m11Gen m11Gen_mem
    0 1 m11Tr m11St [true]
    [false]
    [false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end

end M11

section M12

/-- The two corpus generators of `M₁₂` (`false`, `true`). -/
def m12Gen (c : Bool) : Perm (Fin 12) :=
  if c then List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6]
  else List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

theorem m12Gen_mem (c : Bool) : m12Gen c ∈ Corpus.Mathieu.M12 := by
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Words mapping `0` to each point. -/
def m12Tr : List (List Bool) :=
  [[],
    [true, false],
    [true, true, false],
    [false],
    [false, true, false, true, true, false, true, true, false],
    [true, true, false, true, true, false],
    [true, false, true, true, false],
    [true],
    [true, true],
    [false, true, true, false],
    [true, false, true, true, false, true, true, false],
    [false, true, true, false, true, true, false]]

/-- Words fixing `0` and mapping `1` to each point `y ≠ 0`. -/
def m12St : List (List Bool) :=
  [[],
    [],
    [false, true, false, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true, true, false, true, false],
    [true, false, true, true, false, true, true, false, true, false],
    [true, true, false, true],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, false],
    [true, false, true, true],
    [false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false],
    [true, false, true, false, true, false, true, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, false],
    [false, true, true, false, true, false]]

section
variable [h0 : Corpus.Mathieu.Bridges]
include h0

/-- **`M₁₂` satisfies the permutation-labelling criterion** (natural 2-transitive action of
degree 12). -/
theorem permLabelling_M12 : PermLabelling TauCeti.SporadicName.M12.Group :=
  permLabelling_of_words _ (Classical.choice Corpus.Mathieu.Bridges.m12_nonempty_mulEquiv) m12Gen m12Gen_mem
    0 1 m12Tr m12St [true]
    [true, false, true, true]
    [false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false, true]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end

end M12

section M22

/-- The two corpus generators of `M₂₂` (`false`, `true`). -/
def m22Gen (c : Bool) : Perm (Fin 22) :=
  if c then List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]
  else List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

theorem m22Gen_mem (c : Bool) : m22Gen c ∈ Corpus.Mathieu.M22 := by
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Words mapping `0` to each point. -/
def m22Tr : List (List Bool) :=
  [[],
    [true, false],
    [true, true],
    [true, true, true, false],
    [true, false, true, true, true, false],
    [false, true],
    [true, true, false, true],
    [false, true, false],
    [false, true, true, true, false, true, false],
    [true, true, true, false, true, false],
    [true, false, true],
    [false, true, true, true, false],
    [false],
    [true, false, true, false],
    [true, true, true, false, true],
    [false, true, true],
    [false, true, true, false, true],
    [true, true, false],
    [true, false, true, true, false, true],
    [true, true, false, true, false],
    [true, true, true],
    [true]]

/-- Words fixing `0` and mapping `1` to each point `y ≠ 0`. -/
def m22St : List (List Bool) :=
  [[],
    [],
    [true, true, true, false, true, false, true, false, true, true, false, true, true, false, true],
    [false, true, true, true, false, true, true, true, false, true, false, true],
    [true, true, false, true, false, true, true],
    [true, true, true, false, true, false, true, true, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, true, true],
    [false, true, true, false, true, false, true, true, true, false, true, false, true],
    [false, true, false, true, true, true, false, true, false, true, true, true, false],
    [true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false],
    [true, true, false, true, false, true, false, true, true, true, false, true, false, true, false],
    [true, true, false, true, false, true, true, true, false, true, false, true, false, true, true],
    [true, false, true, false, true, false, true, true],
    [true, false, true, false, true, false, true, true, true, false, true, true, true],
    [false, true, true, true, false, true, false, true, false, true, true, false, true, false, true],
    [true, true, false, true, true, true, false, true, true, true, false, true, true, true],
    [true, true, true, false, true, true, true, false, true, false, true, false],
    [false, true, false, true, false, true, false, true, true, true, false],
    [false, true, false, true, false, true, true, false, true, false, true, true, true, false],
    [true, false, true, true, false, true, false, true, true, false, true, false, true, false],
    [true, false, true, false, true, true, true, false, true, true, true, false, true, true, true],
    [true, false, true, true, true]]

section
variable [h0 : Corpus.Mathieu.Bridges]
include h0

/-- **`M₂₂` satisfies the permutation-labelling criterion** (natural 2-transitive action of
degree 22). -/
theorem permLabelling_M22 : PermLabelling TauCeti.SporadicName.M22.Group :=
  permLabelling_of_words _ (Classical.choice Corpus.Mathieu.Bridges.m22_nonempty_mulEquiv) m22Gen m22Gen_mem
    0 1 m22Tr m22St [true]
    [true, false, true, true, true]
    [false, true, false, true, true, true, false, true, false, true, true, true, false]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end

end M22

section M23

/-- The two corpus generators of `M₂₃` (`false`, `true`). -/
def m23Gen (c : Bool) : Perm (Fin 23) :=
  if c then List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]
  else List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]

theorem m23Gen_mem (c : Bool) : m23Gen c ∈ Corpus.Mathieu.M23 := by
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Words mapping `0` to each point. -/
def m23Tr : List (List Bool) :=
  [[],
    [false],
    [true, true, true],
    [false, true, true, true],
    [true, false, true, true, true],
    [true, true, true, false, true, true, false],
    [false, true, true, false, true, true, true],
    [true, true, false, true, true, true],
    [true, false],
    [false, true, false],
    [true, true],
    [true, true, true, false],
    [false, true, false, true, true, false],
    [true, false, true, true, false],
    [false, true],
    [true],
    [true, false, true],
    [true, true, false, true, true, false],
    [false, true, false, true, false, true, true, false],
    [true, false, true, false, true, true, false],
    [true, true, false],
    [false, true, true, false],
    [true, true, true, false, true, true, true]]

/-- Words fixing `0` and mapping `1` to each point `y ≠ 0`. -/
def m23St : List (List Bool) :=
  [[],
    [],
    [true, true, true, false, true, true, true, false, true, false, true],
    [true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false],
    [false, true, false, true, true, true, false],
    [true, true, true, false, true, false, true, false, true],
    [true, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false],
    [true, true, false, true, true, false, true, true, true, false, true, false, true, false],
    [false, true, true, false, true, false, true, true, true, false, true, false, true, false, true, false],
    [false, true, true, true, false, true, false, true, false, true, true, false, true, true],
    [false, true, false, true, false, true, false, true, true, true, false, true, true, false],
    [false, true, true, false, true, false, true, false, true, true, false, true, true, false],
    [true, true, false, true, false, true, false, true, false, true],
    [false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, true],
    [true, true, false, true, false, true, true, true, false, true, false, true],
    [false, true, true, true, false, true, false, true, false],
    [false, true, true, false, true, false, true, true, true, false, true, true, false],
    [true, true, false, true, true],
    [false, true, false, true, true, true, false, true, true, false, true, true],
    [true, false, true, false, true, true, true, false, true, true, true],
    [true, true, true, false, true, false, true, false, true, true, true, false, true, true],
    [true, false, true, true, false, true, false, true, false, true, false, true, false, true, true],
    [false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false]]

section
variable [h0 : Corpus.Mathieu.Bridges]
include h0

/-- **`M₂₃` satisfies the permutation-labelling criterion** (natural 2-transitive action of
degree 23). -/
theorem permLabelling_M23 : PermLabelling TauCeti.SporadicName.M23.Group :=
  permLabelling_of_words _ (Classical.choice Corpus.Mathieu.Bridges.m23_nonempty_mulEquiv) m23Gen m23Gen_mem
    0 1 m23Tr m23St [true]
    [true, true, false, true, true]
    [false, true, false, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false, true, true]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end

end M23

section M24

/-- The two corpus generators of `M₂₄` (`false`, `true`). -/
def m24Gen (c : Bool) : Perm (Fin 24) :=
  if c then List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]
  else List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]

theorem m24Gen_mem (c : Bool) : m24Gen c ∈ Corpus.Mathieu.M24 := by
  cases c
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Words mapping `0` to each point. -/
def m24Tr : List (List Bool) :=
  [[],
    [true, false, true, false, true, true, false, true, false],
    [true, true, false, true, false],
    [false],
    [false, true, true, false, true, true, false, true, false],
    [true, false],
    [false, true, false, true, false, true, true, false, true, false],
    [false, true, false, true, false],
    [false, true, false],
    [true, true, false, true, true, false, true, true, false, true, false],
    [false, true, false, true, true, false, true, true, false, true, false],
    [false, true, true, false, true, false, true, true, false, true, false],
    [true, true, false, true, true, false, true, false],
    [false, true, false, true, true, false, true, false],
    [true, false, true, false],
    [true, false, true, true, false, true, false],
    [false, true, true, false, true, false],
    [true, false, true, true, false, true, true, false, true, false],
    [false, true, true, false, true, true, false, true, true, false, true, false],
    [false, true, false, true, true, false, true, true, false, true, true, false, true, false],
    [true, true, false, true, false, true, true, false, true, false],
    [false, true, true, false, true, true, false, true, true, false, true, true, false, true, false],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, false],
    [true, false, true, true, false, true, true, false, true, true, false, true, false]]

/-- Words fixing `0` and mapping `1` to each point `y ≠ 0`. -/
def m24St : List (List Bool) :=
  [[],
    [],
    [false, true, false, true, true, false, true, true, false, true, false, true, false, true, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false],
    [false, true, false, true, false, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true],
    [true, true, false],
    [true, false, true, true, false, true, true, false, true, false, true, true, false, true],
    [true, false, true, true, false, true, false, true, false, true, false, true, true, false],
    [true, false, true, true, false, true, false, true, false, true, true],
    [false, true, false, true, false, true, false, true, false, true],
    [false, true],
    [false, true, true, false, true, true, false, true, false, true, false, true, true],
    [true, true, false, true, true, false],
    [true, true, false, true, true, false, true, true, false, true, true, false],
    [false, true, false, true, false, true],
    [true, true, false, true, true, false, true, true, false],
    [false, true, false, true, false, true, false, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true],
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true],
    [false, true, false, true],
    [true, false, true, true, false, true, true, false, true, false, true, true],
    [true, true, false, true, false, true, true, false, true, false, true, false, true, true],
    [true, false, true, true, false, true, false, true, false, true, true, false, true]]

section
variable [h0 : Corpus.Mathieu.Bridges]
include h0

set_option maxRecDepth 100000 in
/-- **`M₂₄` satisfies the permutation-labelling criterion** (natural 2-transitive action of
degree 24). -/
theorem permLabelling_M24 : PermLabelling TauCeti.SporadicName.M24.Group :=
  permLabelling_of_words _ (Classical.choice Corpus.Mathieu.Bridges.m24_nonempty_mulEquiv) m24Gen m24Gen_mem
    0 1 m24Tr m24St [true]
    [false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true]
    [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

end

end M24

end CFSGOutside.HallPaige
