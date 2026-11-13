import CFSGOutside.HallPaige.Statements
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# Kernel-checkable certificates for the permutation-labelling criterion

This file reduces `CFSGOutside.HallPaige.PermLabelling G` for a group `G` acting on `Fin n` to a list of
Boolean checks on natural-number data, all of which the kernel evaluates (`decide +kernel`).

* Generators act through functions `gf i b : ℕ → ℕ` (`b = true`: the generator, `b = false`: its
  inverse), usually lookups in tables packed into one natural number (`tget`).
* A `Model` is a homomorphism `ρ : G →* Perm (Fin n)` sending generators of `G` to these tables;
  `presModel` builds one for a `TauCeti.GroupPresentation` from a check of its relators.
* Transitivity and the orbits of the point stabilizer `H` are certified by spanning trees (`reach`).
* That the labelling `L` is `H`-invariant is certified by colour refinement: starting from the
  partition `{x₀}, rest`, each refinement step relabels points by the multiset of labels of their
  out-neighbours in a digraph invariant under the generators (`InvL`, `invL_base`, `invL_step`);
  or, given an upper bound for `|G|`, by showing that words fixing `x₀` generate the whole point
  stabilizer (a stabilizer chain bounds the order of the subgroup they generate from below) and
  that `L` is invariant under them (`invL_of_order`).
* `permLabelling` assembles the criterion; `presModel` and `Model.injective_of_simple` provide
  the faithful model of a presented simple group.

Large checks over all points can be split into chunks (`allFrom`, `allLt_of_chunks`), each its
own kernel check: this bounds the memory the kernel's caches take.
-/

namespace CFSGOutside.HallPaige.OrbitCert

open Equiv

universe u

/-! ### Boolean loops and packed tables -/

/-- Entry `i` of a table packed into one natural number with `B` bits per entry. -/
def tget (B t i : ℕ) : ℕ := Nat.land (Nat.shiftRight t (Nat.mul B i)) (Nat.sub (Nat.pow 2 B) 1)

/-- Entry `i` of a table stored in blocks of `C` entries, `f j` being the `j`-th block packed
with `B` bits per entry. Keeping the packed numbers small keeps kernel evaluation cheap. -/
def tblk (B C : ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ := tget B (f (Nat.div i C)) (Nat.mod i C)

/-- `allLt n p` holds iff `p i` holds for every `i < n`. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => p k && allLt k p

theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allLt]
  | succ k ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h k (Nat.lt_succ_self k), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/-- `p (a + i)` holds for every `i < len` with `a + i < n`: a chunk of `allLt n p`. -/
def allFrom (n a len : ℕ) (p : ℕ → Bool) : Bool :=
  allLt len fun i => !Nat.blt (a + i) n || p (a + i)

/-- `allLt n p` from checks of chunks of length `C` (each chunk a separate kernel check). -/
theorem allLt_of_chunks {n C m : ℕ} {p : ℕ → Bool} (hn : n ≤ m * C)
    (h : ∀ j < m, allFrom n (j * C) C p = true) : allLt n p = true := by
  rw [allLt_iff]
  intro i hi
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with hC | hC
    · subst hC; omega
    · exact hC
  have hj : i / C < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have := allLt_iff.1 (h _ hj) (i % C) (Nat.mod_lt _ hC)
  have e : i / C * C + i % C = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i C
  rw [e] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h' | h'
  · exact absurd (Nat.blt_eq.mpr hi) (by rw [h']; decide)
  · exact h'

/-- The number of `i < n` with `p i`. -/
def countLt : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, p => countLt k p + cond (p k) 1 0

theorem countLt_eq (n : ℕ) (p : ℕ → Bool) :
    countLt n p = ((Finset.range n).filter fun i => p i = true).card := by
  induction n with
  | zero => simp [countLt]
  | succ k ih =>
    rw [countLt, ih, Finset.range_add_one, Finset.filter_insert]
    cases h : p k
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

/-- `∑_{i < n} f i`. -/
def sumLt : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => sumLt k f + f k

theorem sumLt_eq (n : ℕ) (f : ℕ → ℕ) : sumLt n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumLt, ih, Finset.sum_range_succ]

/-- `t` and `ti` are mutually inverse permutations of `{0, …, n-1}`. -/
def PermOK (n : ℕ) (t ti : ℕ → ℕ) : Bool :=
  allLt n fun i => Nat.blt (t i) n && Nat.blt (ti i) n && Nat.beq (ti (t i)) i &&
    Nat.beq (t (ti i)) i

theorem PermOK_spec {n : ℕ} {t ti : ℕ → ℕ} (h : PermOK n t ti = true) {i : ℕ} (hi : i < n) :
    t i < n ∧ ti i < n ∧ ti (t i) = i ∧ t (ti i) = i := by
  have := allLt_iff.1 h i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- The permutation of `Fin n` defined by a pair of inverse tables. -/
def mkPerm (n : ℕ) (t ti : ℕ → ℕ) (h : PermOK n t ti = true) : Perm (Fin n) where
  toFun x := ⟨t x, (PermOK_spec h x.2).1⟩
  invFun x := ⟨ti x, (PermOK_spec h x.2).2.1⟩
  left_inv x := Fin.ext (PermOK_spec h x.2).2.2.1
  right_inv x := Fin.ext (PermOK_spec h x.2).2.2.2

/-! ### Words -/

/-- The `k` generator tables are permutations of `{0, …, n-1}`. -/
def gensOK (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) : Bool :=
  allLt k fun i => PermOK n (gf i true) (gf i false)

/-- Evaluation of a word (a list of signed generator indices, applied right to left, as a product
of permutations) on a point. Letters with index `≥ k` act trivially. -/
def ev (k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) : List (ℕ × Bool) → ℕ → ℕ
  | [], x => x
  | l :: w, x => cond (Nat.blt l.1 k) (gf l.1 l.2 (ev k gf w x)) (ev k gf w x)

theorem ev_append (k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (v w : List (ℕ × Bool)) (x : ℕ) :
    ev k gf (v ++ w) x = ev k gf v (ev k gf w x) := by
  induction v with
  | nil => rfl
  | cons l v ih => simp only [List.cons_append, ev, ih]

/-- A homomorphism `ρ : G →* Perm (Fin n)` and generators `gen i` (`i < k`) of `G` with
`ρ (gen i)` given by the table `gf i true`. -/
structure Model (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (G : Type*) [Group G] where
  ρ : G →* Perm (Fin n)
  gen : ℕ → G
  closure_eq : Subgroup.closure (gen '' {i | i < k}) = ⊤
  ρ_gen : ∀ i < k, ∀ x : Fin n, (ρ (gen i) x).val = gf i true x.val

namespace Model

variable {n k : ℕ} {gf : ℕ → Bool → ℕ → ℕ} {G : Type*} [Group G] (M : Model n k gf G)

/-- The element of `G` denoted by a word. -/
def word : List (ℕ × Bool) → G
  | [] => 1
  | l :: w => (if l.1 < k then cond l.2 (M.gen l.1) (M.gen l.1)⁻¹ else 1) * word w

theorem word_append (v w : List (ℕ × Bool)) : M.word (v ++ w) = M.word v * M.word w := by
  induction v with
  | nil => simp [word]
  | cons l v ih => simp only [List.cons_append, word, ih, mul_assoc]

theorem ρ_gen_inv (hgf : gensOK n k gf = true) {i : ℕ} (hi : i < k) (x : Fin n) :
    (M.ρ (M.gen i)⁻¹ x).val = gf i false x.val := by
  have hP := allLt_iff.1 hgf i hi
  obtain ⟨-, h2, -, h4⟩ := PermOK_spec hP x.2
  have : M.ρ (M.gen i) ⟨gf i false x, h2⟩ = x := Fin.ext (by rw [M.ρ_gen i hi]; exact h4)
  rw [map_inv, Perm.inv_eq_iff_eq.mpr this.symm]

theorem ρ_word (hgf : gensOK n k gf = true) (w : List (ℕ × Bool)) (x : Fin n) :
    (M.ρ (M.word w) x).val = ev k gf w x.val := by
  induction w generalizing x with
  | nil => simp [word, ev]
  | cons l w ih =>
    rw [word, map_mul, Perm.mul_apply, ev]
    by_cases hl : l.1 < k
    · rw [if_pos hl, show Nat.blt l.1 k = true from Nat.blt_eq.mpr hl, cond_true, ← ih]
      cases hb : l.2
      · exact M.ρ_gen_inv hgf hl _
      · exact M.ρ_gen l.1 hl _
    · rw [if_neg hl, show Nat.blt l.1 k = false from by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hl, cond_false, ← ih, map_one,
        Perm.one_apply]

/-- The action of `g` on natural numbers: `ρ g` below `n`, the identity elsewhere. -/
def act (g : G) (z : ℕ) : ℕ := if hz : z < n then (M.ρ g ⟨z, hz⟩).val else z

theorem act_of_lt (g : G) {z : ℕ} (hz : z < n) : M.act g z = (M.ρ g ⟨z, hz⟩).val :=
  dif_pos hz

theorem act_lt (g : G) {z : ℕ} (hz : z < n) : M.act g z < n := by
  rw [M.act_of_lt g hz]; exact Fin.isLt _

theorem act_mul (g h : G) (z : ℕ) : M.act (g * h) z = M.act g (M.act h z) := by
  by_cases hz : z < n
  · rw [M.act_of_lt _ hz, M.act_of_lt _ hz, M.act_of_lt _ (Fin.isLt _), map_mul, Perm.mul_apply]
  · simp [act, hz]

theorem act_one (z : ℕ) : M.act 1 z = z := by
  by_cases hz : z < n <;> simp [act, hz]

theorem act_inv_act (g : G) (z : ℕ) : M.act g⁻¹ (M.act g z) = z := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : G) (z : ℕ) : M.act g (M.act g⁻¹ z) = z := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_injective (g : G) : Function.Injective (M.act g) := fun a b h => by
  rw [← M.act_inv_act g a, h, M.act_inv_act]

theorem act_word (hgf : gensOK n k gf = true) (w : List (ℕ × Bool)) {z : ℕ} (hz : z < n) :
    M.act (M.word w) z = ev k gf w z := by
  rw [M.act_of_lt _ hz, M.ρ_word hgf]

theorem act_gen (i : ℕ) (hi : i < k) {z : ℕ} (hz : z < n) : M.act (M.gen i) z = gf i true z := by
  rw [M.act_of_lt _ hz, M.ρ_gen i hi]

/-- Induction over `G` from the generators. -/
theorem induction {p : G → Prop} (hgen : ∀ i < k, p (M.gen i)) (one : p 1)
    (mul : ∀ g h, p g → p h → p (g * h)) (inv : ∀ g, p g → p g⁻¹) (g : G) : p g := by
  have hg : g ∈ Subgroup.closure (M.gen '' {i | i < k}) := by rw [M.closure_eq]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact hgen i hi
  | one => exact one
  | mul x y _ _ hx hy => exact mul x y hx hy
  | inv x _ hx => exact inv x hx

/-! ### Spanning trees -/

/-- Spanning-forest certificate: each `y < n` is either a root (`rt y = y`) or is obtained from
its parent `par y` (of smaller depth `dep`, with the same root) by the move `mw[mv y]`. -/
def reachBody (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (mw : List (List (ℕ × Bool)))
    (rt par mv dep : ℕ → ℕ) (y : ℕ) : Bool :=
  Nat.blt (rt y) n && (Nat.beq (rt y) y || (Nat.blt (par y) n &&
    Nat.blt (dep (par y)) (dep y) && Nat.beq (rt (par y)) (rt y) &&
    Nat.beq (ev k gf (mw.getD (mv y) []) (par y)) y))

/-- Spanning-forest certificate (see `reachBody`). -/
def reachOK (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (mw : List (List (ℕ × Bool)))
    (rt par mv dep : ℕ → ℕ) : Bool :=
  allLt n (reachBody n k gf mw rt par mv dep)

theorem reach (hgf : gensOK n k gf = true) (K : Subgroup G) (mw : List (List (ℕ × Bool)))
    (hmw : ∀ w ∈ mw, M.word w ∈ K) (rt par mv dep : ℕ → ℕ)
    (h : reachOK n k gf mw rt par mv dep = true) :
    ∀ y < n, ∃ g ∈ K, M.act g (rt y) = y := by
  have key : ∀ d, ∀ y < n, dep y = d → ∃ g ∈ K, M.act g (rt y) = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy hd
      have hc := allLt_iff.1 h y hy
      simp only [reachBody, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨-, hc | ⟨⟨⟨hp, hdep⟩, hrt⟩, hev⟩⟩ := hc
      · exact ⟨1, K.one_mem, by rw [act_one, hc]⟩
      · obtain ⟨g, hgK, hg⟩ := ih _ (hd ▸ hdep) _ hp rfl
        have hw : mw.getD (mv y) [] ∈ mw ∨ mw.getD (mv y) [] = [] := by
          rw [List.getD_eq_getElem?_getD]
          cases hm : mw[mv y]? with
          | none => right; rfl
          | some w => left; exact List.mem_of_getElem? hm
        have hwK : M.word (mw.getD (mv y) []) ∈ K := by
          rcases hw with hw | hw
          · exact hmw _ hw
          · rw [hw]; exact K.one_mem
        refine ⟨M.word (mw.getD (mv y) []) * g, K.mul_mem hwK hgK, ?_⟩
        rw [act_mul, ← hrt, hg, M.act_word hgf _ hp, hev]
  exact fun y hy => key _ y hy rfl

/-! ### Invariant digraphs and colour refinement -/

/-- The `j`-th out-neighbour of `y` in a digraph of out-valency `kk` with table `nb`. -/
def nbr (kk : ℕ) (nb : ℕ → ℕ) (y j : ℕ) : ℕ := nb (y * kk + j)

/-- The rows of the neighbour table are strictly increasing and below `n`. -/
def rowsOK (n kk : ℕ) (nb : ℕ → ℕ) : Bool :=
  allLt n fun y => allLt kk fun j => Nat.blt (nbr kk nb y j) n &&
    (Nat.beq j 0 || Nat.blt (nbr kk nb y (j - 1)) (nbr kk nb y j))

/-- The permutation `s` maps each out-neighbour `nbr y j` to the out-neighbour `nbr (s y) (c ..)`
of `s y`. -/
def genGraphOK (n kk : ℕ) (nb s c : ℕ → ℕ) : Bool :=
  allLt n fun y => allLt kk fun j =>
    Nat.blt (c (y * kk + j)) kk && Nat.beq (nbr kk nb (s y) (c (y * kk + j))) (s (nbr kk nb y j))

/-- The out-neighbourhood of `y`. -/
def nbhd (kk : ℕ) (nb : ℕ → ℕ) (y : ℕ) : Finset ℕ := (Finset.range kk).image (nbr kk nb y)

theorem rowsOK_strictMono {kk : ℕ} {nb : ℕ → ℕ} (h : rowsOK n kk nb = true) {y : ℕ} (hy : y < n)
    {i j : ℕ} (hij : i < j) (hj : j < kk) : nbr kk nb y i < nbr kk nb y j := by
  have hrow := allLt_iff.1 (allLt_iff.1 h y hy)
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := hrow (j + 1) hj
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hs
    have hlt : nbr kk nb y j < nbr kk nb y (j + 1) := by
      rcases hs.2 with h0 | h0
      · omega
      · simpa using h0
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h' | rfl
    · exact (ih h' (by omega)).trans hlt
    · exact hlt

theorem rowsOK_injOn {kk : ℕ} {nb : ℕ → ℕ} (h : rowsOK n kk nb = true) {y : ℕ} (hy : y < n) :
    Set.InjOn (nbr kk nb y) (Finset.range kk : Set ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact (rowsOK_strictMono h hy h' hj).ne hij
  · exact (rowsOK_strictMono h hy h' hi).ne hij.symm

theorem rowsOK_card {kk : ℕ} {nb : ℕ → ℕ} (h : rowsOK n kk nb = true) {y : ℕ} (hy : y < n) :
    (nbhd kk nb y).card = kk := by
  rw [nbhd, Finset.card_image_of_injOn (rowsOK_injOn h hy), Finset.card_range]

theorem rowsOK_lt {kk : ℕ} {nb : ℕ → ℕ} (h : rowsOK n kk nb = true) {y : ℕ} (hy : y < n)
    {z : ℕ} (hz : z ∈ nbhd kk nb y) : z < n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
  have := allLt_iff.1 (allLt_iff.1 h y hy) j (Finset.mem_range.1 hj)
  simp only [Bool.and_eq_true, Nat.blt_eq] at this
  exact this.1

/-- `g` maps out-neighbourhoods onto out-neighbourhoods. -/
def Preserves (kk : ℕ) (nb : ℕ → ℕ) (g : G) : Prop :=
  ∀ y < n, (nbhd kk nb y).image (M.act g) = nbhd kk nb (M.act g y)

/-- If the rows are injective and every generator maps out-neighbours to out-neighbours, then
every element of `G` preserves the digraph. -/
theorem preserves_of_gens {kk : ℕ} {nb : ℕ → ℕ} (hrows : rowsOK n kk nb = true)
    (c : ℕ → ℕ → ℕ) (hc : ∀ i < k, genGraphOK n kk nb (gf i true) (c i) = true) (g : G) :
    M.Preserves kk nb g := by
  refine M.induction (p := M.Preserves kk nb) ?_ ?_ ?_ ?_ g
  · intro i hi y hy
    have hsy : M.act (M.gen i) y < n := M.act_lt _ hy
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz'
      have hjk := Finset.mem_range.1 hj
      have := allLt_iff.1 (allLt_iff.1 (hc i hi) y hy) j hjk
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
      refine Finset.mem_image.2 ⟨_, Finset.mem_range.2 this.1, ?_⟩
      rw [M.act_gen i hi hy, this.2, M.act_gen i hi (rowsOK_lt hrows hy hz')]
    · rw [rowsOK_card hrows hsy, Finset.card_image_of_injective _ (M.act_injective _), rowsOK_card hrows hy]
  · intro y _
    have e : M.act 1 = id := funext M.act_one
    rw [e, Finset.image_id]
    rfl
  · intro g h hg hh y hy
    have e : M.act (g * h) = M.act g ∘ M.act h := funext (M.act_mul g h)
    rw [e, ← Finset.image_image, hh y hy, hg _ (M.act_lt h hy)]
    rfl
  · intro g hg y hy
    have hy' : M.act g⁻¹ y < n := M.act_lt _ hy
    have := hg _ hy'
    rw [act_act_inv] at this
    have e : M.act g⁻¹ ∘ M.act g = id := funext (M.act_inv_act g)
    rw [← this, Finset.image_image, e, Finset.image_id]

/-- `L` is invariant under the stabilizer of `x0`. -/
def InvL (x0 : ℕ) (L : ℕ → ℕ) : Prop :=
  ∀ g : G, M.act g x0 = x0 → ∀ z < n, L (M.act g z) = L z

/-- The base labelling `{x0}, rest` is invariant under the stabilizer of `x0`. -/
theorem invL_base (x0 : ℕ) : M.InvL x0 fun z => cond (Nat.beq z x0) 0 1 := by
  intro g hg z _
  have : (M.act g z = x0) ↔ z = x0 := by
    constructor
    · intro h; exact M.act_injective g (h.trans hg.symm)
    · rintro rfl; exact hg
  by_cases hz : z = x0
  · simp [hz, hg]
  · have h1 : ¬ M.act g z = x0 := fun h => hz (this.1 h)
    simp [Nat.beq_eq, h1, hz]

/-- The code of `y` with respect to labelling `L` and a digraph: `L y` and the multiset of labels
of the out-neighbours of `y`, encoded as `L y + K * ∑ₖ Q ^ L (nbr y j)`. -/
def code (kk : ℕ) (nb : ℕ → ℕ) (L : ℕ → ℕ) (K Q y : ℕ) : ℕ :=
  L y + K * sumLt kk fun j => Q ^ L (nbr kk nb y j)

/-- One refinement step: the new label `L' y < r'` determines the code of `y` through the
injective table `κ`. -/
def stepOK (n kk : ℕ) (nb L : ℕ → ℕ) (K Q r' : ℕ) (L' κ : ℕ → ℕ) : Bool :=
  allLt n (fun y => Nat.blt (L' y) r' && Nat.beq (κ (L' y)) (code kk nb L K Q y)) &&
    allLt r' fun a => allLt a fun b => !Nat.beq (κ a) (κ b)

theorem invL_step {x0 : ℕ} {L : ℕ → ℕ} (hL : M.InvL x0 L) {kk : ℕ} {nb : ℕ → ℕ}
    (hrows : rowsOK n kk nb = true) (hpres : ∀ g : G, M.Preserves kk nb g) {K Q r' : ℕ}
    {L' κ : ℕ → ℕ} (h : stepOK n kk nb L K Q r' L' κ = true) : M.InvL x0 L' := by
  intro g hg z hz
  simp only [stepOK, Bool.and_eq_true] at h
  have h1 := allLt_iff.1 h.1
  have h2 := allLt_iff.1 h.2
  have hcode : ∀ y < n, code kk nb L K Q y = L y + K * ∑ z ∈ nbhd kk nb y, Q ^ L z := by
    intro y hy
    rw [code, sumLt_eq, nbhd, Finset.sum_image (rowsOK_injOn hrows hy)]
  have hgz : M.act g z < n := M.act_lt g hz
  have hinv : code kk nb L K Q (M.act g z) = code kk nb L K Q z := by
    rw [hcode _ hgz, hcode _ hz, ← hpres g z hz, Finset.sum_image (fun a _ b _ h =>
      M.act_injective g h), hL g hg z hz]
    congr 2
    exact Finset.sum_congr rfl fun y hy => by rw [hL g hg y (rowsOK_lt hrows hz hy)]
  have ha := h1 _ hgz
  have hb := h1 _ hz
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ha hb
  have hκ : κ (L' (M.act g z)) = κ (L' z) := by rw [ha.2, hb.2, hinv]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := allLt_iff.1 (h2 _ hb.1) _ hlt
    simp [Nat.beq_eq, hκ] at this
  · have := allLt_iff.1 (h2 _ ha.1) _ hlt
    simp [Nat.beq_eq, hκ] at this

/-! ### The criterion -/

/-- The Klein-four check: words `u, v` fixing `x0`, of order dividing two, commuting, nontrivial
(witnesses `p1, p2`) and distinct (witness `p3`). -/
def kleinBody (k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (u v : List (ℕ × Bool)) (x : ℕ) : Bool :=
  Nat.beq (ev k gf u (ev k gf u x)) x && Nat.beq (ev k gf v (ev k gf v x)) x &&
    Nat.beq (ev k gf u (ev k gf v x)) (ev k gf v (ev k gf u x))

/-- The Klein-four check (see `kleinBody`). -/
def kleinOK (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (x0 : ℕ) (u v : List (ℕ × Bool)) (p1 p2 p3 : ℕ) :
    Bool :=
  Nat.beq (ev k gf u x0) x0 && Nat.beq (ev k gf v x0) x0 &&
    allLt n (kleinBody k gf u v) &&
    Nat.blt p1 n && Nat.blt p2 n && Nat.blt p3 n &&
    !Nat.beq (ev k gf u p1) p1 && !Nat.beq (ev k gf v p2) p2 &&
    !Nat.beq (ev k gf u p3) (ev k gf v p3)

/-- The pairs check: for each label `c < r`, the words `wa c`, `wb c` move `x0` into class `c`
and their product moves it into class `σ c`. -/
def pairsOK (k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (x0 r : ℕ) (L sg : ℕ → ℕ)
    (wa wb : ℕ → List (ℕ × Bool)) : Bool :=
  allLt r fun c => Nat.beq (L (ev k gf (wa c) x0)) c && Nat.beq (L (ev k gf (wb c) x0)) c &&
    Nat.beq (L (ev k gf (wa c) (ev k gf (wb c) x0))) (sg c)

/-- `σ` preserves the sizes of the label classes. -/
def cardsOK (n r : ℕ) (L sg : ℕ → ℕ) : Bool :=
  allLt r fun c => Nat.beq (countLt n fun y => Nat.beq (L y) (sg c)) (countLt n fun y => Nat.beq (L y) c)

theorem natCard_eq_countLt {n : ℕ} (f : Fin n → ℕ) (L : ℕ → ℕ) (hf : ∀ y, f y = L y) (c : ℕ) :
    Nat.card {y : Fin n // f y = c} = countLt n fun y => Nat.beq (L y) c := by
  classical
  rw [countLt_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp [Nat.beq_eq, ← hf, hy]
  · intro a _ b _ h; exact Fin.ext h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range, Nat.beq_eq] at hy
    exact ⟨⟨y, hy.1⟩, by simp [hf, hy.2], rfl⟩

/-- **Certificate form of the permutation-labelling criterion.** -/
theorem permLabelling {G : Type u} [Group G] {n k : ℕ} {gf : ℕ → Bool → ℕ → ℕ}
    (M : Model n k gf G) (hgf : gensOK n k gf = true) (hinj : Function.Injective M.ρ)
    (x0 : ℕ) (hx0 : x0 < n) (y1 : ℕ) (hy1 : y1 < n) (hy10 : y1 ≠ x0)
    (tpar tmv tdep : ℕ → ℕ)
    (htr : reachOK n k gf ((List.range k).map fun i => [(i, true)]) (fun _ => x0) tpar tmv tdep
      = true)
    (r : ℕ) (L : ℕ → ℕ) (hL : M.InvL x0 L) (hLr : allLt n (fun y => Nat.blt (L y) r) = true)
    (rep : ℕ → ℕ) (hs : List (List (ℕ × Bool)))
    (hhs : (hs.all fun w => Nat.beq (ev k gf w x0) x0) = true) (spar smv sdep : ℕ → ℕ)
    (hsp : reachOK n k gf hs (fun y => rep (L y)) spar smv sdep = true)
    (sg sgi : ℕ → ℕ) (hsg : PermOK r sg sgi = true) (hcards : cardsOK n r L sg = true)
    (wa wb : ℕ → List (ℕ × Bool)) (hpairs : pairsOK k gf x0 r L sg wa wb = true)
    (u v : List (ℕ × Bool)) (p1 p2 p3 : ℕ) (hklein : kleinOK n k gf x0 u v p1 p2 p3 = true) :
    PermLabelling G := by
  classical
  haveI : Finite G := Finite.of_injective _ hinj
  have hLr' : ∀ y < n, L y < r := fun y hy => by simpa using allLt_iff.1 hLr y hy
  let lab : Fin n → Fin r := fun y => ⟨L y, hLr' y y.2⟩
  let σ : Perm (Fin r) := mkPerm r sg sgi hsg
  let X0 : Fin n := ⟨x0, hx0⟩
  have hfix : ∀ g : G, M.ρ g X0 = X0 ↔ M.act g x0 = x0 := fun g => by
    rw [M.act_of_lt g hx0, Fin.ext_iff]
  -- the stabilizer
  let H : Subgroup G := (MulAction.stabilizer (Perm (Fin n)) X0).comap M.ρ
  have hH : ∀ g, g ∈ H ↔ M.act g x0 = x0 := fun g => by
    rw [← hfix]; simp [H, MulAction.mem_stabilizer_iff, Perm.smul_def]
  have hsH : ∀ w ∈ hs, M.word w ∈ H := by
    intro w hw
    rw [hH, M.act_word hgf w hx0]
    have := List.all_eq_true.1 hhs w hw
    simpa using this
  have hsreach := M.reach hgf H hs (hsH) _ spar smv sdep hsp
  have htreach := M.reach hgf ⊤ _ (fun _ _ => Subgroup.mem_top _) _ tpar tmv tdep htr
  refine ⟨n, M.ρ, X0, r, lab, σ, ?_, ?_, ?_, ?_, ?_, ⟨⟨y1, hy1⟩, fun h => hy10 (by
    simpa [X0] using congrArg Fin.val h)⟩⟩
  · -- transitivity
    intro y
    obtain ⟨g, -, hg⟩ := htreach y y.2
    exact ⟨g, Fin.ext (by rw [← M.act_of_lt g hx0]; exact hg)⟩
  · -- the labels are the suborbits
    intro y y'
    constructor
    · intro hyy
      have hyy' : L y = L y' := congrArg Fin.val hyy
      obtain ⟨g, hgH, hg⟩ := hsreach y y.2
      obtain ⟨g', hg'H, hg'⟩ := hsreach y' y'.2
      refine ⟨g' * g⁻¹, (hfix _).2 ((hH _).1 (H.mul_mem hg'H (H.inv_mem hgH))), Fin.ext ?_⟩
      rw [← M.act_of_lt _ y.2, act_mul, ← hg, act_inv_act, hyy']
      exact hg'
    · rintro ⟨g, hg0, hgy⟩
      apply Fin.ext
      show L y = L y'
      rw [← hL g ((hfix g).1 hg0) y y.2, M.act_of_lt g y.2, hgy]
  · -- σ preserves class sizes
    intro c
    have e : ∀ d : Fin r, Nat.card {y : Fin n // lab y = d} =
        countLt n fun y => Nat.beq (L y) d := fun d => by
      rw [← natCard_eq_countLt (fun y => (lab y : ℕ)) L (fun _ => rfl)]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Fin.ext_iff)
    rw [e, e]
    have := allLt_iff.1 hcards c c.2
    simpa [Nat.beq_eq, σ, mkPerm] using this
  · -- the pairs
    intro c
    have h := allLt_iff.1 hpairs c c.2
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    refine ⟨M.word (wa c), M.word (wb c), Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
    · show L _ = _
      rw [M.ρ_word hgf]; exact ha
    · show L _ = _
      rw [M.ρ_word hgf]; exact hb
    · show L _ = sg c
      rw [← M.word_append, M.ρ_word hgf, ev_append]; exact hab
  · -- goodness of the stabilizer
    simp only [kleinOK, Bool.and_eq_true] at hklein
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hu0, hv0⟩, hall⟩, hp1⟩, hp2⟩, hp3⟩, hu1⟩, hv1⟩, huv⟩ := hklein
    simp only [Nat.beq_eq, Nat.blt_eq] at hu0 hv0 hp1 hp2 hp3
    simp only [Bool.not_eq_true'] at hu1 hv1 huv
    replace hu1 := Nat.ne_of_beq_eq_false hu1
    replace hv1 := Nat.ne_of_beq_eq_false hv1
    replace huv := Nat.ne_of_beq_eq_false huv
    have hall' : ∀ x < n, (ev k gf u (ev k gf u x) = x ∧ ev k gf v (ev k gf v x) = x) ∧
        ev k gf u (ev k gf v x) = ev k gf v (ev k gf u x) := fun x hx => by
      simpa [kleinBody, Nat.beq_eq] using allLt_iff.1 hall x hx
    have hperm : ∀ a b : G, (∀ x < n, M.act a x = M.act b x) → a = b := by
      intro a b hab
      apply hinj
      ext x
      rw [← M.act_of_lt _ x.2, ← M.act_of_lt _ x.2, hab x x.2]
    have hw : ∀ w, ∀ x < n, M.act (M.word w) x = ev k gf w x := fun w x hx => M.act_word hgf w hx
    have hw2 : ∀ w w' : List (ℕ × Bool), ∀ x < n, M.act (M.word w * M.word w') x =
        ev k gf w (ev k gf w' x) := fun w w' x hx => by
      rw [act_mul, hw w' x hx, hw w _ (by rw [← hw w' x hx]; exact M.act_lt _ hx)]
    have hne : ∀ w : List (ℕ × Bool), ∀ p < n, ev k gf w p ≠ p → M.word w ≠ 1 := by
      intro w p hp h h1
      apply h
      rw [← hw w p hp, h1, act_one]
    refine Subgroup.isGood_of_commuting_involutions H
      ((hH _).2 (by rw [hw u x0 hx0]; exact hu0)) ((hH _).2 (by rw [hw v x0 hx0]; exact hv0))
      (hperm _ _ fun x hx => by rw [pow_two, hw2 _ _ x hx, act_one]; exact (hall' x hx).1.1)
      (hperm _ _ fun x hx => by rw [pow_two, hw2 _ _ x hx, act_one]; exact (hall' x hx).1.2)
      (hperm _ _ fun x hx => by rw [hw2 _ _ x hx, hw2 _ _ x hx]; exact (hall' x hx).2)
      (hne u p1 hp1 hu1) (hne v p2 hp2 hv1) ?_
    intro h
    apply huv
    rw [← hw u p3 hp3, ← hw v p3 hp3, h]

/-! ### The point stabilizer from an order bound

If `|G| ≤ N` and the words `hs` fixing `x0` generate a subgroup of order at least `N / n`
(certified by a stabilizer chain), then they generate the whole point stabilizer, so a labelling
invariant under `hs` is invariant under the stabilizer. -/

/-- The inverse of a word. -/
def winv (w : List (ℕ × Bool)) : List (ℕ × Bool) := w.reverse.map fun l => (l.1, !l.2)

theorem word_winv (w : List (ℕ × Bool)) : M.word (winv w) = (M.word w)⁻¹ := by
  induction w with
  | nil => simp [winv, word]
  | cons l w ih =>
    have e : winv (l :: w) = winv w ++ [(l.1, !l.2)] := by simp [winv]
    rw [e, word_append, ih, word, word, word, mul_inv_rev]
    simp only [mul_one]
    congr 1
    split_ifs <;> cases l.2 <;> simp

/-- Evaluation of a word in moves `E j b` (move `j`, or its inverse if `b = false`). The test
`Nat.beq y y` makes the kernel evaluate the intermediate point `y` first, which keeps its recursion
shallow. -/
def evc (E : ℕ → Bool → ℕ → ℕ) : List (ℕ × Bool) → ℕ → ℕ
  | [], x => x
  | l :: w, x => let y := evc E w x; cond (Nat.beq y y) (E l.1 l.2 y) (E l.1 l.2 y)

/-- Evaluation of the generators of a level of a stabilizer chain: the generators of level `0`
are the words `hs`; those of level `c :: st` are the words `c` in the generators of level `st`.
The nesting keeps the kernel's recursion shallow. -/
def evl (k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (hs : List (List (ℕ × Bool))) :
    List (List (List (ℕ × Bool))) → ℕ → Bool → ℕ → ℕ
  | [], j, b, x => ev k gf (cond b (hs.getD j []) (winv (hs.getD j []))) x
  | c :: st, j, b, x => evc (evl k gf hs st) (cond b (c.getD j []) (winv (c.getD j []))) x

/-- The generators of a level, as words in the generators of `G`. -/
def flat (hs : List (List (ℕ × Bool))) :
    List (List (List (ℕ × Bool))) → ℕ → Bool → List (ℕ × Bool)
  | [], j, b => cond b (hs.getD j []) (winv (hs.getD j []))
  | c :: st, j, b => (cond b (c.getD j []) (winv (c.getD j []))).flatMap fun l => flat hs st l.1 l.2

theorem evc_eq (f : ℕ → Bool → List (ℕ × Bool)) (w : List (ℕ × Bool)) (x : ℕ) :
    evc (fun j b x => ev k gf (f j b) x) w x = ev k gf (w.flatMap fun l => f l.1 l.2) x := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [evc, Bool.cond_self, ih, List.flatMap_cons, ev_append]

theorem evl_eq (hs : List (List (ℕ × Bool))) (st : List (List (List (ℕ × Bool)))) (j : ℕ) (b : Bool)
    (x : ℕ) : evl k gf hs st j b x = ev k gf (flat hs st j b) x := by
  induction st generalizing j b x with
  | nil => rfl
  | cons c st ih =>
    have e : evl k gf hs st = fun j b x => ev k gf (flat hs st j b) x := by
      funext j b x; exact ih j b x
    rw [evl, e, evc_eq, flat]

theorem word_flatMap (f : ℕ × Bool → List (ℕ × Bool)) (w : List (ℕ × Bool)) :
    M.word (w.flatMap f) = (w.map fun l => M.word (f l)).prod := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.flatMap_cons, word_append, ih, List.map_cons, List.prod_cons]

theorem word_flat_false (hs : List (List (ℕ × Bool))) (st : List (List (List (ℕ × Bool))))
    (j : ℕ) : M.word (flat hs st j false) = (M.word (flat hs st j true))⁻¹ := by
  induction st generalizing j with
  | nil => simp only [flat, cond_false, cond_true, word_winv]
  | cons c st ih =>
    have ih' : ∀ l : ℕ × Bool, M.word (flat hs st l.1 (!l.2)) = (M.word (flat hs st l.1 l.2))⁻¹ := by
      rintro ⟨i, b⟩
      cases b
      · simp only [Bool.not_false]; rw [ih i, inv_inv]
      · exact ih i
    simp only [flat, cond_false, cond_true, word_flatMap, winv, List.map_map]
    rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun l _ => ih' l

/-- The subgroup generated by the generators of a level. -/
def lsub (hs : List (List (ℕ × Bool))) (st : List (List (List (ℕ × Bool)))) : Subgroup G :=
  Subgroup.closure (Set.range fun j => M.word (flat hs st j true))

theorem word_flat_mem (hs : List (List (ℕ × Bool))) (st : List (List (List (ℕ × Bool))))
    (j : ℕ) (b : Bool) : M.word (flat hs st j b) ∈ M.lsub hs st := by
  have h : M.word (flat hs st j true) ∈ M.lsub hs st := Subgroup.subset_closure ⟨j, rfl⟩
  cases b
  · rw [word_flat_false]; exact (M.lsub hs st).inv_mem h
  · exact h

theorem lsub_cons_le (hs : List (List (ℕ × Bool))) (c : List (List (ℕ × Bool)))
    (st : List (List (List (ℕ × Bool)))) : M.lsub hs (c :: st) ≤ M.lsub hs st := by
  rw [lsub, Subgroup.closure_le]
  rintro g ⟨j, rfl⟩
  simp only [flat, cond_true, word_flatMap, SetLike.mem_coe]
  exact Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact M.word_flat_mem hs st l.1 l.2)

/-- One level of a stabilizer chain: the orbit of the base point `b` contains the points
marked by `P` (certified by a spanning tree), and the next level's generators are given as words
`codes` in the current ones, all fixing `b`. -/
structure Lvl where
  codes : List (List (ℕ × Bool))
  b : ℕ
  P : ℕ → Bool
  par : ℕ → ℕ
  mv : ℕ → ℕ
  dep : ℕ → ℕ

end Model

/-- Spanning-forest certificate with moves given by an evaluator `E`. -/
def reachOKE (n : ℕ) (E : ℕ → ℕ → ℕ) (rt par mv dep : ℕ → ℕ) : Bool :=
  allLt n fun y => Nat.blt (rt y) n && (Nat.beq (rt y) y || (Nat.blt (par y) n &&
    Nat.blt (dep (par y)) (dep y) && Nat.beq (rt (par y)) (rt y) && Nat.beq (E (mv y) (par y)) y))

/-- The check of a stabilizer chain, level by level from the bottom (`st` describes the current
level's generators). -/
def chainOK (n k : ℕ) (gf : ℕ → Bool → ℕ → ℕ) (hs : List (List (ℕ × Bool))) :
    List (List (List (ℕ × Bool))) → List Model.Lvl → Bool
  | _, [] => true
  | st, L :: Ls => Nat.blt L.b n && L.P L.b &&
      reachOKE n (fun m y => Model.evl k gf hs st m true y) (fun y => cond (L.P y) L.b y)
        L.par L.mv L.dep &&
      allLt L.codes.length (fun j => Nat.beq (Model.evl k gf hs (L.codes :: st) j true L.b) L.b) &&
      chainOK n k gf hs (L.codes :: st) Ls

/-- The lower bound for the order given by a stabilizer chain. -/
def chainBound (n : ℕ) : List Model.Lvl → ℕ
  | [] => 1
  | L :: Ls => countLt n L.P * chainBound n Ls

namespace Model

variable {n k : ℕ} {gf : ℕ → Bool → ℕ → ℕ} {G : Type*} [Group G] (M : Model n k gf G)

theorem countLt_mul_card_le [Finite G] (A B : Subgroup G) (hBA : B ≤ A) {b : ℕ}
    (hB : ∀ g ∈ B, M.act g b = b) (P : ℕ → Bool)
    (hP : ∀ y < n, P y = true → ∃ g ∈ A, M.act g b = y) :
    countLt n P * Nat.card B ≤ Nat.card A := by
  classical
  rw [countLt_eq]
  set pts := (Finset.range n).filter fun i => P i = true
  have hg : ∀ y : pts, ∃ g ∈ A, M.act g b = y := fun y => by
    have hy := Finset.mem_filter.1 y.2
    exact hP y (Finset.mem_range.1 hy.1) hy.2
  choose g hgA hgb using hg
  let f : pts × B → A := fun p => ⟨g p.1 * p.2, A.mul_mem (hgA _) (hBA p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨y, h⟩ ⟨y', h'⟩ hyy
    have e : g y * h = g y' * h' := congrArg Subtype.val hyy
    have hy : (y : ℕ) = y' := by
      have := congrArg (fun x => M.act x b) e
      simp only [act_mul, hB _ h.2, hB _ h'.2, hgb] at this
      exact this
    have hy' : y = y' := Subtype.ext hy
    subst hy'
    have : h = h' := Subtype.ext (mul_left_cancel e)
    rw [this]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := pts), Fintype.card_coe] at this

theorem reachE (K : Subgroup G) (E : ℕ → ℕ → ℕ) (elt : ℕ → G)
    (hE : ∀ m, ∀ y < n, E m y = M.act (elt m) y) (hK : ∀ m, elt m ∈ K) (rt par mv dep : ℕ → ℕ)
    (h : reachOKE n E rt par mv dep = true) : ∀ y < n, ∃ g ∈ K, M.act g (rt y) = y := by
  have key : ∀ d, ∀ y < n, dep y = d → ∃ g ∈ K, M.act g (rt y) = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy hd
      have hc := allLt_iff.1 h y hy
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨-, hc | ⟨⟨⟨hp, hdep⟩, hrt⟩, hev⟩⟩ := hc
      · exact ⟨1, K.one_mem, by rw [act_one, hc]⟩
      · obtain ⟨g, hgK, hg⟩ := ih _ (hd ▸ hdep) _ hp rfl
        refine ⟨elt (mv y) * g, K.mul_mem (hK _) hgK, ?_⟩
        rw [act_mul, ← hrt, hg, ← hE _ _ hp, hev]
  exact fun y hy => key _ y hy rfl

theorem card_ge_chainBound [Finite G] (hgf : gensOK n k gf = true) (hs : List (List (ℕ × Bool))) :
    ∀ (Ls : List Lvl) (st : List (List (List (ℕ × Bool)))), chainOK n k gf hs st Ls = true →
      chainBound n Ls ≤ Nat.card (M.lsub hs st) := by
  intro Ls
  induction Ls with
  | nil => intro st _; exact Nat.card_pos
  | cons L Ls ih =>
    intro st h
    simp only [chainOK, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨hb, hPb⟩, hreach⟩, hcodes⟩, hrest⟩ := h
    have hfix : ∀ g ∈ M.lsub hs (L.codes :: st), M.act g L.b = L.b := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        rw [M.act_word hgf _ hb, ← evl_eq]
        by_cases hj : j < L.codes.length
        · simpa [Nat.beq_eq] using allLt_iff.1 hcodes j hj
        · rw [evl, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
          rfl
      | one => exact M.act_one _
      | mul x y _ _ hx hy => rw [act_mul, hy, hx]
      | inv x _ hx =>
        conv_lhs => rw [← hx]
        exact M.act_inv_act x _
    have hreach' := M.reachE (M.lsub hs st) _ (fun m => M.word (flat hs st m true))
      (fun m y hy => by rw [M.act_word hgf _ hy, evl_eq]) (fun m => M.word_flat_mem hs st m true)
      _ _ _ _ hreach
    have key := M.countLt_mul_card_le (M.lsub hs st) (M.lsub hs (L.codes :: st))
      (M.lsub_cons_le hs _ st) hfix L.P (by
        intro y hy hPy
        obtain ⟨g, hg, hgy⟩ := hreach' y hy
        simp only [hPy, cond_true] at hgy
        exact ⟨g, hg, hgy⟩)
    calc chainBound n (L :: Ls) = countLt n L.P * chainBound n Ls := rfl
      _ ≤ countLt n L.P * Nat.card (M.lsub hs (L.codes :: st)) :=
          Nat.mul_le_mul_left _ (ih _ hrest)
      _ ≤ _ := key

/-- **Invariance of a labelling from an order bound.** If `|G| ≤ N`, the words `hs` fix `x0`, a
stabilizer chain shows that they generate a subgroup of order at least `N / n`, and `L` is
invariant under `hs`, then `L` is invariant under the stabilizer of `x0`. -/
theorem invL_of_order (hgf : gensOK n k gf = true) (hinj : Function.Injective M.ρ)
    (x0 : ℕ) (hx0 : x0 < n) (tpar tmv tdep : ℕ → ℕ)
    (htr : reachOK n k gf ((List.range k).map fun i => [(i, true)]) (fun _ => x0) tpar tmv tdep
      = true)
    (hs : List (List (ℕ × Bool))) (hhs : (hs.all fun w => Nat.beq (ev k gf w x0) x0) = true)
    (N : ℕ) (hN : Nat.card G ≤ N) (Ls : List Lvl) (hch : chainOK n k gf hs [] Ls = true)
    (hbound : N ≤ chainBound n Ls * n) (L : ℕ → ℕ)
    (hlab : (hs.all fun w => allLt n fun z => Nat.beq (L (ev k gf w z)) (L z)) = true) :
    M.InvL x0 L := by
  classical
  haveI : Finite G := Finite.of_injective _ hinj
  let H : Subgroup G := (MulAction.stabilizer (Perm (Fin n)) (⟨x0, hx0⟩ : Fin n)).comap M.ρ
  have hH : ∀ g, g ∈ H ↔ M.act g x0 = x0 := fun g => by
    rw [M.act_of_lt g hx0]
    simp [H, MulAction.mem_stabilizer_iff, Perm.smul_def, Fin.ext_iff]
  have hgetD : ∀ j, hs.getD j [] ∈ hs ∨ hs.getD j [] = [] := fun j => by
    rw [List.getD_eq_getElem?_getD]
    cases hm : hs[j]? with
    | none => right; rfl
    | some w => left; exact List.mem_of_getElem? hm
  have hKH : M.lsub hs [] ≤ H := by
    rw [lsub, Subgroup.closure_le]
    rintro g ⟨j, rfl⟩
    rw [SetLike.mem_coe, hH, M.act_word hgf _ hx0]
    simp only [flat, cond_true]
    rcases hgetD j with hw | hw
    · simpa using List.all_eq_true.1 hhs _ hw
    · rw [hw]; rfl
  have htreach := M.reach hgf ⊤ _ (fun _ _ => Subgroup.mem_top _) _ tpar tmv tdep htr
  have h1 := M.countLt_mul_card_le ⊤ H le_top (b := x0) (fun g hg => (hH g).1 hg) (fun _ => true)
    (fun y hy _ => htreach y hy)
  have hn : countLt n (fun _ => true) = n := by
    rw [countLt_eq, Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_range]
  rw [hn, Nat.card_congr (Equiv.subtypeUnivEquiv Subgroup.mem_top)] at h1
  have h2 := M.card_ge_chainBound hgf hs Ls [] hch
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hx0
  have hcard : Nat.card H ≤ Nat.card (M.lsub hs []) := by
    have : n * Nat.card H ≤ n * Nat.card (M.lsub hs []) := by
      calc n * Nat.card H ≤ Nat.card G := h1
        _ ≤ N := hN
        _ ≤ chainBound n Ls * n := hbound
        _ ≤ Nat.card (M.lsub hs []) * n := Nat.mul_le_mul_right _ h2
        _ = n * Nat.card (M.lsub hs []) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hnpos
  have hKeq : M.lsub hs [] = H := Subgroup.eq_of_le_of_card_ge hKH hcard
  have hlab' : ∀ j, ∀ z < n, L (M.act (M.word (flat hs [] j true)) z) = L z := by
    intro j z hz
    simp only [flat, cond_true]
    rcases hgetD j with hw | hw
    · have := allLt_iff.1 (List.all_eq_true.1 hlab _ hw) z hz
      rw [M.act_word hgf _ hz]
      simpa using this
    · rw [hw, word, act_one]
  intro g hg
  have hgK : g ∈ M.lsub hs [] := hKeq ▸ (hH g).2 hg
  clear hg
  induction hgK using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hlab' j
  | one => intro z _; rw [act_one]
  | mul x y _ _ hx hy =>
    intro z hz
    rw [act_mul, hx _ (M.act_lt _ hz), hy z hz]
  | inv x _ hx =>
    intro z hz
    have := hx _ (M.act_lt x⁻¹ hz)
    rw [act_act_inv] at this
    exact this.symm

end Model

/-- A model is faithful as soon as `G` is simple and some generator moves some point. -/
theorem Model.injective_of_simple {G : Type*} [Group G] [IsSimpleGroup G] {n k : ℕ}
    {gf : ℕ → Bool → ℕ → ℕ} (M : Model n k gf G) {i : ℕ} (hi : i < k) {p : ℕ} (hp : p < n)
    (h : Nat.beq (gf i true p) p = false) : Function.Injective M.ρ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := M.ρ.ker) with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff _).1 hk
  · exfalso
    have hmem : M.gen i ∈ M.ρ.ker := hk ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have := M.ρ_gen i hi ⟨p, hp⟩
    rw [hmem, Perm.one_apply] at this
    exact Nat.ne_of_beq_eq_false h this.symm

/-! ### Models of presented groups -/

section Presentation

variable (P : TauCeti.GroupPresentation) {n k : ℕ} {gf : ℕ → Bool → ℕ → ℕ}

/-- The permutation of the `i`-th generator table. -/
def genPerm (hgf : gensOK n k gf = true) (i : ℕ) (hi : i < k) : Perm (Fin n) :=
  mkPerm n (gf i true) (gf i false) (allLt_iff.1 hgf i hi)

theorem prod_genPerm_apply (hgf : gensOK n k gf = true) {c : ℕ} (hc : c = k)
    (w : List (Fin c × Bool)) (x : Fin n) :
    ((w.map fun l => cond l.2 (genPerm hgf l.1.val (hc ▸ l.1.2))
      (genPerm hgf l.1.val (hc ▸ l.1.2))⁻¹).prod x).val =
      ev k gf (w.map fun l => (l.1.val, l.2)) x.val := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    have hl : l.1.val < k := hc ▸ l.1.2
    rw [List.map_cons, List.prod_cons, Perm.mul_apply, List.map_cons, ev,
      show Nat.blt l.1.val k = true from Nat.blt_eq.mpr hl, cond_true, ← ih]
    cases l.2 <;> rfl

/-- The model of a presented group given by generator tables satisfying its relators. -/
def presModel (hk : P.generatorCount = k) (hgf : gensOK n k gf = true)
    (hrel : (P.relatorLetters.all fun v => allLt n fun x => Nat.beq (ev k gf v x) x) = true) :
    Model n k gf P.Group where
  ρ := PresentedGroup.toGroup (f := fun i => genPerm hgf i.val (hk ▸ i.2)) (by
    intro r hr
    rw [TauCeti.GroupPresentation.mem_relatorSet_iff] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    rw [← TauCeti.Relator.toWord_toFreeGroup, FreeGroup.lift_mk]
    have hmem : t.toWord.map (fun l => (l.1.val, l.2)) ∈ P.relatorLetters := by
      rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
        List.map_map]
      exact List.mem_map.2 ⟨t, ht, rfl⟩
    have hv := allLt_iff.1 (List.all_eq_true.1 hrel _ hmem)
    ext x
    rw [prod_genPerm_apply hgf hk, Perm.one_apply]
    simpa [Nat.beq_eq] using hv x x.2)
  gen i := if h : i < P.generatorCount then PresentedGroup.of ⟨i, h⟩ else 1
  closure_eq := by
    rw [← PresentedGroup.closure_range_of P.relatorSet]
    congr 1
    ext g
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < P.generatorCount := hk ▸ hi
      exact ⟨⟨i, hi'⟩, by simp [hi']⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, hk ▸ i.2, by simp⟩
  ρ_gen i hi x := by
    have hi' : i < P.generatorCount := hk ▸ hi
    simp only [hi', dite_true]
    rw [PresentedGroup.toGroup.of]
    rfl

end Presentation

end CFSGOutside.HallPaige.OrbitCert
