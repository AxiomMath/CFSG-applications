import Mathlib
import CFSGOutside.Corpus.SteinerTripleIso
import CFSGOutside.Corpus.IsSteinerTripleHexads
import CFSGOutside.Corpus.IsSteinerTripleCardInter
import CFSGOutside.Corpus.CardHexads
import CFSGOutside.Corpus.CardHexadAut

/-!
# The shortened Golay code `G22`

The coding-theory input of the Witt designs, after V. Pless, N. J. A. Sloane, *On the
classification and enumeration of self-dual codes*, J. Combin. Theory Ser. A 18 (1975) 313–335,
Theorem 7.1 / Table I. `G22`, the code spanned by the hexads of the corpus model of S(3,6,22), is
self-dual of dimension 11 with minimum weight 6 (`G22_isSelfDual`, `G22_minWeight`; a rank
certificate shows that the hexads span 11 dimensions). Every self-dual binary [22,11,6] code has the
weight distribution of `G22` (`weight_distribution`, from the binomial moments of an orthogonal
array of strength 5).
-/

/- A corpus-visible instance `AddCommGroup α` from `IsSimpleAddGroup`/`IsNilpotent` derails instance
search for `ZMod 2`-modules; the corpus disables it locally in the same way. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace CFSGOutside.PlessSloaneG22


open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}]

theorem card_of_mem_hexads {B : Finset (Fin 22)} (hB : B ∈ hexads) : B.card = 6 :=
  IsSteinerTriple.card_block IsSteinerTripleHexads.isSteinerTriple_hexads hB
open scoped Matrix

/-- Binary words of length 22. -/
abbrev Word := Fin 22 → ZMod 2

/-- The support of a word. -/
def supp (c : Word) : Finset (Fin 22) := Finset.univ.filter fun i => c i ≠ 0

/-- The Hamming weight of a word. -/
def wt (c : Word) : ℕ := (supp c).card

/-- The indicator word of a set of coordinates. -/
def ind (B : Finset (Fin 22)) : Word := fun i => if i ∈ B then 1 else 0

/-- The all-one word. -/
def one22 : Word := fun _ => 1

/-- A binary linear code of length 22 is self-dual if it equals its dual
`C⊥ = {x | x · c = 0 for all c ∈ C}`. -/
def IsSelfDual (C : Submodule (ZMod 2) Word) : Prop :=
  ∀ x : Word, x ∈ C ↔ ∀ c ∈ C, c ⬝ᵥ x = 0

/-- Every nonzero word of `C` has weight at least `d`. -/
def MinWeightAtLeast (C : Submodule (ZMod 2) Word) (d : ℕ) : Prop :=
  ∀ c ∈ C, c ≠ 0 → d ≤ wt c

/-- The shortened Golay code `G22`: the span of the hexads of the model S(3,6,22). -/
def G22 : Submodule (ZMod 2) Word :=
  Submodule.span (ZMod 2) (ind '' (hexads : Set (Finset (Fin 22))))

/-! ### Words over `ZMod 2` -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem mem_supp {c : Word} {i : Fin 22} : i ∈ supp c ↔ c i ≠ 0 := by simp [supp]

theorem mem_supp_iff_eq_one {c : Word} {i : Fin 22} : i ∈ supp c ↔ c i = 1 := by
  rw [mem_supp]
  rcases zmod2_cases (c i) with h | h <;> simp [h]

theorem ind_supp (c : Word) : ind (supp c) = c := by
  funext i
  simp only [ind, mem_supp]
  rcases zmod2_cases (c i) with h | h <;> simp [h]

theorem supp_ind (B : Finset (Fin 22)) : supp (ind B) = B := by
  ext i
  simp [supp, ind]

theorem wt_eq_sum (c : Word) : wt c = ∑ i, if c i ≠ 0 then 1 else 0 := by
  rw [wt, supp, Finset.card_filter]

theorem wt_eq_zero_iff {c : Word} : wt c = 0 ↔ c = 0 := by
  rw [wt, Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    by_contra hi
    have : i ∈ supp c := mem_supp.2 hi
    rw [h] at this
    simp at this
  · rintro rfl
    simp [supp]

theorem wt_le (c : Word) : wt c ≤ 22 := by
  have := Finset.card_le_univ (supp c)
  simpa [wt] using this

theorem dot_eq_card (c d : Word) : c ⬝ᵥ d = ((supp c ∩ supp d).card : ZMod 2) := by
  have hp : ∀ a b : ZMod 2, a * b = if a ≠ 0 ∧ b ≠ 0 then 1 else 0 := by decide
  rw [dotProduct, Finset.sum_congr rfl fun i _ => hp (c i) (d i), Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext i
  simp [supp]

theorem dot_self (c : Word) : c ⬝ᵥ c = (wt c : ZMod 2) := by
  rw [dot_eq_card, Finset.inter_self, wt]

theorem dot_one22 (c : Word) : c ⬝ᵥ one22 = (wt c : ZMod 2) := by
  rw [dot_eq_card]
  congr 2
  ext i
  simp [supp, one22]

theorem wt_add_add (c d : Word) : wt (c + d) + 2 * (supp c ∩ supp d).card = wt c + wt d := by
  have hp : ∀ a b : ZMod 2, ((if a + b ≠ 0 then 1 else 0) + 2 * (if a ≠ 0 ∧ b ≠ 0 then 1 else 0)
      : ℕ) = (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by decide
  have hi : (supp c ∩ supp d).card = ∑ i, if c i ≠ 0 ∧ d i ≠ 0 then 1 else 0 := by
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp [supp]
  rw [hi, wt_eq_sum, wt_eq_sum, wt_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hp (c i) (d i)

theorem wt_add_one22 (c : Word) : wt (c + one22) + wt c = 22 := by
  have hp : ∀ a : ZMod 2, ((if a + 1 ≠ 0 then 1 else 0) + (if a ≠ 0 then 1 else 0) : ℕ) = 1 := by
    decide
  rw [wt_eq_sum, wt_eq_sum, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun i _ => hp (c i)).trans ?_
  simp

/-! ### Self-dual codes -/

/-- The standard dot product as a bilinear form. -/
noncomputable def dotForm : LinearMap.BilinForm (ZMod 2) Word := Matrix.toBilin' 1

theorem dotForm_apply (x y : Word) : dotForm x y = x ⬝ᵥ y := by
  rw [dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec]

theorem dotForm_nondegenerate : dotForm.Nondegenerate :=
  Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))

theorem finrank_word : Module.finrank (ZMod 2) Word = 22 := by simp

noncomputable instance (C : Submodule (ZMod 2) Word) : Fintype C := Fintype.ofFinite C

theorem card_submodule (C : Submodule (ZMod 2) Word) :
    Fintype.card C = 2 ^ Module.finrank (ZMod 2) C := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := C), ZMod.card]

/-- Restriction of codewords to a set `S` of coordinates. -/
def restr (C : Submodule (ZMod 2) Word) (S : Finset (Fin 22)) : C →ₗ[ZMod 2] (S → ZMod 2) where
  toFun c s := (c : Word) s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_apply (C : Submodule (ZMod 2) Word) (S : Finset (Fin 22)) (c : C) (s : S) :
    restr C S c s = (c : Word) s := rfl

section code

variable {C : Submodule (ZMod 2) Word} (hC : IsSelfDual C)
include hC

theorem dot_eq_zero {c d : Word} (hc : c ∈ C) (hd : d ∈ C) : c ⬝ᵥ d = 0 := (hC d).1 hd c hc

theorem orthogonal_eq : dotForm.orthogonal C = C := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, hC x]
  simp only [dotForm_apply]

/-- A self-dual code of length 22 has dimension 11. -/
theorem finrank_eq : Module.finrank (ZMod 2) C = 11 := by
  have h := LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate C
  rw [orthogonal_eq hC, finrank_word] at h
  have := Submodule.finrank_le C
  rw [finrank_word] at this
  omega

theorem card_code : Fintype.card C = 2 ^ 11 := by
  rw [card_submodule, finrank_eq hC]

theorem even_wt {c : Word} (hc : c ∈ C) : Even (wt c) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← dot_self]
  exact dot_eq_zero hC hc hc

theorem one22_mem : one22 ∈ C := (hC one22).2 fun c hc => by
  rw [dot_one22, ZMod.natCast_eq_zero_iff_even]
  exact even_wt hC hc

variable (hd : MinWeightAtLeast C 6)
include hd

/-- The possible weights of a self-dual [22,11,6] code. -/
theorem wt_mem {c : Word} (hc : c ∈ C) :
    wt c ∈ ({0, 6, 8, 10, 12, 14, 16, 22} : Finset ℕ) := by
  have he := even_wt hC hc
  have hle := wt_le c
  by_cases h0 : c = 0
  · subst h0
    simp [wt_eq_zero_iff.2 rfl]
  have h6 := hd c hc h0
  by_cases h16 : wt c ≤ 16
  · obtain ⟨k, hk⟩ := he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have h1 := wt_add_one22 c
    have hm : c + one22 ∈ C := C.add_mem hc (one22_mem hC)
    have h0' : c + one22 = 0 := by
      by_contra hne
      have := hd _ hm hne
      omega
    rw [h0', wt_eq_zero_iff.2 rfl] at h1
    simp [show wt c = 22 by omega]

/-- The dual distance is at least 6: restriction to at most five coordinates is onto. -/
theorem restr_surjective {S : Finset (Fin 22)} (hS : S.card ≤ 5) :
    Function.Surjective (restr C S) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let u : Word := fun i => if h : i ∈ S then f (Pi.single ⟨i, h⟩ 1) else 0
  have hu : ∀ s : S, u s = f (fun j => if s = j then 1 else 0) := by
    intro s
    simp only [u, dif_pos s.2]
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]
  have hdot : ∀ c ∈ C, c ⬝ᵥ u = 0 := by
    intro c hc
    have h1 : f (restr C S ⟨c, hc⟩) = 0 := hf (LinearMap.mem_range_self _ _)
    rw [LinearMap.pi_apply_eq_sum_univ f] at h1
    rw [← h1, dotProduct, ← Finset.sum_subset (Finset.subset_univ S) (f := fun i => c i * u i)
      (fun i _ hi => by simp [u, hi]), ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hu s, restr_apply, smul_eq_mul]
  have huC : u ∈ C := (hC u).2 hdot
  have hu0 : u ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← hu s, h0, Pi.zero_apply, smul_zero]
  have hsub : supp u ⊆ S := by
    intro i hi
    by_contra his
    rw [mem_supp] at hi
    exact hi (by simp [u, his])
  have := hd u huC hu0
  have := Finset.card_le_card hsub
  rw [← wt] at this
  omega

/-- Strength-5 orthogonal array: every set of at most five coordinates is covered by exactly
`2 ^ (11 - |S|)` codewords. -/
theorem card_cover {S : Finset (Fin 22)} (hS : S.card ≤ 5) :
    (Finset.univ.filter fun c : C => S ⊆ supp c).card = 2 ^ (11 - S.card) := by
  have hsurj := restr_surjective hC hd hS
  have e : (Finset.univ.filter fun c : C => S ⊆ supp c) =
      Finset.univ.filter fun c : C => restr C S c = fun _ => 1 := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      funext s
      exact mem_supp_iff_eq_one.1 (h s.2)
    · intro h i hi
      exact mem_supp_iff_eq_one.2 (congrFun h ⟨i, hi⟩)
  rw [e]
  have htot := Finset.card_eq_sum_card_fiberwise (f := restr C S) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.card_univ, card_code hC,
    Finset.sum_congr rfl fun y _ => AddMonoidHom.card_fiber_eq_of_mem_range (restr C S)
      (hsurj y) (hsurj fun _ => 1), Finset.sum_const, Finset.card_univ, smul_eq_mul] at htot
  have hcard : Fintype.card (S → ZMod 2) = 2 ^ S.card := by simp
  rw [hcard] at htot
  have h2 : (2 : ℕ) ^ 11 = 2 ^ S.card * 2 ^ (11 - S.card) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2] at htot
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) htot).symm

/-- Binomial moments of the weight distribution. -/
theorem moment {j : ℕ} (hj : j ≤ 5) :
    ∑ c : C, (wt c).choose j = (22).choose j * 2 ^ (11 - j) := by
  have h1 : ∀ c : C, (wt c).choose j =
      ∑ T ∈ Finset.univ.powersetCard j, if T ⊆ supp c then 1 else 0 := by
    intro c
    rw [← Finset.card_filter, wt, ← Finset.card_powersetCard]
    congr 1
    ext T
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    exact and_comm
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun T hT => ?_, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.mem_powersetCard] at hT
  rw [← Finset.card_filter, card_cover hC hd (hT.2 ▸ hj), hT.2]

omit hC hd in
theorem sum_eight (f : ℕ → ℕ) : ∑ i ∈ ({0, 6, 8, 10, 12, 14, 16, 22} : Finset ℕ), f i =
    f 0 + (f 6 + (f 8 + (f 10 + (f 12 + (f 14 + (f 16 + f 22)))))) := by
  simp

/-- The number of codewords of weight `i`. -/
noncomputable def A (C : Submodule (ZMod 2) Word) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun c : C => wt c = i).card

theorem sum_wt (g : ℕ → ℕ) :
    ∑ c : C, g (wt c) = ∑ i ∈ ({0, 6, 8, 10, 12, 14, 16, 22} : Finset ℕ), A C i * g i := by
  rw [← Finset.sum_fiberwise_of_maps_to' (g := fun c : C => wt c)
    (fun c _ => wt_mem hC hd c.2) g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, smul_eq_mul, A]

omit hd in
theorem A_zero : A C 0 = 1 := by
  rw [A, Finset.card_eq_one]
  refine ⟨⟨0, C.zero_mem⟩, ?_⟩
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    wt_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

omit hC hd in
theorem wt_one22 : wt one22 = 22 := by
  rw [wt, show supp one22 = Finset.univ by ext i; simp [supp, one22]]
  rfl

omit hd in
theorem A_22 : A C 22 = 1 := by
  rw [A, Finset.card_eq_one]
  refine ⟨⟨one22, one22_mem hC⟩, ?_⟩
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have h1 := wt_add_one22 (c : Word)
    rw [h] at h1
    have h0 : (c : Word) + one22 = 0 := wt_eq_zero_iff.1 (by omega)
    apply Subtype.ext
    funext i
    have hp : ∀ a : ZMod 2, a + 1 = 0 → a = 1 := by decide
    exact hp _ (congrFun h0 i)
  · rintro rfl
    exact wt_one22

/-- The weight distribution of a self-dual [22,11,6] code: 1, 77, 330, 616, 616, 330, 77, 1. -/
theorem weight_distribution :
    A C 6 = 77 ∧ A C 8 = 330 ∧ A C 10 = 616 ∧ A C 12 = 616 ∧ A C 14 = 330 ∧ A C 16 = 77 := by
  have e : ∀ j ≤ 5, ∑ i ∈ ({0, 6, 8, 10, 12, 14, 16, 22} : Finset ℕ), A C i * i.choose j =
      (22).choose j * 2 ^ (11 - j) := fun j hj => by
    rw [← sum_wt hC hd (fun i => i.choose j)]
    exact moment hC hd hj
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e5 := e 5 (by norm_num)
  simp only [sum_eight, A_zero hC, A_22 hC,
    show Nat.choose 0 0 = 1 from rfl,
      show Nat.choose 0 1 = 0 from rfl,
      show Nat.choose 0 2 = 0 from rfl,
      show Nat.choose 0 3 = 0 from rfl,
      show Nat.choose 0 4 = 0 from rfl,
      show Nat.choose 0 5 = 0 from rfl,
      show Nat.choose 6 0 = 1 from rfl,
      show Nat.choose 6 1 = 6 from rfl,
      show Nat.choose 6 2 = 15 from rfl,
      show Nat.choose 6 3 = 20 from rfl,
      show Nat.choose 6 4 = 15 from rfl,
      show Nat.choose 6 5 = 6 from rfl,
      show Nat.choose 8 0 = 1 from rfl,
      show Nat.choose 8 1 = 8 from rfl,
      show Nat.choose 8 2 = 28 from rfl,
      show Nat.choose 8 3 = 56 from rfl,
      show Nat.choose 8 4 = 70 from rfl,
      show Nat.choose 8 5 = 56 from rfl,
      show Nat.choose 10 0 = 1 from rfl,
      show Nat.choose 10 1 = 10 from rfl,
      show Nat.choose 10 2 = 45 from rfl,
      show Nat.choose 10 3 = 120 from rfl,
      show Nat.choose 10 4 = 210 from rfl,
      show Nat.choose 10 5 = 252 from rfl,
      show Nat.choose 12 0 = 1 from rfl,
      show Nat.choose 12 1 = 12 from rfl,
      show Nat.choose 12 2 = 66 from rfl,
      show Nat.choose 12 3 = 220 from rfl,
      show Nat.choose 12 4 = 495 from rfl,
      show Nat.choose 12 5 = 792 from rfl,
      show Nat.choose 14 0 = 1 from rfl,
      show Nat.choose 14 1 = 14 from rfl,
      show Nat.choose 14 2 = 91 from rfl,
      show Nat.choose 14 3 = 364 from rfl,
      show Nat.choose 14 4 = 1001 from rfl,
      show Nat.choose 14 5 = 2002 from rfl,
      show Nat.choose 16 0 = 1 from rfl,
      show Nat.choose 16 1 = 16 from rfl,
      show Nat.choose 16 2 = 120 from rfl,
      show Nat.choose 16 3 = 560 from rfl,
      show Nat.choose 16 4 = 1820 from rfl,
      show Nat.choose 16 5 = 4368 from rfl,
      show Nat.choose 22 0 = 1 from rfl,
      show Nat.choose 22 1 = 22 from rfl,
      show Nat.choose 22 2 = 231 from rfl,
      show Nat.choose 22 3 = 1540 from rfl,
      show Nat.choose 22 4 = 7315 from rfl,
      show Nat.choose 22 5 = 26334 from rfl] at e0 e1 e2 e3 e4 e5
  norm_num at e0 e1 e2 e3 e4 e5
  omega

end code

theorem three_le_card' {s : Finset (Fin 22)} {a b c : Fin 22} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset (Fin 22)) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have h3 := Finset.card_le_card hsub
  rwa [Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩] at h3

/-! ### Steiner systems from counting -/

/-! ### The hexads of a self-dual [22,11,6] code -/

/-- The supports of the weight-6 words of `C`. -/
noncomputable def wordHexads (C : Submodule (ZMod 2) Word) : Finset (Finset (Fin 22)) :=
  (Finset.univ.filter fun c : C => wt c = 6).image fun c : C => supp (c : Word)

theorem add_eq_zero_iff_eq {c d : Word} : c + d = 0 ↔ c = d := by
  have hp : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  constructor
  · intro h; funext i; exact (hp _ _).1 (congrFun h i)
  · rintro rfl; funext i; exact (hp _ _).2 rfl

section code2

variable {C : Submodule (ZMod 2) Word} (hC : IsSelfDual C) (hd : MinWeightAtLeast C 6)
include hC hd

end code2

/-! ### Rank certificate: the hexads span an 11-dimensional code -/

/-- Eleven hexads of the model, with pivot coordinates making their incidence matrix upper
unitriangular. -/
def certHexads : Fin 11 → Finset (Fin 22) := ![{2, 9, 12, 15, 16, 21}, {0, 1, 4, 5, 13, 18}, {1, 5, 8, 11, 17, 20}, {3, 6, 8, 11, 12, 21}, {2, 6, 10, 12, 17, 20}, {0, 1, 2, 9, 17, 19}, {0, 4, 7, 9, 14, 15}, {7, 8, 12, 15, 17, 19}, {8, 10, 14, 15, 20, 21}, {0, 8, 9, 12, 18, 20}, {3, 7, 9, 17, 20, 21}]

def certCols : Fin 11 → Fin 22 := ![16, 13, 5, 11, 6, 1, 4, 19, 15, 18, 21]

theorem certHexads_mem (i : Fin 11) : certHexads i ∈ hexads := by
  rw [mem_hexads]
  revert i
  decide +kernel

/-- The incidence matrix of the certificate hexads on the pivot coordinates. -/
def certMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  Matrix.of fun i k => ind (certHexads i) (certCols k)

theorem certMatrix_upperTriangular : certMatrix.BlockTriangular id := by
  have h : ∀ p : Fin 11 × Fin 11, p.2 < p.1 → certMatrix p.1 p.2 = 0 := by decide +kernel
  exact fun i k hik => h (i, k) hik

theorem certMatrix_diag (i : Fin 11) : certMatrix i i = 1 := by
  revert i
  decide +kernel

theorem certMatrix_isUnit : IsUnit certMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular certMatrix_upperTriangular,
    Finset.prod_eq_one fun i _ => certMatrix_diag i]
  exact isUnit_one

theorem eleven_le_finrank_G22 : 11 ≤ Module.finrank (ZMod 2) G22 := by
  let v : Fin 11 → Word := fun i => ind (certHexads i)
  have hv : LinearIndependent (ZMod 2) v := by
    refine LinearIndependent.of_comp (LinearMap.funLeft (ZMod 2) (ZMod 2) certCols) ?_
    exact Matrix.linearIndependent_rows_of_isUnit certMatrix_isUnit
  let w : Fin 11 → G22 := fun i => ⟨v i, Submodule.subset_span ⟨certHexads i, certHexads_mem i, rfl⟩⟩
  have hw : LinearIndependent (ZMod 2) w := LinearIndependent.of_comp G22.subtype hv
  simpa using hw.fintype_card_le_finrank

/-! ### Uniqueness -/

/-! ### Existence: `G22` is self-dual with minimum weight 6 -/

theorem dot_ind_hexads {B B' : Finset (Fin 22)} (hB : B ∈ hexads) (hB' : B' ∈ hexads) :
    ind B ⬝ᵥ ind B' = 0 := by
  rw [dot_eq_card, supp_ind, supp_ind, ZMod.natCast_eq_zero_iff_even]
  by_cases h : B = B'
  · rw [h, Finset.inter_self, card_of_mem_hexads hB']
    decide
  · rcases IsSteinerTripleCardInter.isSteinerTriple_card_inter IsSteinerTripleHexads.isSteinerTriple_hexads hB hB' h with h0 | h2
    · rw [h0]; decide
    · rw [h2]; decide

theorem G22_le_orthogonal : G22 ≤ dotForm.orthogonal G22 := by
  rw [G22, Submodule.span_le]
  rintro _ ⟨B, hB, rfl⟩
  rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have hker : Submodule.span (ZMod 2) (ind '' (hexads : Set (Finset (Fin 22)))) ≤
      LinearMap.ker (dotForm.flip (ind B)) := by
    rw [Submodule.span_le]
    rintro _ ⟨B', hB', rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply, dotForm_apply]
    exact dot_ind_hexads hB' hB
  have := hker hn
  rwa [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply] at this

theorem finrank_G22 : Module.finrank (ZMod 2) G22 = 11 := by
  have h1 := Submodule.finrank_mono G22_le_orthogonal
  rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate, finrank_word] at h1
  have := eleven_le_finrank_G22
  omega

theorem G22_isSelfDual : IsSelfDual G22 := by
  have heq : G22 = dotForm.orthogonal G22 := by
    refine Submodule.eq_of_le_of_finrank_le G22_le_orthogonal ?_
    rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate, finrank_word, finrank_G22]
  intro x
  conv_lhs => rw [heq]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [dotForm_apply]

theorem exists_not_mem {s : Finset (Fin 22)} (h : s.card < 22) : ∃ y, y ∉ s := by
  by_contra hne
  push Not at hne
  have : s = Finset.univ := Finset.eq_univ_of_forall hne
  rw [this, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- In S(3,6,22), every set of two or four points meets some block in an odd number of
points. -/
theorem exists_hexad_odd {U : Finset (Fin 22)} (hU : U.card = 2 ∨ U.card = 4) :
    ∃ B ∈ hexads, Odd (U ∩ B).card := by
  have hS := IsSteinerTripleHexads.isSteinerTriple_hexads
  have block : ∀ a b c : Fin 22, a ≠ b → a ≠ c → b ≠ c →
      ∃ B ∈ hexads, a ∈ B ∧ b ∈ B ∧ c ∈ B := by
    intro a b c hab hac hbc
    obtain ⟨B, ⟨hB, hT⟩, -⟩ := hS.2.2 {a, b, c} (Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩)
    exact ⟨B, hB, hT (by simp), hT (by simp), hT (by simp)⟩
  have same : ∀ {B B' : Finset (Fin 22)}, B ∈ hexads → B' ∈ hexads → ∀ {a b c : Fin 22},
      a ≠ b → a ≠ c → b ≠ c → a ∈ B → b ∈ B → c ∈ B → a ∈ B' → b ∈ B' → c ∈ B' → B = B' := by
    intro B B' hB hB' a b c hab hac hbc ha hb hc ha' hb' hc'
    by_contra hne
    have h1 : (B ∩ B').card ≤ 2 := by
      rcases IsSteinerTripleCardInter.isSteinerTriple_card_inter hS hB hB' hne with h | h <;> omega
    have h2 : ({a, b, c} : Finset (Fin 22)) ⊆ B ∩ B' := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> simp_all
    have h3 := Finset.card_le_card h2
    rw [Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩] at h3
    omega
  -- a block through `a` and two points `e, y` with `e ∈ B₀ \ U`, `y ∉ B₀` meets `U` only in `a`
  have single : ∀ {B₀ : Finset (Fin 22)}, B₀ ∈ hexads → ∀ {a e : Fin 22}, a ∈ U → a ∈ B₀ →
      e ∈ B₀ → e ∉ U → (∀ z ∈ U, z ≠ a → z ∈ B₀) → ∃ B ∈ hexads, Odd (U ∩ B).card := by
    intro B₀ hB₀ a e haU haB₀ heB₀ heU hUB₀
    obtain ⟨y, hy⟩ := exists_not_mem (s := B₀) (by rw [card_of_mem_hexads hB₀]; omega)
    have hae : a ≠ e := fun h => heU (h ▸ haU)
    have hay : a ≠ y := fun h => hy (h ▸ haB₀)
    have hey : e ≠ y := fun h => hy (h ▸ heB₀)
    obtain ⟨B, hB, haB, heB, hyB⟩ := block a e y hae hay hey
    refine ⟨B, hB, ?_⟩
    have : U ∩ B = {a} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hzU, hzB⟩
        by_contra hza
        have hze : z ≠ e := fun h => heU (h ▸ hzU)
        have := same hB₀ hB hae (Ne.symm hza) (Ne.symm hze) haB₀ heB₀ (hUB₀ z hzU hza) haB heB hzB
        exact hy (this ▸ hyB)
      · rintro rfl
        exact ⟨haU, haB⟩
    rw [this, Finset.card_singleton]
    exact odd_one
  rcases hU with h2 | h4
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    obtain ⟨x, hx⟩ := exists_not_mem (s := {a, b}) (by rw [Finset.card_pair hab]; omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨B₀, hB₀, ha, hb, hxB⟩ := block a b x hab (Ne.symm hx.1) (Ne.symm hx.2)
    exact single hB₀ (by simp) ha hxB (by simp [hx.1, hx.2]) (fun z hz hza => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact absurd rfl hza
      · exact hb)
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := (Finset.two_lt_card (s := U)).1 (by omega)
    obtain ⟨B₀, hB₀, haB, hbB, hcB⟩ := block a b c hab hac hbc
    by_cases hsub : U ⊆ B₀
    · have hlt : U.card < B₀.card := by rw [h4, card_of_mem_hexads hB₀]; omega
      obtain ⟨e, heB, heU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact single hB₀ ha haB heB heU fun z hz _ => hsub hz
    · obtain ⟨d, hdU, hdB⟩ := Finset.not_subset.1 hsub
      refine ⟨B₀, hB₀, ?_⟩
      have h3 : 3 ≤ (U ∩ B₀).card :=
        three_le_card' (Finset.mem_inter.2 ⟨ha, haB⟩) (Finset.mem_inter.2 ⟨hb, hbB⟩)
          (Finset.mem_inter.2 ⟨hc, hcB⟩) hab hac hbc
      have hle : (U ∩ B₀).card ≤ 3 := by
        have : U ∩ B₀ ⊆ U.erase d := by
          intro z hz
          rw [Finset.mem_inter] at hz
          exact Finset.mem_erase.2 ⟨fun h => hdB (h ▸ hz.2), hz.1⟩
        have := Finset.card_le_card this
        rw [Finset.card_erase_of_mem hdU, h4] at this
        exact this
      rw [show (U ∩ B₀).card = 3 by omega]
      decide

/-- `G22` has minimum weight 6. -/
theorem G22_minWeight : MinWeightAtLeast G22 6 := by
  intro u hu hu0
  have he := even_wt G22_isSelfDual hu
  have hpos : 0 < wt u := Nat.pos_of_ne_zero fun h => hu0 (wt_eq_zero_iff.1 h)
  by_contra hlt
  have hU : (supp u).card = 2 ∨ (supp u).card = 4 := by
    obtain ⟨k, hk⟩ := he
    rw [wt] at hk hpos hlt
    omega
  obtain ⟨B, hB, hodd⟩ := exists_hexad_odd hU
  have h0 : u ⬝ᵥ ind B = 0 := dot_eq_zero G22_isSelfDual hu
    (Submodule.subset_span ⟨B, hB, rfl⟩)
  rw [dot_eq_card, supp_ind, ZMod.natCast_eq_zero_iff_even] at h0
  exact (Nat.not_even_iff_odd.2 hodd) h0

/-! ### The automorphism group -/

/-- The permutation automorphism group of a binary code of length 22. -/
def codeAut (C : Submodule (ZMod 2) Word) : Subgroup (Equiv.Perm (Fin 22)) where
  carrier := {σ | ∀ x : Word, x ∘ σ ∈ C ↔ x ∈ C}
  mul_mem' {σ τ} hσ hτ x := by
    change x ∘ (σ ∘ τ) ∈ C ↔ x ∈ C
    rw [← Function.comp_assoc, hτ, hσ]
  one_mem' x := Iff.rfl
  inv_mem' {σ} hσ x := by
    have := hσ (x ∘ ⇑σ⁻¹)
    rw [Function.comp_assoc, show (⇑σ⁻¹ ∘ ⇑σ : Fin 22 → Fin 22) = id by
      funext i; simp, Function.comp_id] at this
    exact this.symm

variable [CardHexads]

variable [CardHexadAut]

/-! ### Main theorem -/

end CFSGOutside.PlessSloaneG22
