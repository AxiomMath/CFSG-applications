import Mathlib
import CFSGOutside.GiuliettiKorchmaros.Thm61Defs
import CFSGOutside.GiuliettiKorchmaros.Order48GL

/-!
# Binary octahedral group: finite data
-/

open scoped MatrixGroups

namespace CFSGOutside.GiuliettiKorchmaros.Order48

def wordsO : List (List Bool) :=
  [[],
   [true],
   [false],
   [true, true],
   [true, false],
   [false, true],
   [false, false],
   [true, true, true],
   [true, true, false],
   [true, false, true],
   [true, false, false],
   [false, true, true],
   [false, true, false],
   [false, false, true],
   [true, true, true, true],
   [true, true, false, true],
   [true, true, false, false],
   [true, false, true, true],
   [true, false, true, false],
   [true, false, false, true],
   [false, true, true, false],
   [false, true, false, true],
   [false, true, false, false],
   [false, false, true, true],
   [false, false, true, false],
   [true, true, true, true, true],
   [true, true, false, true, true],
   [true, true, false, true, false],
   [true, true, false, false, true],
   [true, false, true, true, false],
   [true, false, true, false, false],
   [true, false, false, true, true],
   [true, false, false, true, false],
   [false, true, true, false, true],
   [false, true, true, false, false],
   [false, true, false, true, true],
   [false, false, true, true, false],
   [false, false, true, false, true],
   [true, true, true, true, true, true],
   [true, true, false, true, true, false],
   [true, true, false, false, true, false],
   [true, false, true, true, false, true],
   [true, false, false, true, true, false],
   [true, false, false, true, false, true],
   [false, true, true, false, true, true],
   [true, true, true, true, true, true, true],
   [true, true, false, true, true, false, true],
   [true, false, true, true, false, true, true]]

/-- The 48 elements of `2O` as a finset (words in the generators). -/
def Octa : Finset SL(2, ZMod 7) := (wordsO.map (evalW b48A b48B)).toFinset

theorem octa_mul : ∀ x ∈ Octa, ∀ y ∈ Octa, x * y ∈ Octa := by
  unfold Octa wordsO evalW; decide +kernel

theorem octa_inv : ∀ x ∈ Octa, x⁻¹ ∈ Octa := by
  unfold Octa wordsO evalW; decide +kernel

theorem octa_gen : b48A ∈ Octa ∧ b48B ∈ Octa ∧ (1 : SL(2, ZMod 7)) ∈ Octa := by
  unfold Octa wordsO evalW; decide +kernel

theorem card_Octa : Octa.card = 48 := by
  unfold Octa wordsO evalW; decide +kernel

theorem mem_bin_iff (g : SL(2, ZMod 7)) : g ∈ binaryOctahedral ↔ g ∈ Octa := by
  constructor
  · intro h
    refine Subgroup.closure_induction (p := fun g _ => g ∈ Octa) ?_ ?_ ?_ ?_ h
    · intro x hx
      rcases hx with rfl | hx
      · exact octa_gen.1
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact octa_gen.2.1
    · exact octa_gen.2.2
    · intro x y _ _ hx hy; exact octa_mul x hx y hy
    · intro x _ hx; exact octa_inv x hx
  · intro h
    unfold Octa at h
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨w, _, rfl⟩ := h
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, _, rfl⟩ := hx
    apply Subgroup.subset_closure
    cases b <;> simp


/-- Image of `s3` in `2O`. -/
def sO : SL(2, ZMod 7) := ⟨!![1, 1; 4, 5], by decide⟩
/-- Image of `t3` in `2O`. -/
def tO : SL(2, ZMod 7) := ⟨!![2, 5; 0, 4], by decide⟩
/-- The element `-1` of `SL(2,3)`. -/
def m1 : SL(2, ZMod 3) := ⟨!![2, 0; 0, 2], by decide⟩

def Fpairs : List (SL(2, ZMod 3) × SL(2, ZMod 7)) :=
  wordsSL3.map fun w => (evalW s3 t3 w, evalW sO tO w)

/-- The isomorphism `SL(2,3) → 2T ⊂ 2O`, as a lookup table. -/
def Ffun (g : SL(2, ZMod 3)) : SL(2, ZMod 7) :=
  ((Fpairs.find? fun p => decide (p.1 = g)).map Prod.snd).getD 1

theorem Ffun_one : Ffun 1 = 1 := by decide +kernel

theorem Ffun_mul : ∀ a b, Ffun (a * b) = Ffun a * Ffun b := by decide +kernel

theorem Ffun_inj : ∀ a b, Ffun a = Ffun b → a = b := by decide +kernel

theorem Ffun_mem : ∀ g, Ffun g ∈ Octa := by decide +kernel

theorem Ffun_pairs : ∀ a b : SL(2, ZMod 3), PRel a b →
    ∃ X ∈ Octa, Ffun a = X * Ffun s3 * X⁻¹ ∧ Ffun b = X * Ffun t3 * X⁻¹ := by
  unfold PRel
  decide +kernel

theorem Ffun_cent : ∀ c ∈ Octa, c * Ffun s3 = Ffun s3 * c → c * Ffun t3 = Ffun t3 * c →
    c = 1 ∨ c = Ffun m1 := by decide +kernel

theorem Ffun_sq : ∀ Y₀ ∈ Octa, (¬ ∃ a, Ffun a = Y₀) → ∃ w, (Y₀ * Ffun w) ^ 2 = Ffun m1 := by
  decide +kernel

theorem m1_facts : m1 ^ 2 = 1 ∧ m1 ≠ 1 := by decide

/-- The embedding `SL(2,3) → 2O`. -/
def Fhom : SL(2, ZMod 3) →* SL(2, ZMod 7) where
  toFun := Ffun
  map_one' := Ffun_one
  map_mul' := Ffun_mul

/-- The embedding `SL(2,3) → 2O`, landing in `binaryOctahedral`. -/
def Fb : SL(2, ZMod 3) →* binaryOctahedral :=
  Fhom.codRestrict binaryOctahedral (fun g => (mem_bin_iff _).2 (Ffun_mem g))

theorem Fb_inj : Function.Injective Fb := by
  intro a b h
  exact Ffun_inj a b (congrArg Subtype.val h)

theorem card_binOct : Nat.card binaryOctahedral = 48 := by
  have : binaryOctahedral ≃ {x // x ∈ Octa} := Equiv.subtypeEquivRight mem_bin_iff
  rw [Nat.card_congr this, Nat.card_eq_fintype_card, Fintype.card_coe, card_Octa]

end CFSGOutside.GiuliettiKorchmaros.Order48
