import CFSGOutside.Corpus.HallPaige.Ly

/-!
# Kernel-checked words in the 111-dimensional model of `Ly`

Words over the letters `aStar k` (`k < 7`) and `(aStar (k - 7))⁻¹` (`7 ≤ k < 14`) are evaluated as
packed matrices with the corpus multiplication `fMul`; the corpus facts `fmul`, `one_facts`,
`af_facts` say that the packed product is the matrix of the word (`pw_spec`). A word whose packed
value is the packed identity is `1` in `J` (`eq_one_of_pw`); one whose packed `(0, 0)` entry is not
`1` is not `1` (`ne_one_of_pw`).
-/

namespace CFSGOutside.HallPaige.Ly

open CFSGOutside.Corpus.Ly

/-- Packed letters. -/
noncomputable def letP (k : ℕ) : ℕ := if k < 7 then AF k else AI (k - 7)

/-- Packed product of a word, starting from `X`. -/
noncomputable def pw (X : ℕ) : List ℕ → ℕ
  | [] => X
  | k :: w => pw (fMul BC X (letP k)) w

section

variable [Theorems] [LySeed]

/-- The letters in `J`. -/
noncomputable def letJ (k : ℕ) : J := if k < 7 then aStar k else (aStar (k - 7))⁻¹

/-- A word in `J`. -/
noncomputable def wJ (w : List ℕ) : J := (w.map letJ).prod

theorem wJ_append (u v : List ℕ) : wJ (u ++ v) = wJ u * wJ v := by
  simp [wJ, List.map_append, List.prod_append]

theorem let_spec {k : ℕ} (hk : k < 14) :
    LCanon 12 111 111 (letP k) ∧ bigM (letP k) = mat (letJ k) := by
  unfold letP letJ
  split_ifs with h
  · exact ⟨(Theorems.af_facts h).1, (Theorems.af_facts h).2.1⟩
  · have h' : k - 7 < 7 := by omega
    exact ⟨(Theorems.af_facts h').2.2.1, (Theorems.af_facts h').2.2.2⟩

theorem pw_spec : ∀ (w : List ℕ) (X : ℕ), (∀ k ∈ w, k < 14) → LCanon 12 111 111 X →
    LCanon 12 111 111 (pw X w) ∧ bigM (pw X w) = bigM X * mat (wJ w)
  | [], X, _, hX => ⟨hX, by
      show bigM X = bigM X * mat 1
      rw [mat_one, Matrix.mul_one]⟩
  | k :: w, X, hw, hX => by
    obtain ⟨cl, el⟩ := let_spec (hw k List.mem_cons_self)
    obtain ⟨c1, e1⟩ := Theorems.fmul hX cl
    obtain ⟨c, e⟩ := pw_spec w _ (fun l hl => hw l (List.mem_cons_of_mem _ hl)) c1
    refine ⟨c, ?_⟩
    rw [show pw X (k :: w) = pw (fMul BC X (letP k)) w from rfl, e, e1, el, Matrix.mul_assoc]
    rfl

theorem mat_pw (w : List ℕ) (hw : ∀ k ∈ w, k < 14) : bigM (pw BC.ONEF w) = mat (wJ w) := by
  rw [(pw_spec w _ hw Theorems.one_facts.1).2, Theorems.one_facts.2, Matrix.one_mul]

theorem eq_one_of_pw (w : List ℕ) (hw : ∀ k ∈ w, k < 14)
    (h : Nat.beq (pw BC.ONEF w) BC.ONEF = true) : wJ w = 1 := by
  have e := mat_pw w hw
  rw [Nat.eq_of_beq_eq_true h, Theorems.one_facts.2] at e
  exact Subtype.ext (Units.ext e.symm)

theorem ne_one_of_pw (w : List ℕ) (hw : ∀ k ∈ w, k < 14) {d : ℕ}
    (h : pw BC.ONEF w % 2 ^ 12 = d) (hd : ((d : ℕ) : ZMod 5) ≠ 1) : wJ w ≠ 1 := by
  intro h1
  have e := congrFun (congrFun (mat_pw w hw) 0) 0
  rw [h1] at e
  apply hd
  have e' : bigM (pw BC.ONEF w) 0 0 = ((d : ℕ) : ZMod 5) := by
    simp only [bigM, ent, Fin.val_zero, mul_zero, add_zero, pow_zero, Nat.div_one, h]
  rw [← e', e]
  rfl

theorem wJ_mem_lyH : ∀ w : List ℕ, (∀ k ∈ w, (2 ≤ k ∧ k ≤ 6) ∨ (9 ≤ k ∧ k ≤ 13)) → wJ w ∈ lyH
  | [], _ => lyH.one_mem
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have hs : ∀ j, 2 ≤ j → j ≤ 6 → aStar j ∈ lyH := fun j h1 h2 =>
      Subgroup.subset_closure ⟨j, ⟨h1, h2⟩, rfl⟩
    have hl : letJ k ∈ lyH := by
      unfold letJ
      split_ifs with h
      · exact hs k (by omega) (by omega)
      · exact lyH.inv_mem (hs (k - 7) (by omega) (by omega))
    have : wJ (k :: w) = letJ k * wJ w := by simp [wJ]
    rw [this]
    exact lyH.mul_mem hl (wJ_mem_lyH w fun l hl' => hw l (List.mem_cons_of_mem _ hl'))

/-- The `a, b` letters of `abWord` as letters of `wJ`. -/
def abL (l : ℕ) : ℕ := [0, 1, 7, 8].getD l 0

theorem abWord_eq : ∀ w : List ℕ, (∀ l ∈ w, l < 4) → abWord w = wJ (w.map abL)
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have h1 : abLet l = letJ (abL l) := by
      interval_cases l <;>
        simp [abLet, letJ, abL, Theorems.aStar_zero, Theorems.aStar_one]
    have e : abWord (l :: w) = abLet l * abWord w := by simp [abWord]
    have e' : wJ ((l :: w).map abL) = letJ (abL l) * wJ (w.map abL) := by simp [wJ]
    rw [e, e', h1, abWord_eq w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]

end

end CFSGOutside.HallPaige.Ly
