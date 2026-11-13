import CFSGOutside.VanDamHaemers.Facts

/-!
# Girth from the spectrum, via non-backtracking walks

For a cubic graph, the matrices `F r` counting non-backtracking walks of length `r` satisfy
`A F₁ = F₂ + 3 F₀` and `A F_{r+1} = F_{r+2} + 2 F_r` (`r ≥ 1`), so `F r = p_r(A)` for explicit
polynomials `p_r`. Their traces are determined by the spectrum, and vanish for `1 ≤ r ≤ 11`;
a cycle of length `g ≤ 11` would give a closed non-backtracking walk of length `g`.
-/

namespace CFSGOutside.VanDamHaemers

open Matrix Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A walk is non-backtracking if it never returns to the vertex two steps back. -/
def IsNB {u v : V} (p : G.Walk u v) : Prop :=
  ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

open Classical in
/-- The non-backtracking walks of length `r` from `u` to `v`. -/
noncomputable def nbWalks (r : ℕ) (u v : V) : Finset (G.Walk u v) :=
  (G.finsetWalkLength r u v).filter fun p => IsNB G p

lemma mem_nbWalks {r : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ nbWalks G r u v ↔ p.length = r ∧ IsNB G p := by
  simp [nbWalks, SimpleGraph.mem_finsetWalkLength_iff]

lemma isNB_cons_iff {u w v : V} (h : G.Adj u w) (p : G.Walk w v) (hp : 1 ≤ p.length) :
    IsNB G (Walk.cons h p) ↔ IsNB G p ∧ p.getVert 1 ≠ u := by
  constructor
  · intro hnb
    refine ⟨fun i hi => ?_, fun he => ?_⟩
    · have := hnb (i + 1) (by rw [Walk.length_cons]; omega)
      simpa [Walk.getVert_cons_succ] using this
    · have := hnb 0 (by rw [Walk.length_cons]; omega)
      simp [Walk.getVert_cons_succ, he] at this
  · rintro ⟨hnb, hne⟩ i hi
    rw [Walk.length_cons] at hi
    rcases i with _ | i
    · simpa [Walk.getVert_cons_succ] using hne.symm
    · simpa [Walk.getVert_cons_succ] using hnb i (by omega)

lemma isNB_of_length_le {u v : V} (p : G.Walk u v) (h : p.length ≤ 1) : IsNB G p :=
  fun i hi => absurd hi (by omega)

/-- The key recursion for non-backtracking walk counts in a cubic graph. -/
lemma nb_recursion (hdeg : ∀ v, G.degree v = 3) (r : ℕ) (u v : V) :
    ∑ w ∈ G.neighborFinset u, (nbWalks G (r + 1) w v).card =
      (nbWalks G (r + 2) u v).card + (if r = 0 then 3 else 2) * (nbWalks G r u v).card := by
  classical
  set S := (G.neighborFinset u).sigma fun w => nbWalks G (r + 1) w v
  have hS : S.card = ∑ w ∈ G.neighborFinset u, (nbWalks G (r + 1) w v).card := card_sigma _ _
  rw [← hS, ← card_filter_add_card_filter_not (s := S)
    (p := fun a : (Σ w, G.Walk w v) => a.2.getVert 1 ≠ u)]
  congr 1
  · -- good pairs: extending by the first edge gives a non-backtracking walk
    apply card_bij (fun a ha => Walk.cons (by
        have := (mem_sigma.1 (mem_filter.1 ha).1).1
        exact (mem_neighborFinset _ _ _).1 this) a.2)
    · intro a ha
      obtain ⟨hmem, hne⟩ := mem_filter.1 ha
      obtain ⟨-, hp⟩ := mem_sigma.1 hmem
      obtain ⟨hl, hnb⟩ := (mem_nbWalks G).1 hp
      rw [mem_nbWalks, Walk.length_cons, hl, isNB_cons_iff G _ _ (by omega)]
      exact ⟨rfl, hnb, hne⟩
    · rintro ⟨w, p⟩ ha ⟨w', p'⟩ ha' he
      simp only [Walk.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      simp only [heq_eq_eq] at he
      subst he
      rfl
    · intro q hq
      obtain ⟨hl, hnb⟩ := (mem_nbWalks G).1 hq
      cases q with
      | nil => simp at hl
      | cons h p =>
        rw [Walk.length_cons] at hl
        rw [isNB_cons_iff G _ _ (by omega)] at hnb
        refine ⟨⟨_, p⟩, ?_, rfl⟩
        rw [mem_filter, mem_sigma, mem_neighborFinset, mem_nbWalks]
        exact ⟨⟨h, by dsimp only; omega, hnb.1⟩, hnb.2⟩
  · -- bad pairs: the walk returns to `u` at the second step
    have hcount : ∀ q ∈ nbWalks G r u v,
        ((G.neighborFinset u).filter fun w => r = 0 ∨ w ≠ q.getVert 1).card =
          if r = 0 then 3 else 2 := by
      intro q hq
      obtain ⟨hl, -⟩ := (mem_nbWalks G).1 hq
      split_ifs with hr
      · rw [filter_true_of_mem (fun _ _ => Or.inl hr), card_neighborFinset_eq_degree, hdeg]
      · have hadj : G.Adj u (q.getVert 1) := by
          have := q.adj_getVert_succ (i := 0) (by omega)
          simpa using this
        have : (G.neighborFinset u).filter (fun w => r = 0 ∨ w ≠ q.getVert 1) =
            (G.neighborFinset u).erase (q.getVert 1) := by
          ext w; simp [hr, and_comm]
        rw [this, card_erase_of_mem ((mem_neighborFinset _ _ _).2 hadj),
          card_neighborFinset_eq_degree, hdeg]
    rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_congr rfl hcount, ← card_sigma]
    symm
    apply card_bij (fun (b : Σ _ : G.Walk u v, V) hb => (⟨b.2, Walk.cons (by
        have := (mem_filter.1 (mem_sigma.1 hb).2).1
        exact ((mem_neighborFinset _ _ _).1 this).symm) b.1⟩ : Σ w, G.Walk w v))
    · rintro ⟨q, w⟩ hb
      obtain ⟨hq, hw⟩ := mem_sigma.1 hb
      obtain ⟨hwu, hor⟩ := mem_filter.1 hw
      obtain ⟨hl, hnb⟩ := (mem_nbWalks G).1 hq
      rw [mem_filter, mem_sigma, mem_nbWalks]
      refine ⟨⟨hwu, by rw [Walk.length_cons, hl], ?_⟩, by simp⟩
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exact isNB_of_length_le G _ (by rw [Walk.length_cons, hl, hr])
      · rw [isNB_cons_iff G _ _ (by omega)]
        exact ⟨hnb, fun he => (hor.resolve_left (by omega)) he.symm⟩
    · rintro ⟨q, w⟩ hb ⟨q', w'⟩ hb' he
      simp only [Sigma.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      simp only [heq_eq_eq, Walk.cons.injEq, true_and] at he
      rw [he]
    · rintro ⟨w, p⟩ ha
      obtain ⟨hmem, hbad⟩ := mem_filter.1 ha
      simp only [ne_eq, not_not] at hbad
      obtain ⟨hwu, hp⟩ := mem_sigma.1 hmem
      obtain ⟨hl, hnb⟩ := (mem_nbWalks G).1 hp
      cases p with
      | nil => simp at hl
      | cons h q =>
        simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at hbad
        subst hbad
        rw [Walk.length_cons] at hl
        refine ⟨⟨q, w⟩, ?_, rfl⟩
        rw [mem_sigma, mem_filter]
        refine ⟨?_, hwu, ?_⟩
        · rw [mem_nbWalks]
          rcases Nat.eq_zero_or_pos r with hr | hr
          · exact ⟨by show q.length = r; omega, isNB_of_length_le G _ (by show q.length ≤ 1; omega)⟩
          · exact ⟨by show q.length = r; omega,
              ((isNB_cons_iff G _ _ (by show 1 ≤ q.length; omega)).1 hnb).1⟩
        · rcases Nat.eq_zero_or_pos r with hr | hr
          · exact Or.inl hr
          · exact Or.inr fun he => ((isNB_cons_iff G _ _ (by show 1 ≤ q.length; omega)).1 hnb).2 he.symm

end CFSGOutside.VanDamHaemers
