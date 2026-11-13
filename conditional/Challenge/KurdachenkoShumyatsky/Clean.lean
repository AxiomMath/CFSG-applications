import CFSGOutside.KurdachenkoShumyatsky.Defs

/-!
# Kurdachenko–Shumyatsky, Lemma `schrei`

L. A. Kurdachenko, P. Shumyatsky, *The ranks of central factor and commutator groups*, Math. Proc.
Cambridge Philos. Soc. 154 (2013), 63–69, DOI 10.1017/S0305004112000412 (arXiv:1204.4641).
-/

open CFSGOutside.KurdachenkoShumyatsky

/-- **Kurdachenko–Shumyatsky, Lemma `schrei`** (Math. Proc. Cambridge Philos. Soc. 154 (2013),
the lemma before the proof of Theorem 1): *Let `G` be a finite group of rank `r` and assume
that `G` has no nontrivial normal soluble subgroups. Then `G` has a normal series `M ≤ T ≤ G`
such that `M` is isomorphic to a direct product of at most `r` non-abelian simple groups, `T/M`
is soluble and `G/T` has order at most `r!`.* -/
theorem CFSGOutsideClean.KurdachenkoShumyatsky.schrei {G : Type} [Group G] [Finite G]
    {r : ℕ} (hr : rank G = r)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ∃ (M T : Subgroup G) (_ : M.Normal) (_ : T.Normal), M ≤ T ∧
      (∃ (ι : Type) (_ : Fintype ι) (S : ι → Type) (_ : ∀ i, Group (S i)),
        Fintype.card ι ≤ r ∧ (∀ i, IsSimpleGroup (S i)) ∧
        (∀ i, ∃ a b : S i, a * b ≠ b * a) ∧ Nonempty (M ≃* ((i : ι) → S i))) ∧
      Group.IsSolvable (T ⧸ M.subgroupOf T) ∧ Nat.card (G ⧸ T) ≤ r.factorial := sorry
