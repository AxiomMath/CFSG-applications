import CFSGOutside.HallPaige.DoubleCosets

/-!
# A suborbit form of the Wilcox criterion, for the Lyons group

Let `G` act on `X`, let `H = G_{x₀}` be proper and good, and let representatives `r i` be given
such that every point `g • x₀` lies in the `H`-orbit of some `r i • x₀` (so the `H r i H` are
all the double cosets of `H`). If each `H r i H` has a triangle witness (`TriWit`), then
`WilcoxCriterion G` holds. Three sources of triangle witnesses:

* `triWit_one`: the trivial double coset;
* `triWit_of_cube`: some `g = h * r` with `h ∈ H` and `g ^ 3 ∈ H` (then `(g * g)⁻¹ ∈ H g H`);
* `triWit_of_ncard`: the suborbit of `r • x₀` has more than half of the points of the orbit
  (then `S ∩ r • S ≠ ∅` for the suborbit `S`).

This is the form used for `Ly` acting on the cosets of `G₂(5)`, whose suborbit decomposition is a
corpus theorem.
-/

namespace CFSGOutside.HallPaige.Ly

open DoubleCoset MulAction

variable {G : Type*} {X : Type*} [Group G] [MulAction G X]

/-- A triangle witness for the double coset `H r H`: `a, b ∈ H r H` with `a * b` or `(a * b)⁻¹`
in `H r H`. -/
def TriWit (H : Subgroup G) (r : G) : Prop :=
  ∃ a b : G, mk H H a = mk H H r ∧ mk H H b = mk H H r ∧
    (mk H H (a * b) = mk H H r ∨ mk H H (a * b)⁻¹ = mk H H r)

theorem mk_mul_left_of_mem {H : Subgroup G} {h : G} (hh : h ∈ H) (g : G) :
    mk H H (h * g) = mk H H g := by
  rw [DoubleCoset.eq]
  exact ⟨h⁻¹, H.inv_mem hh, 1, H.one_mem, by group⟩

theorem mk_mul_right_of_mem {H : Subgroup G} {h : G} (hh : h ∈ H) (g : G) :
    mk H H (g * h) = mk H H g := by
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, h⁻¹, H.inv_mem hh, by group⟩

theorem triWit_one (H : Subgroup G) : TriWit H 1 :=
  ⟨1, 1, rfl, rfl, Or.inl (by rw [one_mul])⟩

/-- An element `g = h * r` (`h ∈ H`) with `g ^ 3 ∈ H` is a triangle witness:
`(g * g)⁻¹ = g * (g ^ 3)⁻¹ ∈ H r H`. -/
theorem triWit_of_cube {H : Subgroup G} {h r : G} (hh : h ∈ H) (h3 : (h * r) ^ 3 ∈ H) :
    TriWit H r := by
  have hg : mk H H (h * r) = mk H H r := mk_mul_left_of_mem hh r
  refine ⟨h * r, h * r, hg, hg, Or.inr ?_⟩
  have e : ∀ g : G, (g * g)⁻¹ = g * (g ^ 3)⁻¹ := fun g => by group
  rw [e (h * r), mk_mul_right_of_mem (H.inv_mem h3), hg]

/-- Counting: if the suborbit `S` of `r • x₀` has more than half of the points of the orbit of
`x₀`, then `S` meets `r • S`, which gives a triangle witness. -/
theorem triWit_of_ncard (x₀ : X) {r : G} (hfin : (orbit G x₀).Finite)
    (hcard : (orbit G x₀).ncard < 2 * (orbit (stabilizer G x₀) (r • x₀)).ncard) :
    TriWit (stabilizer G x₀) r := by
  set H := stabilizer G x₀ with hH
  set S : Set X := orbit H (r • x₀) with hS
  set T : Set X := (fun y => r • y) '' S with hT
  have hSO : S ⊆ orbit G x₀ := by
    rintro _ ⟨h, rfl⟩
    exact ⟨(h : G) * r, by show ((h : G) * r) • x₀ = (h : G) • r • x₀; rw [mul_smul]⟩
  have hTO : T ⊆ orbit G x₀ := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨r * ((h : G) * r), by
      show (r * ((h : G) * r)) • x₀ = r • (h : G) • r • x₀; rw [mul_smul, mul_smul]⟩
  have hTS : T.ncard = S.ncard :=
    Set.ncard_image_of_injective S (MulAction.injective r)
  have hmeet : ¬ Disjoint S T := by
    intro hd
    have hu := Set.ncard_union_eq hd (hfin.subset hSO) (hfin.subset hTO)
    have hle := Set.ncard_le_ncard (Set.union_subset hSO hTO) hfin
    omega
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨_, ⟨h', rfl⟩, ⟨y, ⟨h, rfl⟩, hy⟩⟩ := hmeet
  refine ⟨r, (h : G) * r, rfl, mk_mul_left_of_mem h.2 r, Or.inl ?_⟩
  refine ((mk_stabilizer_eq_mk_iff x₀ r (r * ((h : G) * r))).2 ⟨(h' : G), h'.2, ?_⟩).symm
  rw [mul_smul, mul_smul]
  exact hy.symm

/-- **Suborbit form of the Wilcox criterion.** -/
theorem wilcoxCriterion_of_cover (x₀ : X) {ι : Type*} (r : ι → G)
    (hne : stabilizer G x₀ ≠ ⊤) (hgood : IsGood (stabilizer G x₀))
    (hcov : ∀ g : G, ∃ i, g • x₀ ∈ orbit (stabilizer G x₀) (r i • x₀))
    (hw : ∀ i, TriWit (stabilizer G x₀) (r i)) : WilcoxCriterion G := by
  refine wilcoxCriterion_of_triangle (stabilizer G x₀) hne hgood fun q => ?_
  obtain ⟨i, hi⟩ := hcov q.out
  obtain ⟨h, hh⟩ := hi
  have hq : mk (stabilizer G x₀) (stabilizer G x₀) (r i) = q := by
    rw [← out_eq' q]
    exact (mk_stabilizer_eq_mk_iff x₀ (r i) q.out).2 ⟨(h : G), h.2, hh⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hw i
  exact ⟨a, b, ha.trans hq, hb.trans hq, hab.imp (fun e => e.trans hq) (fun e => e.trans hq)⟩

end CFSGOutside.HallPaige.Ly
