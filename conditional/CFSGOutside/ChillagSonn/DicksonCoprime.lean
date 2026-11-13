import CFSGOutside.Corpus.DicksonPsl2

/-!
# Nonsolvable subgroups of `PSL(2, q)` of order prime to `p`

From Dickson's classification: a nonsolvable subgroup of `PSL(2, q)`, `q = p ^ f`, of order prime to `p` is `A₅`,
so it has order 60. Used in Lemma (1.9) of Chillag–Sonn.
-/

namespace CFSGOutside.ChillagSonn

open Matrix

/-- The dihedral group is solvable: the rotations form an abelian kernel of the map onto `C₂`. -/
theorem dihedralGroup_isSolvable (n : ℕ) : Group.IsSolvable (DihedralGroup n) := by
  let f : Multiplicative (ZMod n) →* DihedralGroup n :=
    { toFun := fun i => .r i.toAdd, map_one' := rfl, map_mul' := fun _ _ => (DihedralGroup.r_mul_r _ _).symm }
  let g : DihedralGroup n →* Multiplicative (ZMod 2) :=
    { toFun := fun | .r _ => 1 | .sr _ => .ofAdd 1
      map_one' := rfl
      map_mul' := by
        rintro (i | i) (j | j) <;>
          simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
            DihedralGroup.sr_mul_sr]
        all_goals decide }
  refine Group.isSolvable_of_ker_le_range f g ?_
  rintro (i | i) hx
  · exact ⟨.ofAdd i, rfl⟩
  · change Multiplicative.ofAdd (1 : ZMod 2) = 1 at hx
    exact absurd hx (by decide)

/-- The unipotent element `!![1, 1; 0, 1]` of `SL(2, K)`. -/
def unipSLOne (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp⟩

/-- Powers of the unipotent matrix. -/
theorem unip_pow (K : Type) [Field K] (k : ℕ) :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) ^ k = !![1, (k : K); 0, 1] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih => rw [pow_succ, ih]; ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- In characteristic `p`, the image of the unipotent element in `PSL(2, K)` has order `p`. -/
theorem orderOf_unip {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    orderOf (QuotientGroup.mk (unipSLOne K) : ProjectiveSpecialLinearGroup (Fin 2) K) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow]
    have hm : ((unipSLOne K ^ p : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_pow, unipSLOne, Matrix.SpecialLinearGroup.coe_mk, unip_pow, CharP.cast_eq_zero]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have : unipSLOne K ^ p = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [hm]; rfl
    rw [this, QuotientGroup.mk_one]
  · intro h
    have h' := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, map_one, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar] at h'
    obtain ⟨u, hu⟩ := h'
    have := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at this
    simp [unipSLOne] at this

/-- `p` divides `|PSL(2, K)|` in characteristic `p`. -/
theorem dvd_card_psl {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    p ∣ Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) :=
  orderOf_unip (K := K) p ▸ orderOf_dvd_natCard _

/-- `p` divides `|PGL(2, K)|` in characteristic `p`. -/
theorem dvd_card_pgl {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    p ∣ Nat.card (ProjGenLinGroup (Fin 2) K) := by
  have := orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (QuotientGroup.mk (unipSLOne K))
  exact orderOf_unip (K := K) p ▸ this ▸ orderOf_dvd_natCard _

open CFSGOutside.Corpus in
/-- A nonsolvable subgroup of `PSL(2, q)` of order prime to the characteristic has order 60 (it is `A₅`). -/
theorem card_eq_sixty_of_not_isSolvable [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hH : ¬ Group.IsSolvable H)
    (hp : ¬ p ∣ Nat.card H) : Nat.card H = 60 := by
  have solv {G : Type} [Group G] (e : H ≃* G) (hG : Group.IsSolvable G) : False :=
    hH (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  rcases DicksonPsl2SubgroupClassification.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    h | ⟨_, _, _, h⟩ | ⟨z, _, _, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ |
      ⟨m, t, _, _, N, C, _, hN, hNc, hC, _, _, hNC⟩ | ⟨m, _, _, ⟨e⟩⟩ | ⟨m, _, _, ⟨e⟩⟩
  · exact (hH inferInstance).elim
  · exact (hH inferInstance).elim
  · exact (solv e (dihedralGroup_isSolvable z)).elim
  · exact (solv e (alternatingGroup.isSolvable (by simp))).elim
  · exact (solv e (Equiv.Perm.isSolvable (by simp))).elim
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]; simp [Nat.factorial]
  · have hm : m = 0 := by
      by_contra hm
      exact hp ((dvd_pow_self p hm).trans (hNc ▸ Subgroup.card_subgroup_dvd_card N))
    have hNb : N = ⊥ := Subgroup.eq_bot_of_card_eq N (by rw [hNc, hm, pow_zero])
    rw [hNb, bot_sup_eq] at hNC
    subst hNC
    have : IsCyclic H := isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective
    exact (hH inferInstance).elim
  · exact (hp (Nat.card_congr e.toEquiv ▸ dvd_card_psl p)).elim
  · exact (hp (Nat.card_congr e.toEquiv ▸ dvd_card_pgl p)).elim

end CFSGOutside.ChillagSonn
