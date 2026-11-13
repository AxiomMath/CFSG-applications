import CFSGOutside.Corpus.HallPaige.B
import CFSGOutside.HallPaige.Sporadic.B.Conj
import CFSGOutside.HallPaige.Sporadic.B.Check

/-!
# Elements of the corpus model of `B`

From the corpus theorems `certificate17101`, `certificate17450` and `genA₁_mul_self` (fields of
`CFSGOutside.Corpus.B.Theorems`): the matrices `stripMat Seven.t1`, `Seven.al`, `Seven.e3`,
`SevenLocal.s4` and the seed `stripMat Seeds.A1` lie in the model and are invertible there, giving
elements `τ₁ = tau`, `α = alpha`, `e`, `s₄ = sFour`, `a₁` of `NativeSporadic.B`; `τ₁`, `α`, `s₄` lie in
`2A`, `τ₁ α` in `2C` (orbital `1`) and `τ₁ s₄` has order 4 with square in `2B` (orbital `3`).
-/

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B CFSGOutside.Corpus.B.Blueprint CFSGOutside.Corpus.B.Monster.GMS
  CFSGOutside.Corpus.B.KC.BM CFSGOutside.Corpus.B.KC.BM.SevenFacts

local notation "𝔹" => NativeSporadic.B
local notation "SM" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2
local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

-- Elaboration unfolds the large literal matrices in a few unification problems.
set_option maxRecDepth 100000

/-- The matrix of an element of the model. -/
abbrev mat (x : 𝔹) : MatB := x.val.val

theorem mat_mul (x y : 𝔹) : mat (x * y) = mat x * mat y := rfl

theorem mat_sq (x : 𝔹) : mat (x ^ 2) = mat x * mat x := by rw [pow_two]; rfl

theorem eq_one_of_mat {x : 𝔹} (h : mat x = 1) : x = 1 := Units.ext (Subtype.ext h)

instance finite_model : Finite 𝔹 :=
  Finite.of_injective (fun u : 𝔹 => (u.val.val : Fin 4370 → Fin 4370 → ZMod 2))
    fun _ _ h => Units.ext (Subtype.ext h)

/-- An element whose matrix is an involution `X` with `rank (X - 1) > 0` has order 2. -/
theorem orderOf_eq_two_of {x : 𝔹} (h : mat x * mat x = 1) {k : ℕ} (hk : 0 < k)
    (hr : (mat x - 1).rank = k) : orderOf x = 2 := by
  have h2 : x ^ 2 = 1 := eq_one_of_mat (by rw [mat_sq]; exact h)
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [h1] at hr
  have : (mat (1 : 𝔹) - 1).rank = 0 := by
    rw [show mat (1 : 𝔹) = 1 from rfl, sub_self, Matrix.rank_zero]
  omega

section Model

variable [Theorems]

theorem words : SevenWords := Theorems.certificate17101.1.1

theorem f17101 : Fact17101Of (stripMat Seven.al) (stripMat Seven.x) (stripMat Seven.y)
    (stripMat Seven.t1) (stripMat Seven.t2) (stripMat Seven.e3) :=
  Theorems.certificate17101.1.2

theorem f17450 : Fact17450Of (stripMat Seven.al) (stripMat Seven.x) (stripMat Seven.t1)
    (stripMat SevenLocal.s3) (stripMat SevenLocal.s4) (stripMat SevenLocal.f)
    (stripMat SevenLocal.u1) (stripMat SevenLocal.u2) :=
  Theorems.certificate17450.2.2.2.2.2.2

theorem mem_A1 : stripMat Seeds.A1 ∈ SM := by
  rw [← Theorems.certificate17101.2.1]
  exact Submonoid.subset_closure (Set.mem_insert _ _)

theorem mem_A2 : stripMat Seeds.A2 ∈ SM := by
  rw [← Theorems.certificate17101.2.2.1]
  exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mems : stripMat Seven.g ∈ SM ∧ stripMat Seven.al ∈ SM ∧ stripMat Seven.t1 ∈ SM ∧
    stripMat Seven.e3 ∈ SM :=
  Theorems.certificate17101.2.2.2 _ mem_A1 mem_A2

theorem mem_t2_word {S : Submonoid MatB} {Y T : MatB} (hy : Y ∈ S) (ht : T ∈ S) :
    Y ^ 3 * T * Y ^ 2 ∈ S :=
  S.mul_mem (S.mul_mem (S.pow_mem hy 3) ht) (S.pow_mem hy 2)

theorem mem_w4W {S : Submonoid MatB} {Y T E : MatB} (hy : Y ∈ S) (ht : T ∈ S) (he : E ∈ S) :
    w4W Y T E ^ 7 ∈ S :=
  S.pow_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.pow_mem he 2)
    (S.pow_mem hy 4)) (S.pow_mem he 2)) ht) hy) he) 7

theorem mem_s4 : stripMat SevenLocal.s4 ∈ SM := by
  have hy : stripMat Seven.y ∈ SM := by
    have := Submonoid.pow_mem _ mems.1 14
    rwa [← words.2.2.1] at this
  have ht2 : stripMat Seven.t2 ∈ SM := by
    have := mem_t2_word hy mems.2.2.1
    rwa [← words.2.2.2] at this
  have := mem_w4W hy ht2 mems.2.2.2
  rwa [← Theorems.certificate17450.2.2.1] at this

theorem t1_sq : stripMat Seven.t1 * stripMat Seven.t1 = 1 := f17101.2.2.2.2.2.2.2.2.2.2.1

theorem t1_rank : (stripMat Seven.t1 - 1).rank = 1860 := f17101.2.2.2.2.2.2.2.2.2.2.2.1

theorem t1_al : stripMat Seven.t1 * stripMat Seven.al = stripMat Seven.al * stripMat Seven.t1 :=
  f17101.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem t1_ne_al : stripMat Seven.t1 ≠ stripMat Seven.al := f17101.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem al_sq : stripMat Seven.al * stripMat Seven.al = 1 := f17101.1

theorem al_rank : (stripMat Seven.al - 1).rank = 1860 := f17101.2.2.1

theorem e3_cube : stripMat Seven.e3 ^ 3 = 1 := f17101.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem al_t1_rank : (stripMat Seven.al * stripMat Seven.t1 - 1).rank = 2158 := f17450.2.1

theorem s4_sq : stripMat SevenLocal.s4 * stripMat SevenLocal.s4 = 1 := f17450.2.2.2.2.2.2.2.2.1

theorem s4_rank : (stripMat SevenLocal.s4 - 1).rank = 1860 := f17450.2.2.2.2.2.2.2.2.2.1

theorem t1s4_pow : (stripMat Seven.t1 * stripMat SevenLocal.s4) ^ 4 = 1 :=
  f17450.2.2.2.2.2.2.2.2.2.2.2.1

theorem t1s4_rank : ((stripMat Seven.t1 * stripMat SevenLocal.s4) ^ 2 - 1).rank = 2048 :=
  f17450.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem A1_sq : stripMat Seeds.A1 * stripMat Seeds.A1 = 1 := by
  rw [← Theorems.certificate17101.2.1]
  exact Theorems.genA₁_mul_self

/-- `τ₁`: the corpus element `tauOne` (matrix `Seven.t1`). -/
noncomputable def tau : 𝔹 :=
  ⟨⟨stripMat Seven.t1, mems.2.2.1⟩, ⟨stripMat Seven.t1, mems.2.2.1⟩, Subtype.ext t1_sq,
    Subtype.ext t1_sq⟩

/-- `α`: the corpus element `alphaB` (matrix `Seven.al`). -/
noncomputable def alpha : 𝔹 :=
  ⟨⟨stripMat Seven.al, mems.2.1⟩, ⟨stripMat Seven.al, mems.2.1⟩, Subtype.ext al_sq,
    Subtype.ext al_sq⟩

/-- `e`: the corpus element `eSeven` (matrix `Seven.e3`, of order 3). -/
noncomputable def ee : 𝔹 :=
  ⟨⟨stripMat Seven.e3, mems.2.2.2⟩, ⟨stripMat Seven.e3 ^ 2, pow_mem mems.2.2.2 2⟩,
    Subtype.ext (by rw [Submonoid.coe_mul, ← pow_succ']; exact e3_cube),
    Subtype.ext (by rw [Submonoid.coe_mul, ← pow_succ]; exact e3_cube)⟩

/-- `s₄`: the corpus element `sFour` (matrix `SevenLocal.s4`). -/
noncomputable def sFour : 𝔹 :=
  ⟨⟨stripMat SevenLocal.s4, mem_s4⟩, ⟨stripMat SevenLocal.s4, mem_s4⟩, Subtype.ext s4_sq,
    Subtype.ext s4_sq⟩

/-- `a₁`: the first seed (matrix `Seeds.A1`, an involution). -/
noncomputable def aOne : 𝔹 :=
  ⟨⟨stripMat Seeds.A1, mem_A1⟩, ⟨stripMat Seeds.A1, mem_A1⟩, Subtype.ext A1_sq, Subtype.ext A1_sq⟩

/-- `p = a₁ τ₁ a₁⁻¹`. -/
noncomputable def pp : 𝔹 := aOne * tau * aOne⁻¹

theorem mat_tau : mat tau = stripMat Seven.t1 := rfl
theorem mat_alpha : mat alpha = stripMat Seven.al := rfl
theorem mat_ee : mat ee = stripMat Seven.e3 := rfl
theorem mat_ee_inv : mat ee⁻¹ = stripMat Seven.e3 ^ 2 := rfl
theorem mat_sFour : mat sFour = stripMat SevenLocal.s4 := rfl
theorem mat_pp : mat pp = stripMat Seeds.A1 * stripMat Seven.t1 * stripMat Seeds.A1 := rfl

/-- `rank (X - 1) = k` with `X² = 1` and `k ∈ {1860, 2048, 2158}` puts `X` in `2A`, `2B`, `2C`. -/
theorem babyInv_zero_of {x : 𝔹} (h : mat x * mat x = 1) (hr : (mat x - 1).rank = 1860) :
    BabyInv 0 x :=
  Theorems.babyInv_zero_of_rank_1860 (orderOf_eq_two_of h (by norm_num) hr) hr

theorem babyOrbit_zero_of {r s : 𝔹} (h : mat (r * s) * mat (r * s) = 1)
    (hr : (mat (r * s) - 1).rank = 2048) : BabyOrbit 0 r s :=
  Theorems.babyInv_one_of_rank_2048 (orderOf_eq_two_of h (by norm_num) hr) hr

theorem babyOrbit_one_of {r s : 𝔹} (h : mat (r * s) * mat (r * s) = 1)
    (hr : (mat (r * s) - 1).rank = 2158) : BabyOrbit 1 r s :=
  Theorems.babyInv_three_of_rank_2158 (orderOf_eq_two_of h (by norm_num) hr) hr

theorem babyOrbit_three_of {r s : 𝔹} (h : mat ((r * s) ^ 2) * mat ((r * s) ^ 2) = 1)
    (hr : (mat ((r * s) ^ 2) - 1).rank = 2048) : BabyOrbit 3 r s := by
  have h2 := orderOf_eq_two_of h (by norm_num) hr
  refine ⟨?_, Theorems.babyInv_one_of_rank_2048 h2 hr⟩
  have hne : (r * s) ^ 2 ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have h4 : (r * s) ^ 2 ^ (1 + 1) = 1 := by
    have := pow_orderOf_eq_one ((r * s) ^ 2)
    rw [h2] at this
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul]
    exact this
  rw [orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one]; exact hne) h4]
  norm_num

theorem tau_babyInv : BabyInv 0 tau := babyInv_zero_of t1_sq t1_rank

theorem alpha_babyInv : BabyInv 0 alpha := babyInv_zero_of al_sq al_rank

theorem sFour_babyInv : BabyInv 0 sFour := babyInv_zero_of s4_sq s4_rank

theorem tau_mul_self : tau * tau = 1 := eq_one_of_mat t1_sq

theorem tau_ne_alpha : tau ≠ alpha := fun h => t1_ne_al (congrArg mat h)

theorem tau_comm_alpha : tau * alpha = alpha * tau := Units.ext (Subtype.ext t1_al)

theorem tau_alpha_orbit : BabyOrbit 1 tau alpha := by
  refine babyOrbit_one_of ?_ ?_
  · show stripMat Seven.t1 * stripMat Seven.al * (stripMat Seven.t1 * stripMat Seven.al) = 1
    calc stripMat Seven.t1 * stripMat Seven.al * (stripMat Seven.t1 * stripMat Seven.al)
        = stripMat Seven.t1 * (stripMat Seven.al * stripMat Seven.t1) * stripMat Seven.al := by
          simp only [mul_assoc]
      _ = stripMat Seven.t1 * stripMat Seven.t1 * (stripMat Seven.al * stripMat Seven.al) := by
          rw [← t1_al]
          simp only [mul_assoc]
      _ = 1 := by rw [t1_sq, al_sq, one_mul]
  · show (stripMat Seven.t1 * stripMat Seven.al - 1).rank = 2158
    rw [t1_al]
    exact al_t1_rank

theorem tau_sFour_orbit : BabyOrbit 3 tau sFour := by
  have hm : mat ((tau * sFour) ^ 2) = (stripMat Seven.t1 * stripMat SevenLocal.s4) ^ 2 := by
    rw [mat_sq, pow_two]
    rfl
  refine babyOrbit_three_of ?_ ?_ <;> rw [hm]
  · rw [← pow_add]
    exact t1s4_pow
  · exact t1s4_rank

theorem pp_babyInv : BabyInv 0 pp := by
  rw [pp, babyInv_conj_iff]
  exact tau_babyInv

end Model

end CFSGOutside.HallPaige.B
