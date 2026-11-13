import CFSGOutside.Corpus.HallPaige.J4
import CFSGOutside.HallPaige.Sporadic.F2Packed

/-!
# Packed `𝔽₂`-linear algebra in dimension 112 for `J₄`

Row vectors of `𝔽₂¹¹²` are natural numbers (bit `j` is coordinate `j`) and matrices are lists of
their rows. `vmL R x` is the row vector `x ᵥ* R` (the xor of the rows of `R` selected by the bits
of `x`) and `mmL R S` the product `R * S`; both are written with `List.rec` so that the kernel
evaluates them quickly. `spanL bs` is the subspace spanned by a list of packed vectors; `red bs v`
reduces `v` by `bs`, and `red bs v = 0` shows `v ∈ spanL bs`. A list in reduced echelon form
(`rrefB`) is linearly independent, which gives the dimension of `spanL bs`.

The group `J` acts on subspaces of row vectors by `g • S = S ᵥ* g⁻¹`; `Cert g R` says that the
matrix of `g` is the packed matrix `R`.
-/

namespace CFSGOutside.HallPaige.J4

open CFSGOutside.Corpus.J4 CFSGOutside.HallPaige.F2 Matrix

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-! ### Packed products -/

/-- `vmL R x = x ᵥ* R`, packed. -/
def vmL (R : List ℕ) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun r _ ih x => (cond (x.testBit 0) r 0) ^^^ ih (x / 2)) R x

theorem vmL_cons (r : ℕ) (R : List ℕ) (x : ℕ) :
    vmL (r :: R) x = (cond (x.testBit 0) r 0) ^^^ vmL R (x / 2) := rfl

theorem b2z_vmL (R : List ℕ) (x j : ℕ) :
    b2z ((vmL R x).testBit j) =
      ∑ i ∈ Finset.range R.length, b2z (x.testBit i) * b2z ((R.getD i 0).testBit j) := by
  induction R generalizing x with
  | nil => show b2z ((0 : ℕ).testBit j) = _; simp [b2z]
  | cons r R ih =>
    rw [vmL_cons, Nat.testBit_xor, b2z_xor, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [Nat.testBit_div_two, List.getD_cons_succ]
    · rw [List.getD_cons_zero]
      cases x.testBit 0 <;> simp [b2z]

theorem vecOf_vmL (R : List ℕ) (hR : R.length = 112) (x : ℕ) :
    vecOf 112 (vmL R x) = vecOf 112 x ᵥ* matOf 112 R := by
  funext j
  simp only [vecOf, Matrix.vecMul, dotProduct, matOf, Matrix.of_apply]
  rw [b2z_vmL, hR]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => b2z (x.testBit i) * b2z ((R.getD i 0).testBit (j : ℕ))) 112).symm

theorem vmL_zero (S : List ℕ) : vmL S 0 = 0 := by
  induction S with
  | nil => rfl
  | cons s S ih => rw [vmL_cons]; simp [ih]

/-- Packed matrix product. -/
def mmL (R S : List ℕ) : List ℕ := R.map (vmL S)

theorem length_mmL (R S : List ℕ) : (mmL R S).length = R.length := List.length_map _

theorem getD_mmL (R S : List ℕ) (i : ℕ) : (mmL R S).getD i 0 = vmL S (R.getD i 0) := by
  have h := Option.getD_map (vmL S) 0 R[i]?
  rw [vmL_zero] at h
  rw [mmL, List.getD_eq_getElem?_getD, List.getElem?_map, h, ← List.getD_eq_getElem?_getD]

theorem matOf_mmL (R S : List ℕ) (hS : S.length = 112) :
    matOf 112 (mmL R S) = matOf 112 R * matOf 112 S := by
  ext i k
  have := congrFun (vecOf_vmL S hS (R.getD i 0)) k
  simp only [vecOf, Matrix.vecMul, dotProduct, matOf, Matrix.of_apply] at this
  simp only [matOf, Matrix.of_apply, Matrix.mul_apply]
  rw [getD_mmL]
  exact this

theorem length_idm : (idm 112).length = 112 := by simp [idm]

/-! ### Spans, reduction and echelon form -/

/-- The row vectors of `𝔽₂¹¹²`. -/
abbrev V := Fin 112 → ZMod 2

/-- The span of a list of packed vectors. -/
def spanL (bs : List ℕ) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range fun i : Fin bs.length => vecOf 112 (bs.getD i 0))

theorem mem_spanL {bs : List ℕ} {b : ℕ} (hb : b ∈ bs) : vecOf 112 b ∈ spanL bs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  apply Submodule.subset_span
  refine ⟨⟨i, hi⟩, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi]

/-- The lowest set bit of `b`. -/
def lowbit (b : ℕ) : ℕ := b ^^^ (b &&& (b - 1))

/-- Reduction of `v` by the list `bs`. -/
def red (bs : List ℕ) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun v => v)
    (fun b _ ih v => ih (if v &&& lowbit b = 0 then v else v ^^^ b)) bs v

theorem red_cons (b : ℕ) (bs : List ℕ) (v : ℕ) :
    red (b :: bs) v = red bs (if v &&& lowbit b = 0 then v else v ^^^ b) := rfl

theorem vecOf_xor_red_mem (S : Submodule (ZMod 2) V) (bs : List ℕ)
    (hS : ∀ b ∈ bs, vecOf 112 b ∈ S) (v : ℕ) : vecOf 112 (v ^^^ red bs v) ∈ S := by
  induction bs generalizing v with
  | nil => show vecOf 112 (v ^^^ v) ∈ S; rw [Nat.xor_self, vecOf_zero]; exact S.zero_mem
  | cons b bs ih =>
    rw [red_cons]
    set v' := if v &&& lowbit b = 0 then v else v ^^^ b with hv'
    have key : v ^^^ red bs v' = (v ^^^ v') ^^^ (v' ^^^ red bs v') := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc v', Nat.xor_self, Nat.zero_xor]
    rw [key, ← vecOf_add]
    refine S.add_mem ?_ (ih (fun c hc => hS c (List.mem_cons_of_mem _ hc)) v')
    rw [hv']
    split_ifs
    · rw [Nat.xor_self, vecOf_zero]; exact S.zero_mem
    · rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]; exact hS b List.mem_cons_self

theorem mem_spanL_of_red {bs : List ℕ} {v : ℕ} (h : red bs v = 0) : vecOf 112 v ∈ spanL bs := by
  have := vecOf_xor_red_mem (spanL bs) bs (fun b hb => mem_spanL hb) v
  rwa [h, Nat.xor_zero] at this

/-- Reduced echelon form with pivots `ps`. -/
def rrefB (bs ps : List ℕ) : Bool :=
  (List.range bs.length).all fun i => decide (ps.getD i 0 < 112) &&
    (List.range bs.length).all fun j => (bs.getD j 0).testBit (ps.getD i 0) == decide (i = j)

theorem linearIndependent_of_rrefB {bs ps : List ℕ} (h : rrefB bs ps = true) :
    LinearIndependent (ZMod 2) (fun i : Fin bs.length => vecOf 112 (bs.getD i 0)) := by
  simp only [rrefB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  refine (Fintype.linearIndependent_iff (R := ZMod 2) (M := Fin 112 → ZMod 2)
    (v := fun i : Fin bs.length => vecOf 112 (bs.getD i 0))).2 ?_
  intro g hg i
  have h1 := congrFun hg ⟨ps.getD i 0, (h i i.2).1⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, vecOf] at h1
  rw [Finset.sum_eq_single i] at h1
  · rw [(h i i.2).2 i i.2] at h1
    simpa [b2z] using h1
  · intro j _ hji
    rw [(h i i.2).2 j j.2]
    have : (i : ℕ) ≠ j := fun e => hji (Fin.ext e).symm
    simp [b2z, this]
  · simp

theorem finrank_spanL_le (bs : List ℕ) : Module.finrank (ZMod 2) (spanL bs) ≤ bs.length := by
  have := finrank_range_le_card (R := ZMod 2) (fun i : Fin bs.length => vecOf 112 (bs.getD i 0))
  unfold spanL
  simpa [Set.finrank] using this

theorem finrank_spanL {bs ps : List ℕ} (h : rrefB bs ps = true) :
    Module.finrank (ZMod 2) (spanL bs) = bs.length := by
  rw [spanL, finrank_span_eq_card (linearIndependent_of_rrefB h), Fintype.card_fin]

/-! ### Matrices of group elements -/

/-- The matrix of an element of `J`. -/
def Mx (g : J) : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))

theorem Mx_mul (g h : J) : Mx (g * h) = Mx g * Mx h := rfl

theorem Mx_one : Mx 1 = 1 := rfl

theorem Mx_inv_mul (g : J) : Mx g⁻¹ * Mx g = 1 := by
  rw [← Mx_mul, inv_mul_cancel, Mx_one]

theorem Mx_injective : Function.Injective Mx := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  exact e

/-- The matrix of `g : GL` is the packed matrix `R`. -/
def CertG (g : GL (Fin 112) (ZMod 2)) (R : List ℕ) : Prop :=
  ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = matOf 112 R ∧
    R.length = 112

/-- The matrix of `g : J` is the packed matrix `R`. -/
def Cert (g : J) (R : List ℕ) : Prop := CertG (g : GL (Fin 112) (ZMod 2)) R

theorem CertG.mul {g h : GL (Fin 112) (ZMod 2)} {R S T : List ℕ} (hg : CertG g R) (hh : CertG h S)
    (e : mmL R S = T) : CertG (g * h) T := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, hg.1, hh.1, ← matOf_mmL R S hh.2, e]
  · rw [← e, length_mmL, hg.2]

theorem CertG.inv {g : GL (Fin 112) (ZMod 2)} {R S : List ℕ} (hg : CertG g R)
    (e : mmL R S = idm 112) (hS : S.length = 112) : CertG g⁻¹ S := by
  refine ⟨?_, hS⟩
  have h1 : (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) * matOf 112 S = 1 := by
    rw [hg.1, ← matOf_mmL R S hS, e, matOf_idm]
  calc ((g⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))
      = ((g⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) *
          ((g : Matrix (Fin 112) (Fin 112) (ZMod 2)) * matOf 112 S) := by rw [h1, Matrix.mul_one]
    _ = matOf 112 S := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem CertG.one : CertG 1 (idm 112) := ⟨by rw [matOf_idm]; rfl, length_idm⟩

theorem Cert.mul {g h : J} {R S T : List ℕ} (hg : Cert g R) (hh : Cert h S)
    (e : mmL R S = T) : Cert (g * h) T := CertG.mul hg hh e

theorem Cert.inv {g : J} {R S : List ℕ} (hg : Cert g R) (e : mmL R S = idm 112)
    (hS : S.length = 112) : Cert g⁻¹ S := CertG.inv hg e hS

theorem Cert.mx_eq {g : J} {R : List ℕ} (hg : Cert g R) : Mx g = matOf 112 R := hg.1

theorem Cert.vec {g : J} {R : List ℕ} (hg : Cert g R) (x : ℕ) :
    vecOf 112 x ᵥ* Mx g = vecOf 112 (vmL R x) := by
  rw [Cert.mx_eq hg, vecOf_vmL R hg.2]

/-! ### Words -/

/-- The product of the letters `f l` of a word. -/
def wordE (f : ℕ → J) (w : List ℕ) : J := (w.map f).prod

theorem wordE_nil (f : ℕ → J) : wordE f [] = 1 := rfl

theorem wordE_cons (f : ℕ → J) (l : ℕ) (w : List ℕ) : wordE f (l :: w) = f l * wordE f w := by
  simp [wordE]

theorem wordE_append (f : ℕ → J) (u w : List ℕ) : wordE f (u ++ w) = wordE f u * wordE f w := by
  simp [wordE]

theorem wordE_mem (f : ℕ → J) (K : Subgroup J) (w : List ℕ) (h : ∀ l ∈ w, f l ∈ K) :
    wordE f w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [wordE_cons]
    exact K.mul_mem (h l List.mem_cons_self) (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

/-- Packed matrix of a word. -/
def wordM (L : ℕ → List ℕ) (w : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) (idm 112) (fun l _ ih => mmL (L l) ih) w

theorem cert_wordE (f : ℕ → J) (L : ℕ → List ℕ) (w : List ℕ) (h : ∀ l ∈ w, Cert (f l) (L l)) :
    Cert (wordE f w) (wordM L w) := by
  induction w with
  | nil => exact CertG.one
  | cons l w ih =>
    rw [wordE_cons]
    exact Cert.mul (h l List.mem_cons_self) (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      rfl

/-- Packed image of a vector under a word, letter by letter. -/
def applyW (L : ℕ → List ℕ) (w : List ℕ) (v : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun v => v) (fun l _ ih v => ih (vmL (L l) v)) w v

theorem vec_applyW (f : ℕ → J) (L : ℕ → List ℕ) (w : List ℕ) (h : ∀ l ∈ w, Cert (f l) (L l))
    (v : ℕ) : vecOf 112 v ᵥ* Mx (wordE f w) = vecOf 112 (applyW L w v) := by
  induction w generalizing v with
  | nil => rw [wordE_nil, Mx_one, Matrix.vecMul_one]; rfl
  | cons l w ih =>
    rw [wordE_cons, Mx_mul, ← Matrix.vecMul_vecMul, Cert.vec (h l List.mem_cons_self),
      ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    rfl

/-! ### The action on subspaces -/

/-- `x ↦ x ᵥ* g⁻¹`. -/
def LM (g : J) : V →ₗ[ZMod 2] V := (Mx g⁻¹).vecMulLinear

instance subAct : MulAction J (Submodule (ZMod 2) V) where
  smul g S := S.map (LM g)
  one_smul S := by
    show S.map (LM 1) = S
    have : LM 1 = LinearMap.id := LinearMap.ext fun x =>
      show x ᵥ* Mx 1⁻¹ = x by rw [inv_one, Mx_one, Matrix.vecMul_one]
    rw [this, Submodule.map_id]
  mul_smul g h S := by
    show S.map (LM (g * h)) = (S.map (LM h)).map (LM g)
    have : LM (g * h) = (LM g).comp (LM h) := by
      apply LinearMap.ext
      intro x
      simp only [LM, LinearMap.comp_apply, Matrix.vecMulLinear_apply]
      rw [_root_.mul_inv_rev, Mx_mul, Matrix.vecMul_vecMul]
    rw [this, Submodule.map_comp]

theorem smul_def (g : J) (S : Submodule (ZMod 2) V) : g • S = S.map (LM g) := rfl

theorem finrank_smul (g : J) (S : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) ↥(g • S) = Module.finrank (ZMod 2) S := by
  apply le_antisymm (Submodule.finrank_map_le _ _)
  calc Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) ↥(g⁻¹ • g • S) := by
        rw [inv_smul_smul]
    _ ≤ _ := Submodule.finrank_map_le _ _

/-- The image of `spanL bs` under `g` lies in `spanL tbs` if every image vector, computed by
`φ`, reduces to `0`. -/
theorem smul_spanL_le (g : J) (φ : ℕ → ℕ) (hφ : ∀ x, vecOf 112 x ᵥ* Mx g⁻¹ = vecOf 112 (φ x))
    (bs tbs : List ℕ) (h : bs.all (fun b => red tbs (φ b) == 0) = true) :
    g • spanL bs ≤ spanL tbs := by
  rw [smul_def, spanL, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hb : bs.getD i 0 ∈ bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2]
    exact List.getElem_mem _
  rw [List.all_eq_true] at h
  have := h _ hb
  rw [beq_iff_eq] at this
  show vecOf 112 (bs.getD i 0) ᵥ* Mx g⁻¹ ∈ spanL tbs
  rw [hφ]
  exact mem_spanL_of_red this

theorem smul_spanL_eq (g : J) (φ : ℕ → ℕ) (hφ : ∀ x, vecOf 112 x ᵥ* Mx g⁻¹ = vecOf 112 (φ x))
    (bs ps tbs : List ℕ) (hr : rrefB bs ps = true) (hl : tbs.length ≤ bs.length)
    (h : bs.all (fun b => red tbs (φ b) == 0) = true) :
    g • spanL bs = spanL tbs := by
  have hle := smul_spanL_le g φ hφ bs tbs h
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply le_antisymm (Submodule.finrank_mono hle)
  rw [finrank_smul, finrank_spanL hr]
  exact (finrank_spanL_le tbs).trans hl

/-- Matrix form: `Cert g⁻¹ R` gives the image vectors as `vmL R`. -/
theorem smul_spanL_eq_cert {g : J} {R : List ℕ} (hg : Cert g⁻¹ R)
    (bs ps tbs : List ℕ) (hr : rrefB bs ps = true) (hl : tbs.length ≤ bs.length)
    (h : bs.all (fun b => red tbs (vmL R b) == 0) = true) :
    g • spanL bs = spanL tbs :=
  smul_spanL_eq g (vmL R) (fun x => Cert.vec hg x) bs ps tbs hr hl h

/-- Word form: the image of `spanL bs` under `(wordE f w)⁻¹`, letter by letter. -/
theorem inv_smul_spanL_eq_word (f : ℕ → J) (L : ℕ → List ℕ) (w : List ℕ)
    (hw : ∀ l ∈ w, Cert (f l) (L l))
    (bs ps tbs : List ℕ) (hr : rrefB bs ps = true) (hl : tbs.length ≤ bs.length)
    (h : bs.all (fun b => red tbs (applyW L w b) == 0) = true) :
    (wordE f w)⁻¹ • spanL bs = spanL tbs :=
  smul_spanL_eq _ (applyW L w) (fun x => by rw [inv_inv, vec_applyW f L w hw]) bs ps tbs hr hl h

end

end CFSGOutside.HallPaige.J4
