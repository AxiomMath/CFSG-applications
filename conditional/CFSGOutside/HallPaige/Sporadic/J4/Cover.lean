import CFSGOutside.HallPaige.Sporadic.J4.All
import CFSGOutside.HallPaige.Sporadic.J4.LtCert
import CFSGOutside.HallPaige.Sporadic.Ly.Criterion
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein

/-!
# The Wilcox criterion for the matrix model of `J₄`

`H` is the stabilizer of the `10`-dimensional subspace `W = S 0` (invariant under the centralizer
of the involution `aI`). From the corpus decomposition `J = ⋃ Hj (pathElt pℓ)⁻¹ Hj` and
`Hj = Stab_J(v)`, the kernel-checked Schreier forests show that every `g • W` lies in the
`H`-orbit of `r i • W` for one of `ncand` explicit words `r i`, and each `H r i H` has a
kernel-checked triangle witness.
-/

namespace CFSGOutside.HallPaige.J4

open CFSGOutside.Corpus.J4 CFSGOutside.HallPaige.F2 Matrix MulAction DoubleCoset

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

set_option maxRecDepth 100000

/-! ### Basic facts from the checks -/

theorem allR_spec {lo hi : ℕ} {f : ℕ → Bool} (h : allR lo hi f = true) {m : ℕ} (h1 : lo ≤ m)
    (h2 : m < hi) : f m = true := by
  rw [allR, List.all_eq_true] at h
  exact h m (List.mem_range'_1.2 ⟨h1, by omega⟩)

/-- The subspaces. -/
def S (m : ℕ) : Submodule (ZMod 2) V := spanL (sb m)

/-- `W`. -/
def W : Submodule (ZMod 2) V := S 0

/-- The subgroup `H`: the stabilizer of `W`. -/
def H : Subgroup J := stabilizer J W

theorem length_sb (m : ℕ) : (sb m).length = 10 := length_unpack _ _ _

theorem length_qb (c : ℕ) : (qb c).length = 10 := length_unpack _ _ _

theorem rref_sb {m : ℕ} (hm : m < 1771) : rrefB (sb m) (spv m) = true :=
  allR_spec rref_c (Nat.zero_le _) hm

theorem word_cert (w : List ℕ) (hw : ∀ l ∈ w, l < 43) :
    ∀ l ∈ w, Cert (lt l) (lm l) := fun l hl => cert_lt l (hw l hl)

/-- The image of `S m` under `(wordE lt w)⁻¹`. -/
theorem inv_smul_S (w : List ℕ) (hw : ∀ l ∈ w, l < 43) {m : ℕ} (hm : m < 1771) (tbs : List ℕ)
    (htl : tbs.length ≤ 10) (h : wImgChk w (sb m) tbs = true) :
    (wordE lt w)⁻¹ • S m = spanL tbs :=
  inv_smul_spanL_eq_word lt lm w (word_cert w hw) (sb m) (spv m) tbs (rref_sb hm)
    (by rw [length_sb]; exact htl) h

theorem inv_smul_S_cert {g : J} {R : List ℕ} (hg : Cert g R) {m : ℕ} (hm : m < 1771)
    (tbs : List ℕ) (htl : tbs.length ≤ 10) (h : imgChk R (sb m) tbs = true) :
    g⁻¹ • S m = spanL tbs :=
  smul_spanL_eq_cert (g := g⁻¹) (by rw [inv_inv]; exact hg) (sb m) (spv m) tbs (rref_sb hm)
    (by rw [length_sb]; exact htl) h

/-! ### The `Hj`-orbit of `W` -/

theorem tab_spec {k : ℕ} (hk : k < 3) {m : ℕ} (hm : m < 1771) :
    tab k m < 1771 ∧ (xJ k)⁻¹ • S m = S (tab k m) := by
  have h := allR_spec (tab_all k hk) (Nat.zero_le _) hm
  simp only [chkTab, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have hc : Cert (xJ k) (lm k) := by
    have := cert_lt0 k (by omega)
    interval_cases k <;> exact this
  exact inv_smul_S_cert hc hm _ (le_of_eq (length_sb _)) h.2

theorem tinv_spec {k : ℕ} (hk : k < 3) {m : ℕ} (hm : m < 1771) :
    tinv k m < 1771 ∧ xJ k • S m = S (tinv k m) := by
  have h := allR_spec (tinv_all k hk) (Nat.zero_le _) hm
  simp only [chkTinv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  have := (tab_spec hk h.1).2
  rw [h.2] at this
  rw [← this, smul_inv_smul]

theorem orbit_step (x : J) (hx : x ∈ Hj) :
    ∀ m < 1771, ∃ m' < 1771, x⁻¹ • S m = S m' := by
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    intro m hm
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, (tab_spec (k := 0) (by norm_num) hm).1, (tab_spec (by norm_num) hm).2⟩
    · exact ⟨_, (tab_spec (k := 1) (by norm_num) hm).1, (tab_spec (by norm_num) hm).2⟩
    · exact ⟨_, (tab_spec (k := 2) (by norm_num) hm).1, (tab_spec (by norm_num) hm).2⟩
  | inv_mem x hx =>
    intro m hm
    rw [inv_inv]
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, (tinv_spec (k := 0) (by norm_num) hm).1, (tinv_spec (by norm_num) hm).2⟩
    · exact ⟨_, (tinv_spec (k := 1) (by norm_num) hm).1, (tinv_spec (by norm_num) hm).2⟩
    · exact ⟨_, (tinv_spec (k := 2) (by norm_num) hm).1, (tinv_spec (by norm_num) hm).2⟩
  | one => intro m hm; exact ⟨m, hm, by rw [inv_one, one_smul]⟩
  | mul x y _ _ ihx ihy =>
    intro m hm
    obtain ⟨m1, hm1, e1⟩ := ihx m hm
    obtain ⟨m2, hm2, e2⟩ := ihy m1 hm1
    exact ⟨m2, hm2, by rw [_root_.mul_inv_rev, mul_smul, e1, e2]⟩

theorem orbit_W (x : J) (hx : x ∈ Hj) : ∃ m < 1771, x⁻¹ • W = S m :=
  orbit_step x hx 0 (by norm_num)

/-! ### Words -/

theorem letter_eq (l : ℕ) : letterElt l = lt (if l = 1 then 6 else 7) := by
  by_cases hl : l = 1
  · rw [if_pos hl, lt_eq_lt0 6 (by norm_num), letterElt, if_pos hl]; rfl
  · rw [if_neg hl, lt_eq_lt0 7 (by norm_num), letterElt, if_neg hl]; rfl

theorem letter_inv (l : ℕ) : (letterElt l)⁻¹ = lt (if l = 1 then 6 else 8) := by
  by_cases hl : l = 1
  · rw [if_pos hl, lt_eq_lt0 6 (by norm_num), letterElt, if_pos hl]; exact a_inv
  · rw [if_neg hl, lt_eq_lt0 8 (by norm_num), letterElt, if_neg hl]; rfl

theorem lt_inv3 (l : ℕ) (hl : l < 3) : (lt l)⁻¹ = lt (l + 3) := by
  rw [lt_eq_lt0 l (by omega), lt_eq_lt0 (l + 3) (by omega)]
  interval_cases l <;> rfl

theorem pathElt_eq (p : List ℕ) : pathElt p = wordE lt (pathW p) := by
  induction p with
  | nil => rfl
  | cons l p ih =>
    rw [pathElt, ih, letter_eq]
    simp only [pathW, List.map_cons, wordE_cons]

theorem pathElt_inv_eq (p : List ℕ) : (pathElt p)⁻¹ = wordE lt (pathInvW p) := by
  induction p with
  | nil => simp [pathElt, pathInvW, wordE]
  | cons l p ih =>
    rw [pathElt, _root_.mul_inv_rev, ih, letter_inv]
    simp only [pathInvW, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      wordE_append, wordE_cons, wordE_nil, mul_one]

theorem word_inv_eq (w : List ℕ) (hw : ∀ l ∈ w, l < 3) : (wordE lt w)⁻¹ = wordE lt (invW w) := by
  induction w with
  | nil => simp [wordE, invW]
  | cons l w ih =>
    have hl := hw l List.mem_cons_self
    rw [wordE_cons, _root_.mul_inv_rev, ih (fun l' h' => hw l' (List.mem_cons_of_mem _ h')),
      lt_inv3 l hl]
    simp only [invW, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      wordE_append, wordE_cons, wordE_nil, mul_one, if_pos hl]

theorem pathW_lt (p : List ℕ) : ∀ l ∈ pathW p, l < 43 := by
  intro l hl
  simp only [pathW, List.mem_map] at hl
  obtain ⟨x, _, rfl⟩ := hl
  split_ifs <;> norm_num

theorem pathInvW_lt (p : List ℕ) : ∀ l ∈ pathInvW p, l < 43 := by
  intro l hl
  simp only [pathInvW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨x, _, rfl⟩ := hl
  split_ifs <;> norm_num

theorem invW_lt (w : List ℕ) (hw : ∀ l ∈ w, l < 3) : ∀ l ∈ invW w, l < 43 := by
  intro l hl
  simp only [invW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  have := hw x hx
  split_ifs <;> omega

/-- The words `uwL j` (`j ∈ needJ`) satisfy `(wordE lt (uwL j))⁻¹ • W = S j`. -/
theorem u_spec {j : ℕ} (hj : j ∈ needJ) :
    (∀ l ∈ uwL.getD j [], l < 3) ∧ (wordE lt (uwL.getD j []))⁻¹ • W = S j := by
  have h := List.all_eq_true.1 u_c j hj
  simp only [chkU, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  exact inv_smul_S _ (fun l hl => by have := h.2 l hl; omega) (by norm_num) _
    (le_of_eq (length_sb _)) h.1

/-! ### `H` -/

theorem mem_H_iff (g : J) : g ∈ H ↔ g • W = W := mem_stabilizer_iff

theorem pool_mem (j : ℕ) (hj : j < 17) : poolE j ∈ H := by
  have h := List.all_eq_true.1 pool_c j (List.mem_range.2 hj)
  have e := inv_smul_S_cert (g := (poolE j)⁻¹) (R := lm (26 + j))
    (by rw [← lt_poolI j hj]; exact cert_lt _ (by omega)) (m := 0) (by norm_num) (sb 0)
    (le_of_eq (length_sb _)) h
  rw [inv_inv] at e
  exact (mem_H_iff _).2 e

theorem lt_mem_H {l : ℕ} (h1 : 9 ≤ l) (h2 : l < 43) : lt l ∈ H := by
  by_cases h : l < 26
  · obtain ⟨j, rfl⟩ : ∃ j, l = 9 + j := ⟨l - 9, by omega⟩
    rw [lt_pool j (by omega)]
    exact pool_mem j (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, l = 26 + j := ⟨l - 26, by omega⟩
    rw [lt_poolI j (by omega)]
    exact H.inv_mem (pool_mem j (by omega))

theorem wordE_mem_H (w : List ℕ) (hw : w.all poolL = true) : wordE lt w ∈ H := by
  apply wordE_mem
  intro l hl
  have := List.all_eq_true.1 hw l hl
  simp only [poolL, Bool.and_eq_true, decide_eq_true_eq] at this
  exact lt_mem_H this.1 this.2

/-! ### Stage 1: the double cosets `Hj g H` -/

def sig (f j : ℕ) : J := wordE lt (gw f j)

theorem sig_cert {f : ℕ} (hf : f < 43) {j : ℕ} (hj : j < 7) : Cert (sig f j) (gm f j) := by
  have h := gen_all f hf j hj
  simp only [chkGen, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [← h.2]
  exact cert_wordE lt lm _ (fun l hl => cert_lt l (by have := h.1 l hl; omega))

theorem for_spec {f : ℕ} (hf : f < 43) {m : ℕ} (hm : m < 1771) (hr : fgen f m ≠ 7) :
    fgen f m < 7 ∧ ftgt f m < 1771 ∧ (sig f (fgen f m))⁻¹ • S m = S (ftgt f m) := by
  have h := allR_spec (for_all f hf) (Nat.zero_le _) hm
  simp only [chkFor, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h hr
  · exact ⟨h1, h2, inv_smul_S_cert (sig_cert hf h1) hm _ (le_of_eq (length_sb _)) h3⟩

theorem reach_spec {f : ℕ} (hf : f < 43) {m : ℕ} (hm : m < 1771) :
    ∃ n, n ≤ 12 ∧ reach f n m = true := ⟨12, le_rfl, allR_spec (reach_all f hf) (Nat.zero_le _) hm⟩

theorem toVecD_eq (x : ℕ) : toVecD 112 x = vecOf 112 x := by
  funext j
  simp only [toVecD, vecOf, b2z]

theorem qv_spec (l : ℕ) :
    vecOf 112 rootBits ᵥ* Mx (pathElt (repPaths.getD l []))⁻¹ = vecOf 112 (qv l) := by
  rw [pathElt_inv_eq, qv]
  exact vec_applyW lt lm _ (word_cert _ (pathInvW_lt _)) rootBits

theorem conj_mem_of_fix [hS : Corpus.J4.Stab] (P σ : J) (q : ℕ)
    (hq : vecOf 112 rootBits ᵥ* Mx P⁻¹ = vecOf 112 q) (hσ : vecOf 112 q ᵥ* Mx σ = vecOf 112 q) :
    P⁻¹ * σ * P ∈ Hj := by
  have hv : vecOf 112 rootBits ᵥ* Mx (P⁻¹ * σ * P) = vecOf 112 rootBits := by
    rw [Mx_mul, Mx_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hq, hσ, ← hq,
      Matrix.vecMul_vecMul, Mx_inv_mul, Matrix.vecMul_one]
  rw [← hS.stabilizer_v_eq_Hj]
  apply (Subgroup.inv_mem_iff _).1
  rw [mem_stabilizer_iff]
  show toRow (ofRow v ᵥ* ((((P⁻¹ * σ * P)⁻¹)⁻¹ : J) : GL (Fin 112) (ZMod 2))) = v
  rw [inv_inv]
  show toRow (toVecD 112 rootBits ᵥ* Mx (P⁻¹ * σ * P)) = toRow (toVecD 112 rootBits)
  rw [toVecD_eq, hv]

theorem conj_mem_Hj [Corpus.J4.Stab] {l : ℕ} (hl : l < 7) {j : ℕ} (hj : j < 7) :
    (pathElt (repPaths.getD l []))⁻¹ * sig l j * pathElt (repPaths.getD l []) ∈ Hj := by
  have hc := sig_cert (f := l) (by omega) hj
  have h := stab_all l hl j hj
  simp only [chkStab, beq_iff_eq] at h
  exact conj_mem_of_fix _ _ (qv l) (qv_spec l) (by rw [Cert.vec hc, h])

theorem stage1 [Corpus.J4.Stab] {l : ℕ} (hl : l < 7) :
    ∀ n m, m < 1771 → reach l n m = true → ∀ x ∈ Hj, ∃ x' ∈ Hj, ∃ r < 1771, fgen l r = 7 ∧
      (x * (pathElt (repPaths.getD l []))⁻¹) • S m =
        (x' * (pathElt (repPaths.getD l []))⁻¹) • S r := by
  intro n
  induction n with
  | zero =>
    intro m hm hr x hx
    simp only [reach, beq_iff_eq] at hr
    exact ⟨x, hx, m, hm, hr, rfl⟩
  | succ n ih =>
    intro m hm hr x hx
    by_cases h7 : fgen l m = 7
    · exact ⟨x, hx, m, hm, h7, rfl⟩
    simp only [reach, Bool.or_eq_true, beq_iff_eq, h7, false_or] at hr
    obtain ⟨hg, ht, e⟩ := for_spec (f := l) (by omega) hm h7
    obtain ⟨x', hx'', r, hr', hr7, e2⟩ := ih (ftgt l m) ht hr _ (Hj.mul_mem hx (conj_mem_Hj hl hg))
    refine ⟨x', hx'', r, hr', hr7, ?_⟩
    rw [← e2, ← e, smul_smul]
    exact congrArg (fun g => g • S m) (by group)

/-! ### Stage 2: the double cosets `H g H` -/

theorem getD_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem misc_spec : ncand = candI.length ∧ clsL.length = 36 ∧ clsRep.length = 36 ∧
    (∀ i < ncand, candC.getD i 0 < 36 ∧ candI.getD i 0 < 1771 ∧ candI.getD i 0 ∈ needJ ∧
      clsRep.getD (candC.getD i 0) 0 ∈ needJ) ∧
    (∀ c < 36, clsL.getD c 0 < 7 ∧ clsRep.getD c 0 < 1771) := by
  have h := misc_c
  unfold chkMisc at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨h, -⟩ := h
  obtain ⟨h, hE⟩ := h
  obtain ⟨h, hD⟩ := h
  obtain ⟨h, hC⟩ := h
  obtain ⟨hA, hB⟩ := h
  refine ⟨hC.symm, hA, hB, fun i hi => ?_, fun c hc => hD c hc⟩
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := hE i hi
  exact ⟨e1, e2, by simpa using e3, by simpa using e4⟩

theorem cls_spec {l : ℕ} (hl : l < 7) {r : ℕ} (hr : r < 1771) (h7 : fgen l r = 7) :
    ∃ c < 36, clsL.getD c 0 = l ∧ clsRep.getD c 0 = r := by
  have h := cls_all l hl
  simp only [chkCls, beq_iff_eq] at h
  have hr' : r ∈ rootsOf l := by
    simp only [rootsOf, List.mem_filter, List.mem_range, beq_iff_eq]; exact ⟨hr, h7⟩
  rw [h] at hr'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
  rw [List.mem_filter, beq_iff_eq] at hp
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hp.1
  rw [List.getElem_zip] at e
  subst e
  have hm := misc_spec
  have hi1 : i < clsL.length := by rw [List.length_zip] at hi; omega
  have hi2 : i < clsRep.length := by rw [List.length_zip] at hi; omega
  refine ⟨i, by rw [hm.2.1] at hi1; exact hi1, ?_, ?_⟩
  · rw [getD_of_lt hi1]; exact hp.2
  · rw [getD_of_lt hi2]

def Q (c : ℕ) : Submodule (ZMod 2) V := spanL (qb c)

theorem q_spec {c : ℕ} (hc : c < 36) (hr : clsRep.getD c 0 < 1771) :
    (pathElt (repPaths.getD (clsL.getD c 0) []))⁻¹ • S (clsRep.getD c 0) = Q c ∧
      ∀ j < 7, sig (7 + c) j • Q c = Q c := by
  have h := q_all c hc
  simp only [chkQ, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hr1, hr2⟩, hr3⟩ := h
  refine ⟨?_, fun j hj => ?_⟩
  · have := inv_smul_S (pathW (repPaths.getD (clsL.getD c 0) [])) (pathW_lt _) hr (qb c)
      (le_of_eq (length_qb _)) hr2
    rw [← pathElt_eq] at this
    exact this
  · have e := smul_spanL_eq_cert (g := (sig (7 + c) j)⁻¹)
      (by rw [inv_inv]; exact sig_cert (by omega) hj) (qb c) (qp c) (qb c) hr1 le_rfl (hr3 j hj)
    exact (inv_smul_eq_iff.1 e).symm

theorem stage2 {c : ℕ} (hc : c < 36) (hr : clsRep.getD c 0 < 1771) :
    ∀ n m, m < 1771 → reach (7 + c) n m = true → ∀ x : J, x⁻¹ • W = S m →
      ∃ i < 1771, fgen (7 + c) i = 7 ∧ ∃ x' : J, x'⁻¹ • W = S i ∧ x • Q c = x' • Q c := by
  intro n
  induction n with
  | zero =>
    intro m hm hr' x hx
    simp only [reach, beq_iff_eq] at hr'
    exact ⟨m, hm, hr', x, hx, rfl⟩
  | succ n ih =>
    intro m hm hr' x hx
    by_cases h7 : fgen (7 + c) m = 7
    · exact ⟨m, hm, h7, x, hx, rfl⟩
    simp only [reach, Bool.or_eq_true, beq_iff_eq, h7, false_or] at hr'
    obtain ⟨hg, ht, e⟩ := for_spec (f := 7 + c) (by omega) hm h7
    have hx2 : (x * sig (7 + c) (fgen (7 + c) m))⁻¹ • W = S (ftgt (7 + c) m) := by
      rw [_root_.mul_inv_rev, mul_smul, hx, e]
    obtain ⟨i, hi, hi7, x', hx', e2⟩ := ih _ ht hr' _ hx2
    refine ⟨i, hi, hi7, x', hx', ?_⟩
    rw [← e2, mul_smul, (q_spec hc hr).2 _ hg]

/-! ### Candidates -/

def r (i : ℕ) : J := wordE lt (rwOf i)

theorem cand_spec {c : ℕ} (hc : c < 36) {i : ℕ} (hi : i < 1771) (h7 : fgen (7 + c) i = 7) :
    ∃ k < ncand, candC.getD k 0 = c ∧ candI.getD k 0 = i := by
  have h := cand_all c hc
  simp only [chkCand, beq_iff_eq] at h
  have hi' : i ∈ rootsOf (7 + c) := by
    simp only [rootsOf, List.mem_filter, List.mem_range, beq_iff_eq]; exact ⟨hi, h7⟩
  rw [h] at hi'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi'
  rw [List.mem_filter, beq_iff_eq] at hp
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hp.1
  rw [List.getElem_zip] at e
  subst e
  have hm := misc_spec
  have hk1 : k < candC.length := by rw [List.length_zip] at hk; omega
  have hk2 : k < candI.length := by rw [List.length_zip] at hk; omega
  refine ⟨k, by rw [hm.1]; exact hk2, ?_, ?_⟩
  · rw [getD_of_lt hk1]; exact hp.2
  · rw [getD_of_lt hk2]

theorem r_eq (k : ℕ) (hk : k < ncand) :
    r k • W = wordE lt (uwL.getD (candI.getD k 0) []) • Q (candC.getD k 0) := by
  obtain ⟨hc, hi, hj1, hj2⟩ := misc_spec.2.2.2.1 k hk
  have hcl := misc_spec.2.2.2.2 _ hc
  obtain ⟨hu, hus⟩ := u_spec hj2
  simp only [r, rwOf]
  rw [wordE_append, wordE_append, ← pathElt_inv_eq, ← word_inv_eq _ hu, mul_smul,
    mul_smul, hus, (q_spec hc hcl.2).1]

theorem cover [Corpus.J4.Stab] [hC : Corpus.J4.Cover] (g : J) :
    ∃ k < ncand, g • W ∈ orbit H (r k • W) := by
  obtain ⟨l, hl, h₁, hh₁, h₂, hh₂, rfl⟩ := hC.certificate4008.1 g
  obtain ⟨j, hj, ej⟩ := orbit_W h₂⁻¹ (Hj.inv_mem hh₂)
  rw [inv_inv] at ej
  obtain ⟨n, -, hn⟩ := reach_spec (f := l) (by omega) hj
  obtain ⟨x', hx', rr, hrr, hr7, e1⟩ := stage1 hl n j hj hn h₁ hh₁
  obtain ⟨c, hc, hcl, hcr⟩ := cls_spec hl hrr hr7
  have hrc : clsRep.getD c 0 < 1771 := by rw [hcr]; exact hrr
  have hq := (q_spec hc hrc).1
  rw [hcl, hcr] at hq
  obtain ⟨i, hi, e2⟩ := orbit_W x' hx'
  obtain ⟨n2, -, hn2⟩ := reach_spec (f := 7 + c) (by omega) hi
  obtain ⟨i0, hi0, hi07, x'', hx'', e3⟩ := stage2 hc hrc n2 i hi hn2 x' e2
  obtain ⟨k, hk, hkc, hki⟩ := cand_spec hc hi0 hi07
  refine ⟨k, hk, ?_⟩
  have hj1 := (misc_spec.2.2.2.1 k hk).2.2.1
  rw [hki] at hj1
  obtain ⟨-, hu⟩ := u_spec hj1
  have hgW : (h₁ * (pathElt (repPaths.getD l []))⁻¹ * h₂) • W = x'' • Q c := by
    rw [mul_smul, ej, e1, mul_smul, hq, e3]
  have hmem : x'' * (wordE lt (uwL.getD i0 []))⁻¹ ∈ H := by
    rw [mem_H_iff, mul_smul, hu, ← hx'', smul_inv_smul]
  refine ⟨⟨x'' * (wordE lt (uwL.getD i0 []))⁻¹, hmem⟩, ?_⟩
  show (x'' * (wordE lt (uwL.getD i0 []))⁻¹) • r k • W =
    (h₁ * (pathElt (repPaths.getD l []))⁻¹ * h₂) • W
  rw [hgW, r_eq k hk, hkc, hki, smul_smul, inv_mul_cancel_right]

/-! ### Triangle witnesses -/

theorem triWit_r (k : ℕ) (hk : k < ncand) : Ly.TriWit H (r k) := by
  have h := allR_spec wit_all (Nat.zero_le _) (by rw [← ncand_eq]; exact hk)
  simp only [chkWit, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hmc := (misc_spec.2.2.2.1 k hk)
  have hu1 := (u_spec hmc.2.2.1).1
  have hu2 := (u_spec hmc.2.2.2).1
  have hr : ∀ l ∈ rwOf k, l < 43 := by
    intro l hl
    simp only [rwOf, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · have := hu1 l hl; omega
    · exact pathInvW_lt _ l hl
    · exact invW_lt _ hu2 l hl
  have hH : ∀ l ∈ candH.getD k [], l < 43 := fun l hl => by
    have := List.all_eq_true.1 h2 l hl; simp [poolL] at this; omega
  have hK : ∀ l ∈ candK.getD k [], l < 43 := fun l hl => by
    have := List.all_eq_true.1 h3 l hl; simp [poolL] at this; omega
  have hw : ∀ l ∈ fullW k, l < 43 := by
    intro l hl
    simp only [fullW, List.mem_append] at hl
    rcases hl with (((hl | hl) | hl) | hl) | hl
    · exact hr l hl
    · exact hH l hl
    · exact hr l hl
    · exact hK l hl
    · exact hr l hl
  have e := inv_smul_S (fullW k) hw (m := 0) (by norm_num) (sb 0) (le_of_eq (length_sb _)) h1
  have hz : wordE lt (fullW k) ∈ H := by
    rw [← inv_inv (wordE lt (fullW k))]
    exact H.inv_mem ((mem_H_iff _).2 e)
  have hhH : wordE lt (candH.getD k []) ∈ H := wordE_mem_H _ h2
  have hkH : wordE lt (candK.getD k []) ∈ H := wordE_mem_H _ h3
  have hfw : wordE lt (fullW k) = r k * wordE lt (candH.getD k []) * r k *
      wordE lt (candK.getD k []) * r k := by
    simp only [fullW, wordE_append, r]
  rw [hfw] at hz
  refine ⟨r k, wordE lt (candH.getD k []) * r k, rfl, Ly.mk_mul_left_of_mem hhH _, Or.inr ?_⟩
  have e2 : (r k * (wordE lt (candH.getD k []) * r k))⁻¹ = wordE lt (candK.getD k []) * r k *
      (r k * wordE lt (candH.getD k []) * r k * wordE lt (candK.getD k []) * r k)⁻¹ := by group
  rw [e2, Ly.mk_mul_right_of_mem (H.inv_mem hz), Ly.mk_mul_left_of_mem hkH]

/-! ### `H` is proper and good -/

theorem dot_vecOf (x y : ℕ) : vecOf 112 x ⬝ᵥ vecOf 112 y = b2z (par (y &&& x)) := by
  simp only [dotProduct, vecOf, par]
  rw [← sum_b2z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← b2z_and, Nat.testBit_and, Bool.and_comm]

theorem fun_facts : funW < 10 ∧ (∀ x ∈ sb 0, par (funN &&& x) = false) ∧
    par (funN &&& vmL (lm 6) ((sb 0).getD funW 0)) = true := by
  have h := fun_c
  simp only [chkFun, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The functional `x ↦ x ⬝ᵥ vecOf funN`. -/
def phi : V →ₗ[ZMod 2] ZMod 2 where
  toFun x := x ⬝ᵥ vecOf 112 funN
  map_add' x y := add_dotProduct x y _
  map_smul' c x := by simp [smul_dotProduct]

theorem W_le_ker : W ≤ LinearMap.ker phi := by
  rw [W, S, spanL, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hb : (sb 0).getD i 0 ∈ sb 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2]; exact List.getElem_mem _
  show vecOf 112 ((sb 0).getD i 0) ⬝ᵥ vecOf 112 funN = 0
  rw [dot_vecOf, fun_facts.2.1 _ hb]
  simp [b2z]

theorem img_mem (ha : a ∈ H) : vecOf 112 (vmL (lm 6) ((sb 0).getD funW 0)) ∈ W := by
  have haW : a⁻¹ • W = W := (mem_H_iff _).1 (H.inv_mem ha)
  have hwmem : vecOf 112 ((sb 0).getD funW 0) ∈ W := by
    apply mem_spanL
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [length_sb]; exact fun_facts.1)]
    exact List.getElem_mem _
  rw [← haW, smul_def]
  refine ⟨_, hwmem, ?_⟩
  show vecOf 112 ((sb 0).getD funW 0) ᵥ* Mx a⁻¹⁻¹ = _
  rw [inv_inv, Cert.vec cert_a]

theorem a_not_mem : a ∉ H := by
  intro ha
  have h1 := W_le_ker (img_mem ha)
  rw [LinearMap.mem_ker] at h1
  change vecOf 112 (vmL (lm 6) ((sb 0).getD funW 0)) ⬝ᵥ vecOf 112 funN = 0 at h1
  rw [dot_vecOf, fun_facts.2.2] at h1
  simp [b2z] at h1

theorem H_ne_top : H ≠ ⊤ := fun h => a_not_mem (h ▸ Subgroup.mem_top a)

instance : Finite J := Subtype.finite

theorem eq_of_cert {g h : J} {R S : List ℕ} (hg : Cert g R) (hh : Cert h S) (e : R = S) : g = h :=
  Mx_injective (by rw [hg.mx_eq, hh.mx_eq, e])

theorem ne_of_cert {g h : J} {R S : List ℕ} (hg : Cert g R) (hh : Cert h S) {i j : ℕ}
    (hi : i < 112) (hj : j < 112) (e : bitAt R i j ≠ bitAt S i j) : g ≠ h := by
  intro gh
  apply e
  have := congrFun (congrFun (congrArg Mx gh) ⟨i, hi⟩) ⟨j, hj⟩
  rw [hg.mx_eq, hh.mx_eq] at this
  simp only [matOf, Matrix.of_apply, bitAt] at this ⊢
  revert this
  cases (R.getD i 0).testBit j <;> cases (S.getD i 0).testBit j <;> simp [b2z]

theorem isGood_H : IsGood H := by
  have h := klein_c
  simp only [chkKlein, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h
  obtain ⟨h, d3⟩ := h
  obtain ⟨h, d2⟩ := h
  obtain ⟨h, d1⟩ := h
  obtain ⟨h, p5⟩ := h
  obtain ⟨h, p4⟩ := h
  obtain ⟨h, p3⟩ := h
  obtain ⟨h, p2⟩ := h
  obtain ⟨h, p1⟩ := h
  obtain ⟨h, p0⟩ := h
  obtain ⟨h, h3⟩ := h
  obtain ⟨h, h2⟩ := h
  obtain ⟨hk, h1⟩ := h
  have cu : Cert aI (lm 25) := cert_aI
  have cv : Cert (poolE kleinJ) (lm (9 + kleinJ)) := by rw [← lt_pool kleinJ (by omega)]; exact cert_lt _ (by omega)
  have huH : aI ∈ H := by rw [← poolE_16]; exact pool_mem 16 (by norm_num)
  have hvH : poolE kleinJ ∈ H := pool_mem kleinJ (by omega)
  have c1 : Cert (1 : J) (idm 112) := CertG.one
  refine Subgroup.isGood_of_commuting_involutions H huH hvH ?_ ?_ ?_ ?_ ?_ ?_
  · rw [sq]; exact eq_of_cert (cu.mul cu rfl) c1 h1
  · rw [sq]; exact eq_of_cert (cv.mul cv rfl) c1 h2
  · exact eq_of_cert (cu.mul cv rfl) (cv.mul cu rfl) h3
  · exact ne_of_cert cu c1 p0 p1 d1
  · exact ne_of_cert cv c1 p2 p3 d2
  · exact ne_of_cert cu cv p4 p5 d3

/-- **The Wilcox criterion for the matrix model `J` of `J₄`.** -/
theorem wilcoxCriterion_J [Corpus.J4.Stab] [Corpus.J4.Cover] : WilcoxCriterion J := by
  refine Ly.wilcoxCriterion_of_cover W (fun k : Fin ncand => r k) H_ne_top isGood_H ?_ ?_
  · intro g
    obtain ⟨k, hk, h⟩ := cover g
    exact ⟨⟨k, hk⟩, h⟩
  · intro k
    exact triWit_r k k.2

end

end CFSGOutside.HallPaige.J4
