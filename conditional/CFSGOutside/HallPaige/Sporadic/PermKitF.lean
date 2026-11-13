import CFSGOutside.HallPaige.Sporadic.PermKit

/-!
# Kernel-checked permutation certificates with function tables

A variant of `CFSGOutside.HallPaige.PermKit` for large degrees. Tables are arbitrary functions `ℕ → ℕ`
(in practice: a binary dispatch on the high bits of the index selecting a small packed chunk), so
that a lookup touches only a small number. The facts to check (`CFSGOutside.HallPaige.PermKitF.CertOK`) are
stated pointwise, so that they can be checked by many small kernel computations, over blocks of
points, in separate modules.

Further elements are given by a word in earlier elements and a forward table only; their
inverses are never looked up (words use inverse letters of presentation generators only).
-/

namespace CFSGOutside.HallPaige.PermKitF

open Equiv CFSGOutside.HallPaige.PermKit

/-- A lookup table. -/
abbrev Tab := ℕ → ℕ

/-! ### Blocks of points -/

/-- `allFrom p a k` checks `p` on `a, …, a + k - 1`. -/
def allFrom (p : ℕ → Bool) (a : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => p (Nat.add a k) && allFrom p a k

theorem allFrom_iff {p : ℕ → Bool} {a k : ℕ} :
    allFrom p a k = true ↔ ∀ i, a ≤ i → i < a + k → p i = true := by
  induction k with
  | zero => simp only [allFrom, true_iff]; intro i h1 h2; omega
  | succ k ih =>
    simp only [allFrom, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi1 hi2
      by_cases h : i < a + k
      · exact h2 i hi1 h
      · have : i = a + k := by omega
        subst this; exact h1
    · intro h
      exact ⟨h _ (by simp) (by simp), fun i hi1 hi2 => h i hi1 (by omega)⟩

/-- The check of block `j` (of size `B`) of `[0, n)`. -/
def allBlock (p : ℕ → Bool) (n B j : ℕ) : Bool := allFrom p (j * B) (min B (n - j * B))

theorem forall_of_blocks {p : ℕ → Bool} {n B K : ℕ} (hn : n ≤ K * B)
    (h : ∀ j < K, allBlock p n B j = true) : ∀ x < n, p x = true := by
  intro x hx
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; simp at hn; omega
    · exact h0
  have hj : x / B < K := by
    rw [Nat.div_lt_iff_lt_mul hB]; omega
  have := allFrom_iff.1 (h _ hj) x (Nat.div_mul_le_self x B) (by
    have h1 := Nat.lt_div_mul_add (a := x) hB
    have h2 : x / B * B ≤ x := Nat.div_mul_le_self x B
    omega)
  exact this

/-! ### Permutations from tables -/

/-- The inverse-pair condition at a point. -/
def invPt (n : ℕ) (f b : Tab) (i : ℕ) : Bool :=
  Nat.blt (f i) n && Nat.beq (b (f i)) i && Nat.blt (b i) n && Nat.beq (f (b i)) i

theorem invPt_spec {n : ℕ} {f b : Tab} (h : ∀ i < n, invPt n f b i = true) {i : ℕ} (hi : i < n) :
    f i < n ∧ b (f i) = i ∧ b i < n ∧ f (b i) = i := by
  have := h i hi
  simp only [invPt, Bool.and_eq_true, Nat.blt_eq, nbeq_iff] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

open Classical in
/-- The permutation with forward table `f` and inverse table `b` (or `1`). -/
noncomputable def tabPerm (n : ℕ) (f b : Tab) : Perm (Fin n) :=
  if h : ∀ i < n, invPt n f b i = true then
    { toFun := fun i => ⟨f i, (invPt_spec h i.2).1⟩
      invFun := fun i => ⟨b i, (invPt_spec h i.2).2.2.1⟩
      left_inv := fun i => Fin.ext (invPt_spec h i.2).2.1
      right_inv := fun i => Fin.ext (invPt_spec h i.2).2.2.2 }
  else 1

/-- The table `f` represents `σ`. -/
def Rep {n : ℕ} (f : Tab) (σ : Perm (Fin n)) : Prop := ∀ x : Fin n, f x = σ x

theorem Rep.unique {n : ℕ} {f : Tab} {σ τ : Perm (Fin n)} (h1 : Rep f σ) (h2 : Rep f τ) :
    σ = τ :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

theorem rep_tabPerm {n : ℕ} {f b : Tab} (h : ∀ i < n, invPt n f b i = true) :
    Rep f (tabPerm n f b) ∧ Rep b (tabPerm n f b)⁻¹ := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [tabPerm, dif_pos h]; rfl
  · rw [tabPerm, dif_pos h]; rfl

/-! ### Codes and words -/

/-- The table with code `c`, if any. -/
def tabOf (tabs : List (Tab × Tab)) (c : ℕ) : Option Tab :=
  (tabs[c / 2]?).map fun t => if c % 2 = 0 then t.1 else t.2

/-- Apply an optional table (identity for `none`). -/
def apOpt : Option Tab → ℕ → ℕ
  | some f, x => f x
  | none, x => x

/-- Apply the table with code `c`. -/
def lk (tabs : List (Tab × Tab)) (c x : ℕ) : ℕ := apOpt (tabOf tabs c) x

/-- Apply a word of codes to a point; the last letter is applied first. -/
def evalPt (tabs : List (Tab × Tab)) (w : List ℕ) (x : ℕ) : ℕ :=
  (w.map (tabOf tabs)).foldr apOpt x

theorem evalPt_cons (tabs : List (Tab × Tab)) (c : ℕ) (w : List ℕ) (x : ℕ) :
    evalPt tabs (c :: w) x = lk tabs c (evalPt tabs w x) := rfl

/-! ### Certificates -/

/-- A Schreier forest (see `CFSGOutside.HallPaige.PermKit.Forest`), with function tables. -/
structure Forest where
  dep : Tab
  par : Tab
  via : Tab
  cls : Tab

/-- The forest condition at the point `x`. -/
def forestPt (tabs : List (Tab × Tab)) (n : ℕ) (gs reps : List ℕ) (F : Forest) (x : ℕ) : Bool :=
  Nat.beq (F.dep x) 0 ||
    (Nat.blt (F.cls x) reps.length &&
      (if Nat.beq (F.dep x) 1 then Nat.beq (reps.getD (F.cls x) 0) x else
        Nat.blt (F.par x) n && !Nat.beq (F.dep (F.par x)) 0 &&
          Nat.blt (F.dep (F.par x)) (F.dep x) &&
          Nat.beq (F.cls (F.par x)) (F.cls x) &&
          Nat.blt (F.via x) gs.length &&
          Nat.beq (lk tabs (2 * gs.getD (F.via x) 0) (F.par x)) x))

/-- One level of a stabilizer chain. -/
structure Level where
  gs : List ℕ
  beta : ℕ
  F : Forest
  m : ℕ

instance : Inhabited Level := ⟨⟨[], 0, ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, 0⟩⟩

/-- The product of the orbit bounds. -/
def chainProd : List Level → ℕ
  | [] => 1
  | L :: rest => L.m * chainProd rest

/-- Consecutive levels: the generators of the next are among those of this one and fix its
base point. -/
def linkOK (tabs : List (Tab × Tab)) (L L' : Level) : Bool :=
  L'.gs.all (fun g => L.gs.contains g && Nat.beq (lk tabs (2 * g) L.beta) L.beta)

/-- The links of a chain. -/
def linksOK (tabs : List (Tab × Tab)) : List Level → Bool
  | L :: L' :: rest => linkOK tabs L L' && linksOK tabs (L' :: rest)
  | _ => true

/-- A complete certificate. -/
structure Cert where
  n : ℕ
  gens : List (Tab × Tab)
  elems : List (List ℕ × Tab)
  x0 : ℕ
  trans : Forest
  levels : List Level
  lab : Forest
  labReps : List ℕ
  wit : List (List ℕ)
  iu : ℕ
  iz : ℕ
  /-- Points moved by `u`, by `z`, and where `u` and `z` differ. -/
  kp : ℕ × ℕ × ℕ

namespace Cert

/-- All the tables (an element's own table also stands in for its unused inverse). -/
def tabs (c : Cert) : List (Tab × Tab) := c.gens ++ c.elems.map fun e => (e.2, e.2)

def gs1 (c : Cert) : List ℕ := (c.levels.headD default).gs

/-- An allowed code in a word of element `k`: a generator, or an earlier element (forward). -/
def codeOK (c : Cert) (K x : ℕ) : Bool :=
  Nat.blt (x / 2) c.gens.length || (Nat.beq (x % 2) 0 && Nat.blt (x / 2) K)

/-- Numerical and combinatorial side conditions. -/
def basicOK (c : Cert) (m N : ℕ) : Bool :=
  Nat.ble 2 c.n && Nat.blt c.x0 c.n && Nat.beq c.gens.length m &&
    !c.levels.isEmpty && Nat.ble N (c.n * chainProd c.levels) &&
    Nat.beq c.wit.length c.labReps.length &&
    c.wit.all (fun w => w.all (c.codeOK (c.gens.length + c.elems.length))) &&
    (List.range c.elems.length).all (fun k =>
      (c.elems.getD k ([], fun _ => 0)).1.all (c.codeOK (c.gens.length + k))) &&
    c.levels.all (fun L => Nat.blt L.beta c.n) &&
    c.gs1.all (fun g => Nat.beq (lk c.tabs (2 * g) c.x0) c.x0) &&
    linksOK c.tabs c.levels &&
    (List.range c.labReps.length).all (fun k =>
      Nat.beq (c.lab.cls (evalPt c.tabs (c.wit.getD k []) c.x0)) k &&
      Nat.beq (c.lab.cls (evalPt c.tabs (c.wit.getD k [])
        (evalPt c.tabs (c.wit.getD k []) c.x0))) k) &&
    Nat.beq (lk c.tabs (2 * c.iu) c.x0) c.x0 && Nat.beq (lk c.tabs (2 * c.iz) c.x0) c.x0 &&
    !Nat.beq (lk c.tabs (2 * c.iu) c.kp.1) c.kp.1 &&
    !Nat.beq (lk c.tabs (2 * c.iz) c.kp.2.1) c.kp.2.1 &&
    !Nat.beq (lk c.tabs (2 * c.iu) c.kp.2.2) (lk c.tabs (2 * c.iz) c.kp.2.2) &&
    Nat.blt c.kp.1 c.n && Nat.blt c.kp.2.1 c.n && Nat.blt c.kp.2.2 c.n

/-- Element `k` at the point `x`. -/
def elemPt (c : Cert) (k x : ℕ) : Bool :=
  Nat.beq ((c.elems.getD k ([], fun _ => 0)).2 x)
    (evalPt c.tabs (c.elems.getD k ([], fun _ => 0)).1 x)

/-- A relator word at the point `x`. -/
def relPt (c : Cert) (w : List ℕ) (x : ℕ) : Bool := Nat.beq (evalPt c.tabs w x) x

/-- The transitivity forest at `x`. -/
def transPt (c : Cert) (m x : ℕ) : Bool :=
  forestPt c.tabs c.n (List.range m) [c.x0] c.trans x && !Nat.beq (c.trans.dep x) 0

/-- The forest of level `i` at `x`. -/
def levelPt (c : Cert) (i x : ℕ) : Bool :=
  forestPt c.tabs c.n (c.levels.getD i default).gs [(c.levels.getD i default).beta]
    (c.levels.getD i default).F x

/-- The orbit bound of level `i`. -/
def countOK (c : Cert) (i : ℕ) : Bool :=
  Nat.ble (c.levels.getD i default).m
    (countLt (fun x => !Nat.beq ((c.levels.getD i default).F.dep x) 0) c.n)

/-- The labelling forest at `x`. -/
def labPt (c : Cert) (x : ℕ) : Bool :=
  forestPt c.tabs c.n c.gs1 c.labReps c.lab x && !Nat.beq (c.lab.dep x) 0

/-- Invariance of the labels under element `g` at `x`. -/
def invGPt (c : Cert) (g x : ℕ) : Bool :=
  Nat.beq (c.lab.cls (lk c.tabs (2 * g) x)) (c.lab.cls x)

/-- The involution conditions at `x`. -/
def kleinPt (c : Cert) (x : ℕ) : Bool :=
  Nat.beq (lk c.tabs (2 * c.iu) (lk c.tabs (2 * c.iu) x)) x &&
  Nat.beq (lk c.tabs (2 * c.iz) (lk c.tabs (2 * c.iz) x)) x &&
  Nat.beq (lk c.tabs (2 * c.iu) (lk c.tabs (2 * c.iz) x))
    (lk c.tabs (2 * c.iz) (lk c.tabs (2 * c.iu) x))

end Cert

/-- The facts checked about a certificate (pointwise facts can be checked in blocks). -/
structure CertOK (c : Cert) (m : ℕ) (rels : List (List (Fin m × Bool))) (N : ℕ) : Prop where
  basic : c.basicOK m N = true
  gens : ∀ i < c.gens.length, ∀ x < c.n,
    invPt c.n (c.gens.getD i default).1 (c.gens.getD i default).2 x = true
  elems : ∀ k < c.elems.length, ∀ x < c.n, c.elemPt k x = true
  rels : ∀ i < rels.length, ∀ x < c.n, c.relPt ((rels.getD i []).map code) x = true
  trans : ∀ x < c.n, c.transPt m x = true
  levels : ∀ i < c.levels.length, ∀ x < c.n, c.levelPt i x = true
  counts : ∀ i < c.levels.length, c.countOK i = true
  lab : ∀ x < c.n, c.labPt x = true
  inv : ∀ j < c.gs1.length, ∀ x < c.n, c.invGPt (c.gs1.getD j 0) x = true
  klein : ∀ x < c.n, c.kleinPt x = true

/-! ### Semantics -/

/-- The permutations of the generators followed by those of the elements' words. -/
noncomputable def semAux {n : ℕ} : List (Perm (Fin n)) → List (List ℕ × Tab) → List (Perm (Fin n))
  | acc, [] => acc
  | acc, e :: es => semAux (acc ++ [wordPerm acc e.1]) es

theorem semAux_prefix {n : ℕ} (acc : List (Perm (Fin n))) (es : List (List ℕ × Tab)) :
    acc <+: semAux acc es := by
  induction es generalizing acc with
  | nil => exact List.prefix_refl _
  | cons e es ih => exact (List.prefix_append _ _).trans (ih _)

theorem semAux_length {n : ℕ} (acc : List (Perm (Fin n))) (es : List (List ℕ × Tab)) :
    (semAux acc es).length = acc.length + es.length := by
  induction es generalizing acc with
  | nil => simp [semAux]
  | cons e es ih => simp [semAux, ih]; omega

theorem semAux_elem {n : ℕ} (acc : List (Perm (Fin n))) (es : List (List ℕ × Tab)) :
    ∀ k (hk : k < es.length), (semAux acc es)[acc.length + k]? =
      some (wordPerm ((semAux acc es).take (acc.length + k)) es[k].1) := by
  induction es generalizing acc with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero =>
      obtain ⟨t, ht⟩ := semAux_prefix (acc ++ [wordPerm acc e.1]) es
      have htake : (semAux (acc ++ [wordPerm acc e.1]) es).take acc.length = acc := by
        rw [← ht, List.append_assoc, List.take_left' rfl]
      show (semAux (acc ++ [wordPerm acc e.1]) es)[acc.length + 0]? =
        some (wordPerm ((semAux (acc ++ [wordPerm acc e.1]) es).take (acc.length + 0)) e.1)
      rw [Nat.add_zero, htake, ← ht, List.append_assoc,
        List.getElem?_append_right (le_refl _), Nat.sub_self]
      rfl
    | succ k =>
      have := ih (acc ++ [wordPerm acc e.1]) k (by simpa using hk)
      simp only [List.length_append, List.length_singleton] at this
      simp only [semAux, List.getElem_cons_succ]
      rw [show acc.length + (k + 1) = acc.length + 1 + k by omega]
      exact this

/-- The permutation of a pair of tables. -/
noncomputable def tp (n : ℕ) (t : Tab × Tab) : Perm (Fin n) := tabPerm n t.1 t.2

namespace Cert

/-- The semantic permutations of all tables. -/
noncomputable def sem (c : Cert) : List (Perm (Fin c.n)) := semAux (c.gens.map (tp c.n)) c.elems

theorem sem_length (c : Cert) : c.sem.length = c.tabs.length := by
  simp [sem, tabs, semAux_length]

theorem sem_gen (c : Cert) {i : ℕ} (hi : i < c.gens.length) :
    c.sem[i]? = some (tp c.n c.gens[i]) := by
  obtain ⟨t, ht⟩ := semAux_prefix (c.gens.map (tp c.n)) c.elems
  rw [sem, ← ht, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem sem_elem (c : Cert) {k : ℕ} (hk : k < c.elems.length) :
    c.sem[c.gens.length + k]? =
      some (wordPerm (c.sem.take (c.gens.length + k)) c.elems[k].1) := by
  have := semAux_elem (c.gens.map (tp c.n)) c.elems k hk
  simpa [sem] using this

theorem tabs_gen (c : Cert) {i : ℕ} (hi : i < c.gens.length) : c.tabs[i]? = some c.gens[i] := by
  rw [tabs, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem tabs_elem (c : Cert) {k : ℕ} (hk : k < c.elems.length) :
    c.tabs[c.gens.length + k]? = some (c.elems[k].2, c.elems[k].2) := by
  rw [tabs, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  rfl

end Cert

theorem pk_take {n : ℕ} (l : List (Perm (Fin n))) {K c : ℕ} (hc : c / 2 < K) :
    pk (l.take K) c = pk l c := by
  unfold pk
  rw [List.getElem?_take_of_lt hc]

theorem wordPerm_take {n : ℕ} (l : List (Perm (Fin n))) {K : ℕ} (w : List ℕ)
    (hw : ∀ c ∈ w, c / 2 < K) : wordPerm (l.take K) w = wordPerm l w := by
  unfold wordPerm
  congr 1
  exact List.map_congr_left fun c hc => pk_take l (hw c hc)

theorem evalPt_eq_of {n : ℕ} {tabs : List (Tab × Tab)} {σs : List (Perm (Fin n))} (w : List ℕ)
    (h : ∀ c ∈ w, ∀ x : Fin n, lk tabs c x = pk σs c x) (x : Fin n) :
    evalPt tabs w x = wordPerm σs w x := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalPt_cons, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'),
      h c (List.mem_cons_self ..)]
    simp [wordPerm, Perm.mul_apply]

section Sound

variable {c : Cert}

theorem basic_codes {m N : ℕ} (h : c.basicOK m N = true) :
    (∀ w ∈ c.wit, ∀ y ∈ w, c.codeOK (c.gens.length + c.elems.length) y = true) ∧
    (∀ k < c.elems.length, ∀ y ∈ (c.elems.getD k ([], fun _ => 0)).1,
      c.codeOK (c.gens.length + k) y = true) := by
  simp only [Cert.basicOK, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := h
  exact ⟨h7, h8⟩

theorem codeOK_iff {K x : ℕ} :
    c.codeOK K x = true ↔ x / 2 < c.gens.length ∨ (x % 2 = 0 ∧ x / 2 < K) := by
  simp [Cert.codeOK, Nat.blt_eq, nbeq_iff]

/-- Lookups agree with the semantics, for generator codes and forward element codes. -/
theorem lk_sem {m N : ℕ} {rels : List (List (Fin m × Bool))} (hc : CertOK c m rels N) :
    ∀ j, ∀ cd, cd / 2 = j → (j < c.gens.length ∨ cd % 2 = 0) → ∀ x : Fin c.n,
      lk c.tabs cd x = pk c.sem cd x := by
  have hcodes := (basic_codes hc.basic).2
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro cd hj hpar x
    by_cases hjm : j < c.gens.length
    · have hr := rep_tabPerm (n := c.n) (f := c.gens[j].1) (b := c.gens[j].2) (by
        intro i hi
        have := hc.gens j hjm i hi
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjm, Option.getD_some] at this)
      unfold lk tabOf pk
      rw [hj, c.tabs_gen hjm, c.sem_gen hjm]
      simp only [Option.map_some]
      split_ifs
      · exact hr.1 x
      · exact hr.2 x
    · obtain ⟨k, rfl⟩ : ∃ k, j = c.gens.length + k := ⟨j - c.gens.length, by omega⟩
      have hev : cd % 2 = 0 := hpar.resolve_left hjm
      by_cases hk : k < c.elems.length
      · have hcw : ∀ y ∈ c.elems[k].1, y / 2 < c.gens.length ∨
            (y % 2 = 0 ∧ y / 2 < c.gens.length + k) := by
          intro y hy
          have := hcodes k hk y (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
            exact hy)
          exact codeOK_iff.1 this
        have hw : ∀ y ∈ c.elems[k].1, ∀ x : Fin c.n, lk c.tabs y x = pk c.sem y x := by
          intro y hy x
          rcases hcw y hy with h | ⟨h1, h2⟩
          · exact ih (y / 2) (by omega) y rfl (Or.inl h) x
          · exact ih (y / 2) h2 y rfl (Or.inr h1) x
        have hval := hc.elems k hk x x.2
        simp only [Cert.elemPt, nbeq_iff, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hk, Option.getD_some] at hval
        unfold lk tabOf pk
        rw [hj, c.tabs_elem hk, c.sem_elem hk]
        simp only [Option.map_some, hev, if_true]
        show c.elems[k].2 x = _
        rw [hval, evalPt_eq_of _ hw x, wordPerm_take _ _ (fun y hy => by
          rcases hcw y hy with h | ⟨_, h2⟩ <;> omega)]
      · have h1 : c.tabs[c.gens.length + k]? = none := by
          rw [List.getElem?_eq_none_iff]
          simp only [Cert.tabs, List.length_append, List.length_map]; omega
        have h2 : c.sem[c.gens.length + k]? = none := by
          rw [List.getElem?_eq_none_iff, c.sem_length]
          simp only [Cert.tabs, List.length_append, List.length_map]; omega
        unfold lk tabOf pk
        rw [hj, h1, h2]
        rfl

theorem lk_even {m N : ℕ} {rels : List (List (Fin m × Bool))} (hc : CertOK c m rels N)
    (g : ℕ) (x : Fin c.n) : lk c.tabs (2 * g) x = pk c.sem (2 * g) x :=
  lk_sem hc _ _ rfl (Or.inr (by omega)) x

theorem forest_reach' {tabs : List (Tab × Tab)} {n : ℕ} {σs : List (Perm (Fin n))}
    {gs reps : List ℕ} {F : Forest}
    (hlk : ∀ g (x : Fin n), lk tabs (2 * g) x = pk σs (2 * g) x)
    (h : ∀ x < n, forestPt tabs n gs reps F x = true) :
    ∀ x : Fin n, F.dep x ≠ 0 → ∃ r : Fin n, (r : ℕ) = reps.getD (F.cls x) 0 ∧
      ∃ σ ∈ Kset σs gs, σ r = x := by
  suffices H : ∀ e, ∀ x : Fin n, F.dep x = e → e ≠ 0 →
      ∃ r : Fin n, (r : ℕ) = reps.getD (F.cls x) 0 ∧ ∃ σ ∈ Kset σs gs, σ r = x from
    fun x hx => H _ x rfl hx
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro x hxe he
    have hx := h x x.2
    unfold forestPt at hx
    rw [Bool.or_eq_true] at hx
    rcases hx with h0 | hx
    · exact absurd (hxe ▸ (nbeq_iff.1 h0)) he
    rw [Bool.and_eq_true] at hx
    obtain ⟨-, hx⟩ := hx
    rw [hxe] at hx
    by_cases he1 : e = 1
    · rw [if_pos (by simp [he1])] at hx
      exact ⟨x, (nbeq_iff.1 hx).symm, 1, Subgroup.one_mem _, rfl⟩
    · rw [if_neg (by simpa [nbeq_iff] using he1)] at hx
      simp only [Bool.and_eq_true, Nat.blt_eq, nbeq_iff, Bool.not_eq_true',
        nbeq_false_iff, ne_eq] at hx
      obtain ⟨⟨⟨⟨⟨hp, hp0⟩, hpe⟩, hcls⟩, hv⟩, himg⟩ := hx
      set p : Fin n := ⟨F.par x, hp⟩ with hpdef
      obtain ⟨r, hr, σ, hσ, hσr⟩ := ih (F.dep p) hpe p rfl hp0
      refine ⟨r, ?_, pk σs (2 * gs.getD (F.via x) 0) * σ,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, by
          simp only [List.getD, List.getElem?_eq_getElem hv, Option.getD_some]
          exact List.getElem_mem hv, rfl⟩) hσ, ?_⟩
      · rw [hr]
        change reps.getD (F.cls (F.par x)) 0 = _
        rw [hcls]
      · apply Fin.ext
        rw [Perm.mul_apply, hσr, ← hlk]
        exact himg

theorem forest_reach_one' {tabs : List (Tab × Tab)} {n : ℕ} {σs : List (Perm (Fin n))}
    {gs : List ℕ} {b : ℕ} {F : Forest}
    (hlk : ∀ g (x : Fin n), lk tabs (2 * g) x = pk σs (2 * g) x)
    (h : ∀ x < n, forestPt tabs n gs [b] F x = true) (hb : b < n) (x : Fin n)
    (hx : F.dep x ≠ 0) : ∃ σ ∈ Kset σs gs, σ ⟨b, hb⟩ = x := by
  obtain ⟨r, hr, σ, hσ, hσr⟩ := forest_reach' hlk h x hx
  have hcls : F.cls x < 1 := by
    have := h x x.2
    simp only [forestPt, Bool.or_eq_true, nbeq_iff, hx, false_or, Bool.and_eq_true,
      Nat.blt_eq, List.length_singleton] at this
    exact this.1
  have : r = ⟨b, hb⟩ := by
    apply Fin.ext
    rw [hr, Nat.lt_one_iff.1 hcls]
    rfl
  exact ⟨σ, hσ, this ▸ hσr⟩

theorem chain_card' {tabs : List (Tab × Tab)} {n : ℕ} {σs : List (Perm (Fin n))}
    (hlk : ∀ g (x : Fin n), lk tabs (2 * g) x = pk σs (2 * g) x) :
    ∀ (L : Level) (rest : List Level),
      (∀ L' ∈ L :: rest, L'.beta < n ∧ (∀ x < n, forestPt tabs n L'.gs [L'.beta] L'.F x = true) ∧
        L'.m ≤ countLt (fun x => !Nat.beq (L'.F.dep x) 0) n) →
      linksOK tabs (L :: rest) = true →
      chainProd (L :: rest) ≤ Nat.card (Kset σs L.gs) := by
  have orbit : ∀ L : Level, ∀ hb : L.beta < n,
      (∀ x < n, forestPt tabs n L.gs [L.beta] L.F x = true) →
      L.m ≤ countLt (fun x => !Nat.beq (L.F.dep x) 0) n →
      ∃ s : Finset (Fin n), L.m ≤ s.card ∧ ∀ x ∈ s, ∃ σ ∈ Kset σs L.gs, σ ⟨L.beta, hb⟩ = x := by
    intro L hb hF hm
    refine ⟨Finset.univ.filter fun x : Fin n => (!Nat.beq (L.F.dep x) 0) = true,
      by rwa [countLt_eq] at hm, ?_⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
      nbeq_false_iff] at hx
    exact forest_reach_one' hlk hF hb x hx
  intro L rest
  induction rest generalizing L with
  | nil =>
    intro hL _
    obtain ⟨hb, hF, hm⟩ := hL L (List.mem_singleton_self _)
    obtain ⟨s, hs, horb⟩ := orbit L hb hF hm
    have := card_le_of_orbit _ ⊥ ⟨L.beta, hb⟩ L.m bot_le (fun σ hσ => by
      rw [Subgroup.mem_bot.1 hσ]; rfl) s hs horb
    simpa [chainProd] using this
  | cons L' rest ih =>
    intro hL hlinks
    simp only [linksOK, Bool.and_eq_true] at hlinks
    obtain ⟨hlink, hrest⟩ := hlinks
    simp only [linkOK, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem,
      nbeq_iff] at hlink
    obtain ⟨hb, hF, hm⟩ := hL L (List.mem_cons_self ..)
    obtain ⟨s, hs, horb⟩ := orbit L hb hF hm
    have hfix : ∀ σ ∈ Kset σs L'.gs, σ ⟨L.beta, hb⟩ = ⟨L.beta, hb⟩ := by
      apply kset_fix
      intro g hg
      apply Fin.ext
      rw [← hlk]
      exact (hlink g hg).2
    have := card_le_of_orbit _ _ ⟨L.beta, hb⟩ L.m (kset_mono _ fun g hg => (hlink g hg).1) hfix s
      hs horb
    calc chainProd (L :: L' :: rest) = L.m * chainProd (L' :: rest) := rfl
      _ ≤ L.m * Nat.card (Kset σs L'.gs) :=
          Nat.mul_le_mul_left _ (ih L' (fun L'' h => hL L'' (List.mem_cons_of_mem _ h)) hrest)
      _ ≤ _ := this

/-- The images of the generators. -/
noncomputable def genPermF (c : Cert) (m : ℕ) : Fin m → Perm (Fin c.n) :=
  fun i => pk c.sem (2 * i)

/-- **Soundness of the certificate checker.** -/
theorem permLabelling_of_certOK {P : TauCeti.GroupPresentation} [Finite P.Group] {N : ℕ}
    (hN : Nat.card P.Group ≤ N) (c : Cert) (hc : CertOK c P.generatorCount P.relators N) :
    PermLabelling P.Group := by
  have hb := hc.basic
  simp only [Cert.basicOK, Bool.and_eq_true, and_assoc, Nat.ble_eq, Nat.blt_eq, nbeq_iff,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, List.mem_range,
    nbeq_false_iff] at hb
  obtain ⟨h1, h3, hm, h9, h12, h16, -, -, hbeta, h10, hlinks, hwit, h18, h19, hk1, hk2, hk3,
    hkp1, hkp2, hkp3⟩ := hb
  have hlk := lk_even hc
  set σs := c.sem with hσs
  have hgenlk : ∀ (l : Fin P.generatorCount × Bool) (x : Fin c.n),
      lk c.tabs (code l) x = pk σs (code l) x := by
    intro l x
    apply lk_sem hc _ _ rfl (Or.inl _) x
    have : code l / 2 = l.1 := by unfold code; split_ifs <;> omega
    rw [this, hm]; exact l.1.2
  -- the homomorphism
  have hrel : ∀ r ∈ P.relatorSet, FreeGroup.lift (genPermF c P.generatorCount) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hw' := hc.rels i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hw'
    have e : (P.relators[i].map fun x => bif x.2 then genPermF c P.generatorCount x.1
        else (genPermF c P.generatorCount x.1)⁻¹) = (P.relators[i].map code).map (pk σs) := by
      rw [List.map_map]
      exact List.map_congr_left fun l _ => pk_code σs l
    rw [e]
    apply Equiv.ext
    intro x
    apply Fin.ext
    have := hw' x x.2
    rw [Cert.relPt, nbeq_iff, evalPt_eq_of (σs := σs) _ (by
      intro cd hcd
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hcd
      exact hgenlk l)] at this
    exact this
  set ρ : P.Group →* Perm (Fin c.n) := PresentedGroup.toGroup hrel with hρ
  set R := ρ.range
  have hmemR : ∀ j : ℕ, ∀ σ, σs[j]? = some σ → σ ∈ R := by
    have hcodes := (basic_codes hc.basic).2
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro σ hσ
      by_cases hj : j < c.gens.length
      · rw [c.sem_gen hj, Option.some.injEq] at hσ
        subst hσ
        refine ⟨PresentedGroup.of ⟨j, hm ▸ hj⟩, ?_⟩
        rw [hρ, PresentedGroup.toGroup.of]
        change pk σs (2 * j) = _
        have h2j : 2 * j / 2 = j := by omega
        have h2j' : 2 * j % 2 = 0 := by omega
        simp [pk, h2j, h2j', hσs, c.sem_gen hj]
      · obtain ⟨k, rfl⟩ : ∃ k, j = c.gens.length + k := ⟨j - c.gens.length, by omega⟩
        by_cases hk : k < c.elems.length
        · rw [c.sem_elem hk, Option.some.injEq] at hσ
          subst hσ
          have hw : ∀ y ∈ c.elems[k].1, y / 2 < c.gens.length + k := by
            intro y hy
            have := codeOK_iff.1 (hcodes k hk y (by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
              exact hy))
            omega
          rw [wordPerm_take _ _ hw]
          exact wordPerm_mem_of_lt (fun j' hj' σ' hσ' => ih j' hj' σ' hσ') _ hw
        · rw [List.getElem?_eq_none (by
            rw [c.sem_length]; simp only [Cert.tabs, List.length_append, List.length_map]; omega)]
            at hσ
          cases hσ
  have hσR : ∀ σ ∈ σs, σ ∈ R := by
    intro σ hσ
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hσ
    exact hmemR j _ (List.getElem?_eq_getElem hj)
  set x₀ : Fin c.n := ⟨c.x0, h3⟩
  -- transitivity
  have htr : ∀ x < c.n, forestPt c.tabs c.n (List.range P.generatorCount) [c.x0] c.trans x =
      true := fun x hx => by
    have := hc.trans x hx; simp only [Cert.transPt, Bool.and_eq_true] at this; exact this.1
  have htrans : ∀ y : Fin c.n, ∃ σ ∈ R, σ x₀ = y := by
    intro y
    have hd := hc.trans y y.2
    simp only [Cert.transPt, Bool.and_eq_true, Bool.not_eq_true', nbeq_false_iff] at hd
    obtain ⟨σ, hσ, hσy⟩ := forest_reach_one' hlk htr h3 y hd.2
    exact ⟨σ, kset_le hσR _ hσ, hσy⟩
  -- the chain
  obtain ⟨L, rest, hL⟩ : ∃ L rest, c.levels = L :: rest := by
    cases hl : c.levels with
    | nil => exact absurd hl h9
    | cons L rest => exact ⟨L, rest, rfl⟩
  have hgs1 : c.gs1 = L.gs := by simp [Cert.gs1, hL]
  have hlev : ∀ L' ∈ L :: rest, L'.beta < c.n ∧
      (∀ x < c.n, forestPt c.tabs c.n L'.gs [L'.beta] L'.F x = true) ∧
      L'.m ≤ countLt (fun x => !Nat.beq (L'.F.dep x) 0) c.n := by
    intro L' hL'
    rw [← hL] at hL'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hL'
    refine ⟨hbeta _ hL', fun x hx => ?_, ?_⟩
    · have := hc.levels i hi x hx
      rwa [Cert.levelPt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some] at this
    · have := hc.counts i hi
      rwa [Cert.countOK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some, Nat.ble_eq] at this
  rw [hgs1] at h10
  rw [hL] at hlinks h12
  set S := MulAction.stabilizer (Perm (Fin c.n)) x₀ ⊓ R
  set K := Kset σs L.gs
  have hKS : K ≤ S := by
    refine le_inf ((Subgroup.closure_le _).2 ?_) (kset_le hσR _)
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Perm.smul_def]
    apply Fin.ext
    rw [← hlk]
    exact h10 g hg
  have hKcard : chainProd (L :: rest) ≤ Nat.card K := chain_card' hlk L rest hlev hlinks
  have hRcard : Nat.card R = c.n * Nat.card S := by
    have e1 := Subgroup.card_mul_index (MulAction.stabilizer R x₀)
    rw [MulAction.index_stabilizer] at e1
    have horb : MulAction.orbit R x₀ = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      obtain ⟨σ, hσ, hσy⟩ := htrans y
      exact ⟨⟨σ, hσ⟩, hσy⟩
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin c.n), Fintype.card_fin] at e1
    have e2 : MulAction.stabilizer R x₀ = S.subgroupOf R := by
      ext g
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, S, Subgroup.mem_inf,
        g.2, and_true]
      rfl
    rw [e2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at e1
    rw [← e1, mul_comm]
  have hGR : Nat.card R ≤ Nat.card P.Group :=
    Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hKeq : K = S := by
    apply Subgroup.eq_of_le_of_card_ge hKS
    have hn : 0 < c.n := by omega
    have : c.n * Nat.card S ≤ c.n * Nat.card K := by
      rw [← hRcard]
      exact (hGR.trans hN).trans (h12.trans (Nat.mul_le_mul_left _ hKcard))
    exact Nat.le_of_mul_le_mul_left this hn
  -- the labelling
  have h13 : ∀ x < c.n, forestPt c.tabs c.n L.gs c.labReps c.lab x = true := fun x hx => by
    have := hc.lab x hx; simp only [Cert.labPt, Bool.and_eq_true, hgs1] at this; exact this.1
  have hlab : ∀ y : Fin c.n, c.lab.dep y ≠ 0 := fun y => by
    have := hc.lab y y.2
    simp only [Cert.labPt, Bool.and_eq_true, Bool.not_eq_true', nbeq_false_iff] at this
    exact this.2
  have hcls : ∀ y : Fin c.n, c.lab.cls y < c.labReps.length := by
    intro y
    have := h13 y y.2
    simp only [forestPt, Bool.or_eq_true, nbeq_iff, hlab y, false_or, Bool.and_eq_true,
      Nat.blt_eq] at this
    exact this.1
  have hr : 0 < c.labReps.length := lt_of_le_of_lt (Nat.zero_le _) (hcls x₀)
  have hinv : ∀ σ ∈ K, ∀ y, c.lab.cls (σ y) = c.lab.cls y := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ =>
      obtain ⟨g, hg, rfl⟩ := hσ
      intro y
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
      have hj' : j < c.gs1.length := hgs1 ▸ hj
      have := hc.inv j hj' y y.2
      rw [hgs1] at this
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
        Cert.invGPt, nbeq_iff] at this
      rw [hlk] at this
      exact this
    | one => intro y; rfl
    | mul σ τ _ _ hσ hτ => intro y; rw [Perm.mul_apply, hσ, hτ]
    | inv σ _ hσ =>
      intro y
      have := hσ (σ⁻¹ y)
      have e : σ (σ⁻¹ y) = y := by simp
      rw [e] at this
      exact this.symm
  have hwlk : ∀ k, ∀ cd ∈ c.wit.getD k [], ∀ x : Fin c.n, lk c.tabs cd x = pk σs cd x := by
    have hwc := (basic_codes hc.basic).1
    intro k cd hcd x
    have hmem : c.wit.getD k [] ∈ c.wit ∨ c.wit.getD k [] = [] := by
      rw [List.getD_eq_getElem?_getD]
      cases h : c.wit[k]? with
      | none => right; rfl
      | some w => left; exact List.mem_of_getElem? h
    rcases hmem with hmem | hmem
    · rcases codeOK_iff.1 (hwc _ hmem cd hcd) with h | ⟨h, -⟩
      · exact lk_sem hc _ cd rfl (Or.inl h) x
      · exact lk_sem hc _ cd rfl (Or.inr h) x
    · rw [hmem] at hcd; cases hcd
  refine ⟨c.n, ρ, x₀, c.labReps.length,
    fun y => ⟨c.lab.cls y % c.labReps.length, Nat.mod_lt _ hr⟩,
    Equiv.refl _, ?_, ?_, fun k => rfl, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ, hσy⟩ := htrans y
    obtain ⟨g, rfl⟩ := hσ
    exact ⟨g, hσy⟩
  · intro y y'
    simp only [Fin.mk.injEq, Nat.mod_eq_of_lt (hcls _)]
    constructor
    · intro hyy
      obtain ⟨r, hr1, σ, hσ, hσr⟩ := forest_reach' hlk h13 y (hlab y)
      obtain ⟨r', hr1', σ', hσ', hσr'⟩ := forest_reach' hlk h13 y' (hlab y')
      have hrr : r = r' := Fin.ext (by
        rw [hr1, hr1']; exact congrArg (fun k => c.labReps.getD k 0) hyy)
      have hτ : σ' * σ⁻¹ ∈ S := hKS (K.mul_mem hσ' (K.inv_mem hσ))
      obtain ⟨g, hg⟩ := (Subgroup.mem_inf.1 hτ).2
      refine ⟨g, ?_, ?_⟩
      · rw [hg]; exact (Subgroup.mem_inf.1 hτ).1
      · rw [hg, Perm.mul_apply, ← hσr, show σ⁻¹ (σ r) = r by simp, hrr, hσr']
    · rintro ⟨g, hg0, rfl⟩
      have hgS : ρ g ∈ K := hKeq ▸ Subgroup.mem_inf.2 ⟨hg0, ⟨g, rfl⟩⟩
      exact (hinv _ hgS y).symm
  · intro k
    have hk := hwit k k.2
    set w := c.wit.getD k []
    have hw : wordPerm σs w ∈ R := wordPerm_mem hσR w
    obtain ⟨g, hg⟩ := hw
    have e1 : evalPt c.tabs w c.x0 = (ρ g x₀ : ℕ) := by
      rw [hg]; exact evalPt_eq_of w (hwlk k) x₀
    have e2 : evalPt c.tabs w (evalPt c.tabs w c.x0) = (ρ (g * g) x₀ : ℕ) := by
      rw [e1, map_mul, Perm.mul_apply, hg]; exact evalPt_eq_of w (hwlk k) _
    refine ⟨g, g, ?_, ?_, ?_⟩ <;> apply Fin.ext <;>
      simp only [Equiv.refl_apply, Nat.mod_eq_of_lt (hcls _)]
    · rw [← hk.1, e1]
    · rw [← hk.1, e1]
    · rw [← hk.2, e2]
  · set u := pk σs (2 * c.iu)
    set z := pk σs (2 * c.iz)
    have hU : ∀ x : Fin c.n, lk c.tabs (2 * c.iu) x = u x := hlk _
    have hZ : ∀ x : Fin c.n, lk c.tabs (2 * c.iz) x = z x := hlk _
    have hmap : ∀ v : Perm (Fin c.n), v ∈ R → v x₀ = x₀ →
        v ∈ ((MulAction.stabilizer (Perm (Fin c.n)) x₀).comap ρ).map ρ := by
      rintro v ⟨g, rfl⟩ hv
      exact ⟨g, by simpa only [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
        Perm.smul_def] using hv, rfl⟩
    have hu0 : u x₀ = x₀ := Fin.ext (by rw [← hU]; exact h18)
    have hz0 : z x₀ = x₀ := Fin.ext (by rw [← hZ]; exact h19)
    have hkl : ∀ x : Fin c.n, u (u x) = x ∧ z (z x) = x ∧ u (z x) = z (u x) := by
      intro x
      have := hc.klein x x.2
      simp only [Cert.kleinPt, Bool.and_eq_true, nbeq_iff] at this
      obtain ⟨⟨e1, e2⟩, e3⟩ := this
      rw [hU, hU] at e1
      rw [hZ, hZ] at e2
      rw [hZ, hU, hU, hZ] at e3
      exact ⟨Fin.ext e1, Fin.ext e2, Fin.ext e3⟩
    apply isGood_of_involutions _ ρ (hmap u (pk_mem hσR _) hu0) (hmap z (pk_mem hσR _) hz0)
    · ext x; simp [Perm.mul_apply, (hkl x).1]
    · ext x; simp [Perm.mul_apply, (hkl x).2.1]
    · ext x; simp [Perm.mul_apply, (hkl x).2.2]
    · intro hu1
      apply hk1
      rw [hU ⟨_, hkp1⟩, hu1]; rfl
    · intro hz1
      apply hk2
      rw [hZ ⟨_, hkp2⟩, hz1]; rfl
    · intro huz
      apply hk3
      rw [hU ⟨_, hkp3⟩, hZ ⟨_, hkp3⟩, huz]
  · by_cases h0 : c.x0 = 0
    · exact ⟨⟨1, by omega⟩, fun e => by simp [x₀, h0] at e⟩
    · exact ⟨⟨0, by omega⟩, fun e => h0 (by simpa [x₀] using (congrArg Fin.val e).symm)⟩

end Sound

end CFSGOutside.HallPaige.PermKitF
