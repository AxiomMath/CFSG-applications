
import CFSGOutside.Common.NonsolubleLength

/-!
# The upper nonsoluble series

For a finite group `X` the *upper nonsoluble series* (Khukhro–Shumyatsky, Proc. AMS 2015, §3) is
`1 = L₀ ≤ M₁ ≤ L₁ ≤ M₂ ≤ ⋯`, where `M_{k+1}/L_k = R(X/L_k)` is the soluble radical and
`L_k/M_k = E(X/M_k)` is the layer (`= F*(X/M_k)`, a direct product of nonabelian simple groups,
since `F(X/M_k) = 1`).  Here `upperSeries X j` is the `j`-th term:
`upperSeries X (2k) = L_k` and `upperSeries X (2k+1) = M_{k+1}`.

Main results:
* `nonsolubleLengthLE_iff_upperSeries`: `λ(X) ≤ l ↔ M_{l+1}(X) = X`, i.e. the upper nonsoluble
  series realizes the nonsoluble length (`upperSeries_eq_top_of_nonsolubleLengthLE` is the
  minimality direction, `nonsolubleLengthLE_of_upperSeries_eq_top` the other one);
* `fittingSubgroup_quotient_upperSeries_odd`: `F(X/M_k) = 1`;
* `solubleFactor_upperSeries`, `semisimpleFactor_upperSeries`: the factors are soluble, resp.
  direct products of nonabelian simple groups;
* `map_upperSeries`: the series is invariant under isomorphisms (hence characteristic).
-/

section

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open scoped commutatorElement

namespace CFSGOutside.UpperNonsolubleSeries

open CFSGOutside.NonsolubleLength

section Basic

variable {Y : Type*} [Group Y]

lemma layer_normal' [Finite Y] : (layer Y).Normal :=
  inferInstance

/-- The image of the layer under a surjection lies in the layer. -/
lemma map_layer_le {Z : Type*} [Group Z] (f : Y →* Z) (hf : Function.Surjective f) :
    (layer Y).map f ≤ layer Z := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  by_cases hker : L ≤ f.ker
  · rw [(Subgroup.map_eq_bot_iff L).mpr hker]; exact bot_le
  · exact le_sSup (show IsComponent (L.map f) from
      ⟨isQuasisimple_map hL.1 f hker, hL.2.map hf⟩)

lemma map_layer_mulEquiv {Z : Type*} [Group Z] (e : Y ≃* Z) :
    (layer Y).map e.toMonoidHom = layer Z := by
  refine le_antisymm (map_layer_le _ e.surjective) ?_
  intro z hz
  exact ⟨e.symm z, map_layer_le e.symm.toMonoidHom e.symm.surjective ⟨z, hz, rfl⟩, by simp⟩

lemma map_solvableRadical_le_of_mulEquiv [Finite Y] {Z : Type*} [Group Z] (f : Y ≃* Z) :
    (solvableRadical Y).map f.toMonoidHom ≤ solvableRadical Z := by
  haveI := isSolvable_solvableRadical (G := Y)
  refine le_solvableRadical
    (Normal.map inferInstance _ f.surjective) ?_
  exact Group.isSolvable_of_surjective (f.toMonoidHom.subgroupMap_surjective _)

lemma map_solvableRadical_mulEquiv [Finite Y] {Z : Type*} [Group Z] (e : Y ≃* Z) :
    (solvableRadical Y).map e.toMonoidHom = solvableRadical Z := by
  haveI : Finite Z := Finite.of_equiv Y e.toEquiv
  refine le_antisymm (map_solvableRadical_le_of_mulEquiv e) ?_
  intro z hz
  exact ⟨e.symm z, map_solvableRadical_le_of_mulEquiv e.symm ⟨z, hz, rfl⟩, by simp⟩

/-- A nonabelian simple group is quasisimple. -/
lemma isQuasisimple_of_simple {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  have hc : Subgroup.center Q = ⊥ := by
    rcases hQ.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, @MulEquiv.isSimpleGroup _ _ _ _ hQ e, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases hQ.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hmem : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

/-- A normal homomorphic image of a direct product of nonabelian simple groups lies in the
layer. -/
lemma range_le_layer_of_semisimple {Q : Type*} [Group Q] (hQ : IsSemisimpleProd Q)
    (f : Q →* Y) (hn : f.range.Normal) : f.range ≤ layer Y := by
  classical
  obtain ⟨ι, S, _, hfin, hS, hnab, ⟨e⟩⟩ := hQ
  haveI := Fintype.ofFinite ι
  have hcomp : ∀ i (s : S i), f (e.symm (Pi.mulSingle i s)) ∈ layer Y := by
    intro i s
    let fi : S i →* Y := (f.comp e.symm.toMonoidHom).comp (MonoidHom.mulSingle S i)
    have hfi : ∀ t, fi t = f (e.symm (Pi.mulSingle i t)) := fun t => rfl
    rw [← hfi]
    by_cases htriv : fi.ker = ⊤
    · rw [(MonoidHom.mem_ker).1 (htriv ▸ mem_top s)]; exact one_mem _
    · haveI := hS i
      have hinj : Function.Injective fi := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact ((fi.normal_ker).eq_bot_or_eq_top).resolve_right htriv
      let ei : S i ≃* fi.range := MonoidHom.ofInjective hinj
      have hsimple : IsSimpleGroup fi.range := ei.symm.isSimpleGroup
      have hnab' : ∃ a b : fi.range, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnab i
        exact ⟨ei a, ei b, fun h => hab (ei.injective (by rw [map_mul, map_mul, h]))⟩
      have hle : fi.range ≤ f.range := by
        rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩
      have key : ∀ (q : Q) (t : S i), f q * fi t * (f q)⁻¹ = fi (e q i * t * (e q i)⁻¹) := by
        intro q t
        rw [hfi, hfi, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply e.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.mulSingle_eq_of_ne hj]
      have hNn : (fi.range.subgroupOf f.range).Normal := by
        refine ⟨fun x hx r => ?_⟩
        obtain ⟨rv, q, rfl⟩ := r
        rw [mem_subgroupOf] at hx ⊢
        obtain ⟨t, ht⟩ := hx
        refine ⟨e q i * t * (e q i)⁻¹, ?_⟩
        rw [← key, ht]
        rfl
      have hcomp : IsComponent fi.range :=
        ⟨isQuasisimple_of_simple hsimple hnab',
          IsSubnormal.step _ _ hle hn.isSubnormal hNn⟩
      exact component_le_layer hcomp ⟨s, rfl⟩
  rintro _ ⟨q, rfl⟩
  have hq : f q = (f.comp e.symm.toMonoidHom) (e q) := by simp
  rw [hq]
  set x := e q
  have key : ∀ T : Finset ι, (f.comp e.symm.toMonoidHom)
      (fun j => if j ∈ T then x j else 1) ∈ layer Y := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : (fun j => if j ∈ (∅ : Finset ι) then x j else 1) = (1 : ∀ i, S i) := by
        funext j; simp
      rw [this, map_one]; exact one_mem _
    | insert a T ha ih =>
      have : (fun j => if j ∈ insert a T then x j else 1) =
          Pi.mulSingle a (x a) * (fun j => if j ∈ T then x j else 1) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [ha]
        · simp [Finset.mem_insert, hj, Pi.mulSingle_eq_of_ne hj]
      rw [this, map_mul]
      exact mul_mem (hcomp a (x a)) ih
  have := key Finset.univ
  simpa using this

end Basic

section Series

variable (X : Type) [Group X] [Finite X]

/-- The terms of the upper nonsoluble series, with their normality. -/
noncomputable def upperSeriesN : ℕ → {N : Subgroup X // N.Normal}
  | 0 => ⟨⊥, normal_bot⟩
  | j + 1 =>
    haveI := (upperSeriesN j).2
    if j % 2 = 0 then
      ⟨(solvableRadical (X ⧸ (upperSeriesN j).1)).comap (QuotientGroup.mk' _),
        Normal.comap inferInstance _⟩
    else
      ⟨(layer (X ⧸ (upperSeriesN j).1)).comap (QuotientGroup.mk' _),
        Normal.comap layer_normal' _⟩

/-- The upper nonsoluble series: `upperSeries X (2k) = L_k`, `upperSeries X (2k+1) = M_{k+1}`. -/
noncomputable def upperSeries (j : ℕ) : Subgroup X := (upperSeriesN X j).1

instance upperSeries_normal (j : ℕ) : (upperSeries X j).Normal := (upperSeriesN X j).2

lemma upperSeries_zero : upperSeries X 0 = ⊥ := rfl

lemma upperSeries_odd (k : ℕ) : upperSeries X (2 * k + 1) =
    (solvableRadical (X ⧸ upperSeries X (2 * k))).comap (QuotientGroup.mk' _) := by
  have h : 2 * k % 2 = 0 := by omega
  show (upperSeriesN X (2 * k + 1)).1 = _
  dsimp only [upperSeriesN]
  rw [if_pos h]
  rfl

lemma upperSeries_even (k : ℕ) : upperSeries X (2 * k + 2) =
    (layer (X ⧸ upperSeries X (2 * k + 1))).comap (QuotientGroup.mk' _) := by
  have h : ¬ (2 * k + 1) % 2 = 0 := by omega
  show (upperSeriesN X (2 * k + 1 + 1)).1 = _
  dsimp only [upperSeriesN]
  rw [if_neg h]
  rfl

variable {X}

lemma upperSeries_le_succ (j : ℕ) : upperSeries X j ≤ upperSeries X (j + 1) := by
  intro x hx
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [upperSeries_odd, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  · rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, upperSeries_even, mem_comap,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _

lemma upperSeries_mono {i j : ℕ} (h : i ≤ j) : upperSeries X i ≤ upperSeries X j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (upperSeries_le_succ _)

/-- `M_{k+1}/L_k` is soluble: `dA b M_{k+1} ≤ L_k`. -/
lemma exists_dA_upperSeries_odd_le (k : ℕ) :
    ∃ b, dA b (upperSeries X (2 * k + 1)) ≤ upperSeries X (2 * k) := by
  set N := upperSeries X (2 * k)
  obtain ⟨b, hb⟩ := (isSolvable_subgroup_iff (solvableRadical (X ⧸ N))).1
    isSolvable_solvableRadical
  refine ⟨b, ?_⟩
  have : (dA b (upperSeries X (2 * k + 1))).map (QuotientGroup.mk' N) = ⊥ := by
    rw [map_dA, upperSeries_odd, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N),
      hb]
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this

lemma solubleFactor_upperSeries (k : ℕ) :
    SolubleFactor (upperSeries X (2 * k)) (upperSeries X (2 * k + 1)) :=
  solubleFactor_iff.2 (exists_dA_upperSeries_odd_le k)

/-- `F(X/M_{k+1}) = 1`. -/
lemma fittingSubgroup_quotient_upperSeries_odd (k : ℕ) :
    fittingSubgroup (X ⧸ upperSeries X (2 * k + 1)) = ⊥ := by
  set N := upperSeries X (2 * k) with hN
  set M := upperSeries X (2 * k + 1) with hM
  rw [fittingSubgroup, sSup_eq_bot]
  rintro W ⟨hW, hWnil⟩
  set P := W.comap (QuotientGroup.mk' M)
  haveI : P.Normal := hW.comap _
  obtain ⟨a, ha⟩ := (isSolvable_subgroup_iff W).1 (by haveI := hWnil; infer_instance)
  obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := X) k
  have h1 : dA a P ≤ M := by
    have : (dA a P).map (QuotientGroup.mk' M) = ⊥ := by
      rw [map_dA, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M), ha]
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
  have h2 : dA (b + a) P ≤ N := by rw [dA_add]; exact (dA_mono b h1).trans hb
  have hPM : P ≤ M := by
    have hle : P.map (QuotientGroup.mk' N) ≤ solvableRadical (X ⧸ N) := by
      refine le_solvableRadical
        (Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)) ?_
      rw [isSolvable_subgroup_iff]
      refine ⟨b + a, ?_⟩
      rw [← map_dA, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact h2
    intro x hx
    rw [hM, upperSeries_odd]
    exact hle ⟨x, hx, rfl⟩
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M w
  rw [mem_bot]
  exact (QuotientGroup.eq_one_iff x).2 (hPM hw)

lemma semisimpleFactor_upperSeries (k : ℕ) :
    SemisimpleFactor (upperSeries X (2 * k + 1)) (upperSeries X (2 * k + 2)) := by
  set M := upperSeries X (2 * k + 1)
  have h := semisimpleFactor_comap (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
    (semisimpleFactor_layer (fittingSubgroup_quotient_upperSeries_odd k))
  rwa [MonoidHom.comap_bot, QuotientGroup.ker_mk', ← upperSeries_even] at h

/-- The upper nonsoluble series is a nonsoluble series. -/
theorem nonsolubleLengthLE_of_upperSeries_eq_top {m : ℕ}
    (h : upperSeries X (2 * m + 1) = ⊤) : NonsolubleLengthLE X m :=
  ⟨{ G := upperSeries X
     normal := upperSeries_normal X
     mono := fun i _ => upperSeries_le_succ i
     zero := rfl
     top := h
     sol := fun i _ => solubleFactor_upperSeries i
     semisimple := fun i _ => semisimpleFactor_upperSeries i }⟩

/-- **Minimality of the upper nonsoluble series**: every nonsoluble series lies termwise below it,
so `λ(X) ≤ l` forces `M_{l+1}(X) = X`. -/
theorem upperSeries_eq_top_of_nonsolubleLengthLE {l : ℕ} (h : NonsolubleLengthLE X l) :
    upperSeries X (2 * l + 1) = ⊤ := by
  obtain ⟨s⟩ := h
  have hsol : ∀ i, s.G (2 * i) ≤ upperSeries X (2 * i) → i ≤ l →
      s.G (2 * i + 1) ≤ upperSeries X (2 * i + 1) := by
    intro i hi hil
    haveI := s.normal (2 * i)
    haveI := s.normal (2 * i + 1)
    set N := upperSeries X (2 * i)
    obtain ⟨a, ha⟩ := solubleFactor_iff.1 (s.sol i hil)
    have hle : (s.G (2 * i + 1)).map (QuotientGroup.mk' N) ≤ solvableRadical (X ⧸ N) := by
      refine le_solvableRadical
        (Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)) ?_
      rw [isSolvable_subgroup_iff]
      refine ⟨a, ?_⟩
      rw [← map_dA, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact ha.trans hi
    intro x hx
    rw [upperSeries_odd]
    exact hle ⟨x, hx, rfl⟩
  have hss : ∀ i, s.G (2 * i + 1) ≤ upperSeries X (2 * i + 1) → i < l →
      s.G (2 * i + 2) ≤ upperSeries X (2 * i + 2) := by
    intro i hi hil
    haveI := s.normal (2 * i + 1)
    haveI := s.normal (2 * i + 2)
    set N := upperSeries X (2 * i + 1)
    set A := s.G (2 * i + 1)
    set B := s.G (2 * i + 2)
    obtain ⟨_, hQ⟩ := s.semisimple i hil
    let f : B ⧸ A.subgroupOf B →* X ⧸ N :=
      QuotientGroup.lift (A.subgroupOf B) ((QuotientGroup.mk' N).comp B.subtype) (by
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact hi (mem_subgroupOf.1 hx))
    have hrange : f.range = B.map (QuotientGroup.mk' N) := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ q
        exact ⟨b, b.2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨QuotientGroup.mk ⟨b, hb⟩, rfl⟩
    have hle := range_le_layer_of_semisimple hQ f (by
      rw [hrange]; exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective N))
    rw [hrange] at hle
    intro x hx
    rw [upperSeries_even]
    exact hle ⟨x, hx, rfl⟩
  have key : ∀ i ≤ l, s.G (2 * i + 1) ≤ upperSeries X (2 * i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0
      exact hsol 0 (by rw [s.zero]; exact bot_le) h0
    | succ i ih =>
      intro hil
      have h1 := hss i (ih (by omega)) (by omega)
      exact hsol (i + 1) (by rw [show 2 * (i + 1) = 2 * i + 2 by ring]; exact h1) hil
  rw [eq_top_iff, ← s.top]
  exact key l le_rfl

theorem nonsolubleLengthLE_iff_upperSeries {l : ℕ} :
    NonsolubleLengthLE X l ↔ upperSeries X (2 * l + 1) = ⊤ :=
  ⟨upperSeries_eq_top_of_nonsolubleLengthLE, nonsolubleLengthLE_of_upperSeries_eq_top⟩

/-- The upper nonsoluble series is invariant under isomorphisms. -/
theorem map_upperSeries {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y) (j : ℕ) :
    (upperSeries X j).map e.toMonoidHom = upperSeries Y j := by
  induction j with
  | zero => rw [upperSeries_zero, upperSeries_zero, Subgroup.map_bot]
  | succ j ih =>
    let ē : X ⧸ upperSeries X j ≃* Y ⧸ upperSeries Y j := QuotientGroup.congr _ _ e ih
    have hē : ∀ x : X, ē (x : X ⧸ upperSeries X j) = (e x : Y ⧸ upperSeries Y j) := fun x => rfl
    have key : ∀ (F : ∀ (Z : Type) [Group Z] [Finite Z], Subgroup Z),
        (F (X ⧸ upperSeries X j)).map ē.toMonoidHom = F (Y ⧸ upperSeries Y j) →
        ((F (X ⧸ upperSeries X j)).comap (QuotientGroup.mk' _)).map e.toMonoidHom =
          (F (Y ⧸ upperSeries Y j)).comap (QuotientGroup.mk' _) := by
      intro F hF
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (QuotientGroup.mk' (upperSeries Y j)) (e x) ∈ F _
        rw [QuotientGroup.mk'_apply, ← hē, ← hF]
        exact ⟨_, hx, rfl⟩
      · intro hy
        change (QuotientGroup.mk' (upperSeries Y j)) y ∈ F _ at hy
        refine ⟨e.symm y, ?_, by simp⟩
        change (QuotientGroup.mk' (upperSeries X j)) (e.symm y) ∈ F _
        rw [QuotientGroup.mk'_apply]
        have : ē ((e.symm y : X) : X ⧸ upperSeries X j) ∈ F (Y ⧸ upperSeries Y j) := by
          rw [hē, e.apply_symm_apply]; exact hy
        rw [← hF] at this
        obtain ⟨z, hz, hz'⟩ := this
        rwa [ē.injective hz'] at hz
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [upperSeries_odd, upperSeries_odd]
      exact key (fun Z _ _ => solvableRadical Z) (map_solvableRadical_mulEquiv ē)
    · rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, upperSeries_even, upperSeries_even]
      exact key (fun Z _ _ => layer Z) (map_layer_mulEquiv ē)

end Series

end CFSGOutside.UpperNonsolubleSeries
