
import CFSGOutside.Common.NonPSolubleLength
import CFSGOutside.KhukhroShumyatskyNonsolubleLength.TheoremA
import CFSGOutside.KhukhroShumyatskyNonsolubleLength.Statement
import CFSGOutside.Corpus.ThompsonElementaryNormalPComplement

/-!
# Khukhro–Shumyatsky, Theorem 1.1(b): non-`p`-soluble length and `p`-length

**Paper.** E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*,
Israel J. Math. **207** (2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434.

**Theorem 1.1(b).** For `p ≠ 2`, the non-`p`-soluble length `λ_p(G)` of a finite group `G` does
not exceed the maximum `p`-length of `p`-soluble subgroups of `G`.

Final statement: `theorem_1_1_b`, with the paper's literal definitions
(`paperNonPSolubleLength`, `paperMaxPLength`, `paperPLength`, `paperPSoluble`: normal series with
`p`-soluble / semisimple factors, resp. `p`- and `p'`-factors, counted as in the paper).  The
crosswalks `paperNonPSolubleLength_eq`, `paperPLength_eq`, `paperPSoluble_iff` identify them with
the working notions (`NonPSolubleLengthLE` from `CFSGOutside.NonPSolubleLength`, the lower
`p`-series `PLenLE`, and `PSoluble`).  Working form: `nonPSolubleLengthLE_of_pLenLE`.

**Proof.** As in the paper, by induction on the bound, using `λ_p(K_p(G)) ≤ 1` (Lemma 2.1, the
Schreier conjecture; `nonPSolubleLengthLE_succ_of_pKernel` from `NonPSolubleLength`) and the
Proposition in the proof of Theorem 1.1(b): the maximum `p`-length of `p`-soluble subgroups of
`G/K_p(G)` is smaller than for `G` (`pLength_quotient_kernel`).  For the Proposition we use a
direct argument in place of the paper's induction on `|G|` (orbit reduction, and induction on a
non-`p`-soluble normalizer `N_G(C)` via the socle of `N/R_p(N)`):

* `exists_pSoluble_not_npc`: every finite group `A` without a normal `p`-complement (`p` odd)
  contains a `p`-soluble subgroup `B` without a normal `p`-complement which is invariant under all
  automorphisms of `A` normalizing a Sylow `p`-subgroup `P` (Thompson's normal `p`-complement
  theorem, from the corpus, and induction on `|A|`: pass to `N_A(C)` or to `A/C` for the
  characteristic subgroup `C ∈ {Z(P), J_e(P)}` of the theorem).
* For `M/K` `p`-soluble of `p`-length `k` in `Y = G/R_p(G)`, with `V = Soc(Y) = ∏ S_i` and
  `P ∈ Syl_p(V)`: `M = V·N_M(P)` (Frattini), choose `B_{S}` as above in one component `S` of each
  `N_M(P)`-orbit, transport it along the orbit, and put `X = (∏ B_{S_i})·N_M(P)`.  Then `X` is
  `p`-soluble, `XK = M`, and the paper's projection argument shows `O_{p',p}(X) ≤ K`, so `X` has
  `p`-length `≥ k + 1`.
-/

section

namespace CFSGOutside.KhukhroShumyatskyNonsolubleLength

open CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores

open Subgroup CFSGOutside.NonPSolubleLength
open CFSGOutside.NonsolubleLength (mem_of_pow_mem_of_coprime map_conj_eq_of_mem_normalizer
  mem_normalizer_of_map_conj_eq mem_map_conj_iff map_subtype_top)

/-! ### The lower `p`-series, `p`-length and normal `p`-complements -/

section PLength

variable (p : ℕ) {G : Type*} [Group G]

/-- One step of the lower `p`-series: `S ↦ O^p(O^{p'}(S))`. -/
def lowerStep (S : Subgroup G) : Subgroup G := pPrimeGen p (pGen p S)

/-- `H` has `p`-length at most `l` (and is `p`-soluble): `O^{p'}` of the `l`-th term of the lower
`p`-series is trivial. -/
def PLenLE (H : Subgroup G) (l : ℕ) : Prop := pGen p ((lowerStep p)^[l] H) = ⊥

/-- `H` has a normal `p`-complement: `O^p(H)` contains no nontrivial `p`-element. -/
def NPC (H : Subgroup G) : Prop := pGen p (pPrimeGen p H) = ⊥

variable {p} [Finite G] [hp : Fact p.Prime]

lemma lowerStep_le (S : Subgroup G) : lowerStep p S ≤ S :=
  (pPrimeGen_le p _).trans (pGen_le p S)

lemma lowerStep_mono {S T : Subgroup G} (h : S ≤ T) : lowerStep p S ≤ lowerStep p T :=
  pPrimeGen_mono p (pGen_mono p h)

lemma lowerStep_iterate_mono (n : ℕ) {S T : Subgroup G} (h : S ≤ T) :
    (lowerStep p)^[n] S ≤ (lowerStep p)^[n] T := by
  induction n generalizing S T with
  | zero => exact h
  | succ n ih => exact ih (lowerStep_mono h)

lemma lowerStep_iterate_le (n : ℕ) (S : Subgroup G) : (lowerStep p)^[n] S ≤ S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih => exact (ih _).trans (lowerStep_le S)

lemma lowerStep_iterate_anti {m n : ℕ} (h : m ≤ n) (S : Subgroup G) :
    (lowerStep p)^[n] S ≤ (lowerStep p)^[m] S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact lowerStep_iterate_le k _

section Map

variable {G' : Type*} [Group G']

lemma map_lowerStep (f : G →* G') (S : Subgroup G) :
    (lowerStep p S).map f = lowerStep p (S.map f) := by
  rw [lowerStep, lowerStep, map_pPrimeGen, map_pGen]

lemma map_lowerStep_iterate (f : G →* G') (n : ℕ) (S : Subgroup G) :
    ((lowerStep p)^[n] S).map f = (lowerStep p)^[n] (S.map f) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, ih, map_lowerStep]

lemma PLenLE.map (f : G →* G') {H : Subgroup G} {l : ℕ} (h : PLenLE p H l) :
    PLenLE p (H.map f) l := by
  unfold PLenLE at h ⊢
  rw [← map_lowerStep_iterate, ← map_pGen, h, Subgroup.map_bot]

lemma PLenLE.of_map_injective {f : G →* G'} (hf : Function.Injective f) {H : Subgroup G} {l : ℕ}
    (h : PLenLE p (H.map f) l) : PLenLE p H l := by
  unfold PLenLE at h ⊢
  rw [← map_lowerStep_iterate, ← map_pGen] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 h

lemma NPC.map (f : G →* G') {H : Subgroup G} (h : NPC p H) : NPC p (H.map f) := by
  unfold NPC at h ⊢
  rw [← map_pPrimeGen, ← map_pGen, h, Subgroup.map_bot]

lemma NPC.of_map_injective {f : G →* G'} (hf : Function.Injective f) {H : Subgroup G}
    (h : NPC p (H.map f)) : NPC p H := by
  unfold NPC at h ⊢
  rw [← map_pPrimeGen, ← map_pGen] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 h

end Map

lemma PLenLE.mono_left {H H' : Subgroup G} (hHH : H ≤ H') {l : ℕ} (h : PLenLE p H' l) :
    PLenLE p H l :=
  le_bot_iff.1 (h ▸ pGen_mono p (lowerStep_iterate_mono l hHH))

lemma PLenLE.mono {H : Subgroup G} {l l' : ℕ} (hl : l ≤ l') (h : PLenLE p H l) :
    PLenLE p H l' :=
  le_bot_iff.1 (h ▸ pGen_mono p (lowerStep_iterate_anti hl H))

lemma NPC.mono {H H' : Subgroup G} (hHH : H ≤ H') (h : NPC p H') : NPC p H :=
  le_bot_iff.1 (h ▸ pGen_mono p (pPrimeGen_mono p hHH))

/-- `p`-length `≤ k + 1` means that `O^{p'}` of the `k`-th term has a normal `p`-complement. -/
lemma pLenLE_succ_iff {H : Subgroup G} {k : ℕ} :
    PLenLE p H (k + 1) ↔ NPC p (pGen p ((lowerStep p)^[k] H)) := by
  unfold PLenLE NPC
  rw [Function.iterate_succ_apply']
  rfl

lemma normalizer_le_normalizer_pGen (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer ((pGen p S : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_of_map_conj_eq (by rw [map_pGen, map_conj_eq_of_mem_normalizer hg])

lemma normalizer_le_normalizer_pPrimeGen (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer ((pPrimeGen p S : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_of_map_conj_eq (by rw [map_pPrimeGen, map_conj_eq_of_mem_normalizer hg])

lemma normalizer_le_normalizer_lowerStep_iterate (n : ℕ) (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (((lowerStep p)^[n] S : Subgroup G) : Set G) :=
  fun g hg =>
  mem_normalizer_of_map_conj_eq (by rw [map_lowerStep_iterate, map_conj_eq_of_mem_normalizer hg])

lemma mem_pGen_of_isPElt {S : Subgroup G} {x : G} (hx : x ∈ S) (h : IsPElt p x) :
    x ∈ pGen p S := subset_closure ⟨hx, h⟩

lemma mem_pPrimeGen_of_isPPrimeElt {S : Subgroup G} {x : G} (hx : x ∈ S) (h : IsPPrimeElt p x) :
    x ∈ pPrimeGen p S := subset_closure ⟨hx, h⟩

lemma pGen_eq_bot_iff {S : Subgroup G} : pGen p S = ⊥ ↔ ∀ x ∈ S, IsPElt p x → x = 1 := by
  constructor
  · intro h x hx hp
    have := mem_pGen_of_isPElt hx hp
    rw [h] at this
    exact this
  · intro h
    rw [eq_bot_iff, pGen, closure_le]
    rintro x ⟨hx, hp⟩
    exact h x hx hp

/-- Having a normal `p`-complement implies `p`-solubility. -/
lemma NPC.pSoluble {H : Subgroup G} (h : NPC p H) : PSoluble p H := by
  refine ⟨2, ?_⟩
  show Dp p (Dp p H) ≤ ⊥
  refine inf_le_right.trans ?_
  rw [← h]
  exact pGen_mono p inf_le_left

lemma PLenLE.pSoluble {H : Subgroup G} {l : ℕ} (h : PLenLE p H l) : PSoluble p H := by
  induction l generalizing H with
  | zero =>
    refine ⟨1, ?_⟩
    show Dp p H ≤ ⊥
    rw [← h]
    exact inf_le_right
  | succ l ih =>
    have h1 : PSoluble p ((lowerStep p) H) := ih (by
      unfold PLenLE at h ⊢; rwa [← Function.iterate_succ_apply])
    obtain ⟨n, hn⟩ := h1
    refine ⟨n + 2, ?_⟩
    rw [Function.iterate_add_apply]
    refine (Dp_iterate_mono p n ?_).trans hn
    show Dp p (Dp p H) ≤ pPrimeGen p (pGen p H)
    exact inf_le_left.trans (pPrimeGen_mono p inf_le_right)

/-- A `p`-subgroup is `p`-soluble. -/
lemma pSoluble_of_isPGroup {C : Subgroup G} (hC : IsPGroup p C) :
    PSoluble p C := by
  refine ⟨1, ?_⟩
  show Dp p C ≤ ⊥
  refine inf_le_left.trans ?_
  rw [pPrimeGen, closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  obtain ⟨k, hk⟩ := hC ⟨x, hx⟩
  have hk' : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have : x ∈ (⊥ : Subgroup G) :=
    mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right k hm) (by rw [hxm]; exact one_mem _)
      (by rw [hk']; exact one_mem _)
  exact this

end PLength

/-! ### Bridge to the corpus notion of a normal `p`-complement -/

section Bridge

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [Group A] [Finite A]

lemma eq_one_of_isPElt_of_coprime {x : A} {m : ℕ} (hm : Nat.Coprime p m) (hxm : x ^ m = 1)
    (hx : IsPElt p x) : x = 1 := by
  obtain ⟨k, hk⟩ := hx
  have : x ∈ (⊥ : Subgroup A) :=
    mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left k hm) (by rw [hk]; exact one_mem _)
      (by rw [hxm]; exact one_mem _)
  exact this

lemma npc_top_iff : NPC p (⊤ : Subgroup A) ↔ HasNormalPComplement p A := by
  constructor
  · intro h
    set N := pPrimeGen p (⊤ : Subgroup A)
    haveI hN : N.Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff]
      refine le_trans ?_ (normalizer_le_normalizer_pPrimeGen (⊤ : Subgroup A))
      rw [normalizer_eq_top_iff.mpr inferInstance]
    refine ⟨N, hN, ?_, ?_⟩
    · rw [Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hdvd
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
      have hy1 : (y : A) ∈ pGen p N := mem_pGen_of_isPElt y.2 ⟨1, by
        rw [pow_one]
        have := pow_orderOf_eq_one (y : A)
        rwa [Subgroup.orderOf_coe, hy] at this⟩
      rw [NPC] at h
      rw [h, mem_bot] at hy1
      have : y = 1 := Subtype.ext hy1
      rw [this, orderOf_one] at hy
      exact hp.out.one_lt.ne hy
    · intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨k, hk⟩ := exists_pow_isPPrimeElt p g
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact mem_pPrimeGen_of_isPPrimeElt (mem_top _) hk
  · rintro ⟨N, hN, hcop, hq⟩
    have hle : pPrimeGen p (⊤ : Subgroup A) ≤ N := by
      rw [pPrimeGen, closure_le]
      rintro x ⟨-, m, hm, hxm⟩
      obtain ⟨k, hk⟩ := hq (x : A ⧸ N)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right k hm) (by rw [hxm]; exact one_mem _)
        hk
    rw [NPC, pGen_eq_bot_iff]
    intro x hx hpx
    have hxN : x ∈ N := hle hx
    have h1 : (⟨x, hxN⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    exact eq_one_of_isPElt_of_coprime hcop (congrArg Subtype.val h1) hpx

lemma npc_iff_subgroup (H : Subgroup A) :
    NPC p H ↔ HasNormalPComplement p H := by
  rw [← npc_top_iff]
  constructor
  · intro h
    apply NPC.of_map_injective H.subtype_injective
    rwa [map_subtype_top]
  · intro h
    have := h.map H.subtype
    rwa [map_subtype_top] at this

end Bridge


/-! ### A `p`-soluble subgroup without normal `p`-complement, invariant under `N_{Aut}(P)` -/

section Thompson

variable {p : ℕ} [hp : Fact p.Prime]

lemma map_eq_of_map_le {A : Type*} [Group A] {C : Subgroup A} {P : Subgroup A}
    (h : ∀ σ : MulAut A, P.map σ.toMonoidHom = P → C.map σ.toMonoidHom ≤ C)
    (σ : MulAut A) (hσ : P.map σ.toMonoidHom = P) : C.map σ.toMonoidHom = C := by
  refine le_antisymm (h σ hσ) ?_
  have hσ' : P.map σ⁻¹.toMonoidHom = P := by
    conv_lhs => rw [← hσ]
    rw [Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp
  intro x hx
  refine ⟨σ⁻¹ x, h σ⁻¹ hσ' ⟨x, hx, rfl⟩, ?_⟩
  simp

lemma apply_mem_iff_of_map_eq {A : Type*} [Group A] {C : Subgroup A} {σ : MulAut A}
    (hC : C.map σ.toMonoidHom = C) (y : A) : σ y ∈ C ↔ y ∈ C := by
  constructor
  · intro h
    rw [← hC] at h
    obtain ⟨y', hy', he⟩ := h
    have : y' = y := σ.injective he
    rwa [← this]
  · intro h
    rw [← hC]
    exact ⟨y, h, rfl⟩

lemma normalizer_map_eq_of_map_eq {A : Type*} [Group A] {C : Subgroup A} {σ : MulAut A}
    (hC : C.map σ.toMonoidHom = C) :
    (normalizer (C : Set A)).map σ.toMonoidHom = normalizer (C : Set A) := by
  have key : ∀ τ : MulAut A, C.map τ.toMonoidHom = C →
      (normalizer (C : Set A)).map τ.toMonoidHom ≤ normalizer (C : Set A) := by
    rintro τ hτ _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_normalizer_iff] at hg
    rw [mem_normalizer_iff]
    intro x
    obtain ⟨x', rfl⟩ := τ.surjective x
    have e : (τ.toMonoidHom g) * τ x' * (τ.toMonoidHom g)⁻¹ = τ (g * x' * g⁻¹) := by
      simp
    rw [e, apply_mem_iff_of_map_eq hτ, apply_mem_iff_of_map_eq hτ]
    exact hg x'
  exact map_eq_of_map_le (P := C) key σ hC

/-- The restriction of an automorphism stabilising a subgroup. -/
def restrictAut {A : Type*} [Group A] (σ : MulAut A) (H : Subgroup A)
    (hH : H.map σ.toMonoidHom = H) : MulAut H :=
  (MulEquiv.subgroupMap σ H).trans (MulEquiv.subgroupCongr hH)

@[simp] lemma restrictAut_apply_coe {A : Type*} [Group A] (σ : MulAut A) (H : Subgroup A)
    (hH : H.map σ.toMonoidHom = H) (x : H) : ((restrictAut σ H hH x : H) : A) = σ x := rfl

lemma centralizer_le_normalizer' {A : Type*} [Group A] (H : Subgroup A) :
    centralizer (H : Set A) ≤ normalizer (H : Set A) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  rw [mem_centralizer_iff] at hx
  constructor
  · intro hh
    have e : x * h * x⁻¹ = h := by rw [← hx h hh]; group
    rw [e]
    exact hh
  · intro hk
    have h2 := hx _ hk
    have e : h = x * h * x⁻¹ :=
      calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [h2]
        _ = x * h * x⁻¹ := by group
    rw [e]
    exact hk

lemma comap_mk_bot {A : Type*} [Group A] (C : Subgroup A) [C.Normal] :
    (⊥ : Subgroup (A ⧸ C)).comap (QuotientGroup.mk' C) = C := by
  ext x
  simp [QuotientGroup.eq_one_iff]

lemma npc_top_of_not_dvd {A : Type*} [Group A] [Finite A] (h : ¬ p ∣ Nat.card A) :
    NPC p (⊤ : Subgroup A) := by
  rw [NPC, eq_bot_iff]
  refine (pGen_mono p (pPrimeGen_le p _)).trans ?_
  rw [← eq_bot_iff, pGen_eq_bot_iff]
  intro x _ hx
  exact eq_one_of_isPElt_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h)
    pow_card_eq_one' hx

lemma elemThompson_ne_bot {R : Type*} [Group R] [Finite R] [Nontrivial R] (hR : IsPGroup p R) :
    elemThompson R p ≠ ⊥ := by
  intro hJ
  obtain ⟨A, hA, hAc⟩ := exists_card_eq_pow_pRank R p
  have hAJ : A ≤ elemThompson R p := le_sSup ⟨hA, hAc⟩
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot] at hAc
  have hdvd : p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    have h1 : 1 < Nat.card R := Finite.one_lt_card
    rw [hn] at h1 ⊢
    exact dvd_pow_self p (by rintro rfl; simp at h1)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hE : IsElementaryAbelian p (Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hle := card_le_pow_pRank (R := R) hE
  rw [Nat.card_zpowers, hx, ← hAc] at hle
  exact absurd hle (by have := hp.out.one_lt; omega)

/-- A characteristic-type subgroup of the Sylow subgroup `P` whose normalizer has no normal
`p`-complement (Thompson's normal `p`-complement theorem, `p` odd). -/
lemma exists_char_not_npc [ThompsonElementaryNormalPComplement.{0}] (hp2 : p ≠ 2) {A : Type} [Group A] [Finite A] (P : Sylow p A)
    (hA : ¬ NPC p (⊤ : Subgroup A)) :
    ∃ C : Subgroup A, C ≤ P ∧ C ≠ ⊥ ∧
      (∀ σ : MulAut A, (P : Subgroup A).map σ.toMonoidHom = P → C.map σ.toMonoidHom = C) ∧
      ¬ NPC p (normalizer (C : Set A)) := by
  have hTh : ¬ HasNormalPComplement p A := by rwa [← npc_top_iff]
  have hdvd : p ∣ Nat.card A := by
    by_contra h
    exact hA (npc_top_of_not_dvd h)
  haveI hPnt : Nontrivial (P : Subgroup A) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (P.ne_bot_of_dvd_card hdvd)
  set Z : Subgroup A := (center (P : Subgroup A)).map (P : Subgroup A).subtype with hZ
  set J : Subgroup A := (elemThompson (P : Subgroup A) p).map (P : Subgroup A).subtype
    with hJ
  have hZσ : ∀ σ : MulAut A, (P : Subgroup A).map σ.toMonoidHom = P → Z.map σ.toMonoidHom = Z := by
    refine map_eq_of_map_le (P := (P : Subgroup A)) ?_
    rintro σ hσ _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hz
    have hzP : σ (z : A) ∈ (P : Subgroup A) := (apply_mem_iff_of_map_eq hσ _).2 z.2
    refine ⟨⟨σ z, hzP⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro q
    obtain ⟨q', rfl⟩ := (restrictAut σ _ hσ).surjective q
    apply Subtype.ext
    have := congrArg (fun w : (P : Subgroup A) => σ (w : A)) (hz q')
    simpa using this
  have hJσ : ∀ σ : MulAut A, (P : Subgroup A).map σ.toMonoidHom = P → J.map σ.toMonoidHom = J := by
    intro σ hσ
    have he := elemThompson_map_mulEquiv (restrictAut σ _ hσ) p
    have hcomm : σ.toMonoidHom.comp (P : Subgroup A).subtype =
        (P : Subgroup A).subtype.comp (restrictAut σ _ hσ).toMonoidHom := by
      ext x; rfl
    calc J.map σ.toMonoidHom
        = (elemThompson (P : Subgroup A) p).map
            (σ.toMonoidHom.comp (P : Subgroup A).subtype) := by rw [hJ, Subgroup.map_map]
      _ = ((elemThompson (P : Subgroup A) p).map
            (restrictAut σ _ hσ).toMonoidHom).map (P : Subgroup A).subtype := by
          rw [hcomm, Subgroup.map_map]
      _ = J := by rw [he]
  have hZne : Z ≠ ⊥ := by
    haveI := IsPGroup.center_nontrivial P.isPGroup'
    intro h
    obtain ⟨z, hz⟩ := exists_ne (1 : center (P : Subgroup A))
    have : ((z : (P : Subgroup A)) : A) ∈ Z := ⟨z, z.2, rfl⟩
    rw [h, mem_bot] at this
    exact hz (Subtype.ext (Subtype.ext this))
  have hJne : J ≠ ⊥ := by
    intro h
    apply elemThompson_ne_bot (R := (P : Subgroup A)) P.isPGroup'
    rw [hJ, Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup A).subtype_injective] at h
    exact h
  by_cases hC : HasNormalPComplement p (centralizer (Z : Set A))
  · refine ⟨J, ?_, hJne, hJσ, ?_⟩
    · rintro _ ⟨x, -, rfl⟩; exact x.2
    · rw [npc_iff_subgroup]
      exact fun hN => hTh (ThompsonElementaryNormalPComplement.thompson_elementary_normal_p_complement hp2 P
        hC hN)
  · refine ⟨Z, ?_, hZne, hZσ, ?_⟩
    · rintro _ ⟨x, -, rfl⟩; exact x.2
    · intro hN
      apply hC
      rw [← npc_iff_subgroup]
      exact hN.mono (centralizer_le_normalizer' Z)

/-- **Key local lemma.** For an odd prime `p`, every finite group `A` without a normal
`p`-complement contains a `p`-soluble subgroup `B` without a normal `p`-complement, which is
invariant under every automorphism of `A` stabilising a given Sylow `p`-subgroup `P`.  (Proof:
Thompson's normal `p`-complement theorem, and induction on `|A|`.) -/
theorem exists_pSoluble_not_npc [ThompsonElementaryNormalPComplement.{0}] (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (A : Type) [Group A] [Finite A], Nat.card A = n → ∀ P : Sylow p A,
      ¬ NPC p (⊤ : Subgroup A) →
      ∃ B : Subgroup A, PSoluble p B ∧ ¬ NPC p B ∧
        ∀ σ : MulAut A, (P : Subgroup A).map σ.toMonoidHom = P → B.map σ.toMonoidHom ≤ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn P hA
  by_cases hs : PSoluble p (⊤ : Subgroup A)
  · exact ⟨⊤, hs, hA, fun _ _ => le_top⟩
  obtain ⟨C, hCP, hCne, hCσ, hCN⟩ := exists_char_not_npc hp2 P hA
  have hPN : (P : Subgroup A) ≤ normalizer (C : Set A) := by
    intro g hg
    apply mem_normalizer_of_map_conj_eq
    apply hCσ
    exact map_conj_eq_of_mem_normalizer (le_normalizer hg)
  by_cases hA₁ : normalizer (C : Set A) = ⊤
  · -- `C` is normal: pass to `A / C`
    haveI hCn : C.Normal := normalizer_eq_top_iff.mp hA₁
    set Q := A ⧸ C
    have hcard : Nat.card Q < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup C]
      have h1 : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot C).2 hCne
      have h2 : 0 < Nat.card Q := Nat.card_pos
      nlinarith
    have hCp : IsPGroup p C := P.isPGroup'.to_le hCP
    have hQ : ¬ NPC p (⊤ : Subgroup Q) := by
      intro hQ
      apply hs
      have h1 := pSolSec_comap (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) hQ.pSoluble
      rw [comap_top, comap_mk_bot] at h1
      exact (pSoluble_of_isPGroup hCp).trans h1
    obtain ⟨B', hB's, hB'n, hB'σ⟩ :=
      ih _ hcard Q rfl (P.mapSurjective (QuotientGroup.mk'_surjective C)) hQ
    refine ⟨B'.comap (QuotientGroup.mk' C), ?_, ?_, ?_⟩
    · have h1 := pSolSec_comap (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) hB's
      rw [comap_mk_bot] at h1
      exact (pSoluble_of_isPGroup hCp).trans h1
    · intro hN
      apply hB'n
      have := hN.map (QuotientGroup.mk' C)
      rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C)] at this
    · intro σ hσ
      have hCσ' : C.map (σ : A →* A) = C := hCσ σ hσ
      let σ' : MulAut Q := QuotientGroup.congr C C σ hCσ'
      have hcomp : σ'.toMonoidHom.comp (QuotientGroup.mk' C) =
          (QuotientGroup.mk' C).comp σ.toMonoidHom := by
        ext x
        exact QuotientGroup.congr_mk C C σ hCσ' x
      have hPσ : ((P.mapSurjective (QuotientGroup.mk'_surjective C) : Sylow p Q) :
          Subgroup Q).map σ'.toMonoidHom = (P.mapSurjective (QuotientGroup.mk'_surjective C) :
            Sylow p Q) := by
        rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hσ]
      rintro _ ⟨b, hb, rfl⟩
      show QuotientGroup.mk' C (σ b) ∈ B'
      have e : QuotientGroup.mk' C (σ b) = σ' (QuotientGroup.mk' C b) :=
        (QuotientGroup.congr_mk C C σ hCσ' b).symm
      rw [e]
      exact hB'σ σ' hPσ ⟨_, hb, rfl⟩
  · -- `N_A(C) < A`: induction inside the normalizer
    set A₁ := normalizer (C : Set A) with hA₁def
    have hcard : Nat.card A₁ < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Subgroup.card_le_card_group A₁) ?_
      intro h
      exact hA₁ ((Subgroup.card_eq_iff_eq_top A₁).1 h)
    have hA₁' : ¬ NPC p (⊤ : Subgroup A₁) := fun h => hCN (by
      have := h.map A₁.subtype
      rwa [map_subtype_top] at this)
    obtain ⟨B₁, hB₁s, hB₁n, hB₁σ⟩ := ih _ hcard A₁ rfl (P.subtype hPN) hA₁'
    refine ⟨B₁.map A₁.subtype, ?_, ?_, ?_⟩
    · have := pSolSec_map A₁.subtype hB₁s
      rwa [Subgroup.map_bot] at this
    · intro hN
      exact hB₁n (NPC.of_map_injective A₁.subtype_injective hN)
    · intro σ hσ
      have hA₁σ : A₁.map σ.toMonoidHom = A₁ := normalizer_map_eq_of_map_eq (hCσ σ hσ)
      set σ₁ := restrictAut σ A₁ hA₁σ
      have hP₁ : ((P.subtype hPN : Sylow p A₁) : Subgroup A₁).map σ₁.toMonoidHom =
          (P.subtype hPN : Sylow p A₁) := by
        rw [Sylow.coe_subtype]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [SetLike.mem_coe, mem_subgroupOf] at hy
          rw [mem_subgroupOf]
          exact (apply_mem_iff_of_map_eq hσ _).2 hy
        · intro hx
          rw [mem_subgroupOf] at hx
          refine ⟨σ₁.symm x, ?_, by simp⟩
          rw [SetLike.mem_coe, mem_subgroupOf, ← apply_mem_iff_of_map_eq hσ]
          have : σ ((σ₁.symm x : A₁) : A) = (x : A) :=
            congrArg Subtype.val (σ₁.apply_symm_apply x)
          rw [this]
          exact hx
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨σ₁ b, hB₁σ σ₁ hP₁ ⟨b, hb, rfl⟩, rfl⟩

end Thompson


/-! ### `p`-soluble subgroups: normalizers of Sylow subgroups, joins, lifting -/

section PSolubleTools

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

lemma pSoluble_subgroupOf_iff {H K : Subgroup G} (hHK : H ≤ K) :
    PSoluble p (H.subgroupOf K) ↔ PSoluble p H := by
  constructor
  · intro h
    have := pSolSec_map K.subtype h
    rwa [Subgroup.map_bot, subgroupOf_map_subtype, inf_eq_left.mpr hHK] at this
  · rintro ⟨n, hn⟩
    refine ⟨n, le_of_eq ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 ?_)⟩
    rw [map_Dp_iterate, subgroupOf_map_subtype, inf_eq_left.mpr hHK]
    exact le_bot_iff.1 hn

/-- The join of two `p`-soluble subgroups, one normalizing the other, is `p`-soluble. -/
lemma pSoluble_sup_of_le_normalizer {A C : Subgroup G} (hA : PSoluble p A) (hC : PSoluble p C)
    (hCA : C ≤ normalizer (A : Set G)) : PSoluble p (A ⊔ C) := by
  set W := A ⊔ C
  haveI : (A.subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le (le_normalizer) hCA)
  have h1 := pSoluble_sup ((pSoluble_subgroupOf_iff le_sup_left).2 hA)
    ((pSoluble_subgroupOf_iff le_sup_right).2 hC)
  have h2 := pSolSec_map W.subtype h1
  rwa [Subgroup.map_bot, Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right] at h2

lemma mem_of_isPElt_of_coprime_relIndex {X T : Subgroup G} (hTX : T ≤ X)
    (hXT : X ≤ normalizer (T : Set G)) (hcop : Nat.Coprime (T.relIndex X) p) {x : G}
    (hx : x ∈ X) (hpx : IsPElt p x) : x ∈ T := by
  haveI : (T.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXT
  have h1 : (⟨x, hx⟩ : X) ^ (T.subgroupOf X).index ∈ T.subgroupOf X :=
    Subgroup.pow_index_mem _ _
  rw [mem_subgroupOf] at h1
  have hcop' : Nat.Coprime (T.subgroupOf X).index p := hcop
  obtain ⟨k, hk⟩ := hpx
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right k hcop') (by simpa using h1)
    (by rw [hk]; exact one_mem _)

/-- The normalizer, inside `N`, of a Sylow `p`-subgroup of `N` is `p`-soluble. -/
lemma pSoluble_inf_normalizer_of_isSylowOf {N T : Subgroup G}
    (hT : ABGLocalTools.IsSylowOf p T N) : PSoluble p (N ⊓ normalizer (T : Set G)) := by
  obtain ⟨Q, rfl⟩ := hT
  set T := (Q : Subgroup N).map N.subtype
  set X := N ⊓ normalizer (T : Set G)
  have hTN : T ≤ N := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hTX : T ≤ X := le_inf hTN le_normalizer
  have hcopN : ¬ p ∣ T.relIndex N := by
    have : T.subgroupOf N = (Q : Subgroup N) :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [Subgroup.relIndex, this]
    exact Q.not_dvd_index
  have hdvd : T.relIndex X ∣ T.relIndex N :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex T X N hTX inf_le_left)
  have hcopX : Nat.Coprime (T.relIndex X) p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h => hcopN (h.trans hdvd))
  have hsec : PSolSec p T X := by
    refine ⟨1, inf_le_right.trans ?_⟩
    rw [pGen, closure_le]
    rintro x ⟨hx, hpx⟩
    exact mem_of_isPElt_of_coprime_relIndex hTX inf_le_right hcopX hx hpx
  exact (pSoluble_of_isPGroup (Q.isPGroup'.map N.subtype)).trans hsec

/-- Frattini argument, inside a subgroup `M` containing a normal subgroup `V`. -/
lemma le_sup_inf_normalizer {V M : Subgroup G} [V.Normal] (hVM : V ≤ M) (Q : Sylow p V) :
    M ≤ V ⊔ (M ⊓ normalizer (((Q : Subgroup V).map V.subtype : Subgroup G) : Set G)) := by
  intro m hm
  have htop := Sylow.normalizer_sup_eq_top (N := V) Q
  have hm' : m ∈ normalizer (((Q : Subgroup V).map V.subtype : Subgroup G) : Set G) ⊔ V :=
    htop ▸ mem_top m
  obtain ⟨n, hn, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hm'
  have hnM : n ∈ M := by
    have := mul_mem hm (inv_mem (hVM hv))
    simpa using this
  have e : n * v = (n * v * n⁻¹) * n := by group
  rw [e]
  exact mul_mem (mem_sup_left ((inferInstance : V.Normal).conj_mem v hv n))
    (mem_sup_right ⟨hnM, hn⟩)

/-- **Lemma 3.1-type lifting.** Every `p`-soluble subgroup of a quotient `G/N` is the image of a
`p`-soluble subgroup of `G`. -/
lemma exists_pSoluble_lift (N : Subgroup G) [N.Normal] (H' : Subgroup (G ⧸ N))
    (hH : PSoluble p H') : ∃ H : Subgroup G, PSoluble p H ∧ H.map (QuotientGroup.mk' N) = H' := by
  obtain ⟨Q⟩ : Nonempty (Sylow p N) := inferInstance
  set T := (Q : Subgroup N).map N.subtype
  set M := H'.comap (QuotientGroup.mk' N)
  have hNM : N ≤ M := by
    intro n hn
    show QuotientGroup.mk' N n ∈ H'
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hfr := le_sup_inf_normalizer hNM Q
  set H := M ⊓ normalizer (T : Set G)
  refine ⟨H, ?_, ?_⟩
  · have h1 : PSoluble p (H ⊓ N) :=
      (pSoluble_inf_normalizer_of_isSylowOf ⟨Q, rfl⟩).mono
        (le_inf inf_le_right (inf_le_left.trans inf_le_right))
    obtain ⟨n, hn⟩ := hH
    refine h1.trans ⟨n, le_inf (Dp_iterate_le p n H) ?_⟩
    have h2 : ((Dp p)^[n] H).map (QuotientGroup.mk' N) ≤ ⊥ := by
      rw [map_Dp_iterate]
      refine (Dp_iterate_mono p n ?_).trans hn
      rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_left
    rw [le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
    exact h2
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.2 inf_le_left) ?_
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) H']
    refine (Subgroup.map_mono hfr).trans ?_
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]

end PSolubleTools


/-! ### The projection argument -/

section Projection

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]

/-- If `x ∈ T` moves the subgroup `L` to a subgroup `L'` commuting with `L` and meeting it
trivially, then every subgroup `B ≤ L` of a group `X` normalizing `T` inherits a normal
`p`-complement from `T`. -/
lemma npc_of_move {L L' T X B : Subgroup Y} (hLL : L ⊓ L' = ⊥)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) {x : Y} (hx : x ∈ T)
    (hL' : L' = L.map (MulAut.conj x).toMonoidHom) (hBL : B ≤ L) (hBX : B ≤ X)
    (hXT : X ≤ normalizer (T : Set Y)) (hT : NPC p T) : NPC p B := by
  let μ : L × L' →* Y := MonoidHom.noncommCoprod L.subtype L'.subtype
    (fun a b => show Commute (a : Y) (b : Y) from hcomm a a.2 b b.2)
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    replace hab : (a : Y) * b = 1 := hab
    have ha : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have hmem : (a : Y) ∈ L ⊓ L' := Subgroup.mem_inf.mpr ⟨a.2, by rw [ha]; exact inv_mem b.2⟩
    rw [hLL, mem_bot] at hmem
    have hb : (b : Y) = 1 := by rw [hmem, one_mul] at hab; exact hab
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  let e := MonoidHom.ofInjective hμ
  let πL : μ.range →* L := (MonoidHom.fst L L').comp e.symm.toMonoidHom
  set W : Subgroup μ.range := T.comap μ.range.subtype
  have hW : NPC p W := NPC.of_map_injective μ.range.subtype_injective
    (hT.mono (Subgroup.map_comap_le _ _))
  have hπW : NPC p (W.map πL) := hW.map πL
  set B' : Subgroup L := B.comap L.subtype
  have hB' : B' ≤ W.map πL := by
    intro b hb
    have hbX : (b : Y) ∈ X := hBX hb
    have hxb : x * (b : Y) * x⁻¹ ∈ L' := by
      rw [hL']; exact ⟨b, b.2, by simp [MulAut.conj_apply]⟩
    set w : L × L' := (b⁻¹, ⟨x * b * x⁻¹, hxb⟩)
    have hcT : (b : Y)⁻¹ * x * b * x⁻¹ ∈ T := by
      have h1 : (b : Y)⁻¹ * x * ((b : Y)⁻¹)⁻¹ ∈ T :=
        (mem_normalizer_iff.1 (hXT (inv_mem hbX)) x).1 hx
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem hx)
    have hμw : μ w = (b : Y)⁻¹ * x * b * x⁻¹ := by
      show ((b⁻¹ : L) : Y) * (x * b * x⁻¹) = _
      rw [coe_inv]
      group
    have hwW : e w ∈ W := by
      show ((e w : μ.range) : Y) ∈ T
      rw [MonoidHom.ofInjective_apply, hμw]
      exact hcT
    have : πL (e w) = b⁻¹ := by
      show (e.symm (e w)).1 = b⁻¹
      rw [MulEquiv.symm_apply_apply]
    have hinv : b⁻¹ ∈ W.map πL := ⟨e w, hwW, this⟩
    simpa using inv_mem hinv
  have hB'npc : NPC p B' := hπW.mono hB'
  have := hB'npc.map L.subtype
  rwa [Subgroup.map_comap_eq, range_subtype, inf_eq_right.mpr hBL] at this

end Projection

/-! ### The main proposition: `L_p(G/K_p(G)) < L_p(G)` -/

section Core

open CFSGOutside.NonsolubleLength

variable {p : ℕ} [hp : Fact p.Prime]

lemma pPrimeGen_top_normal {A : Type*} [Group A] [Finite A] :
    (pPrimeGen p (⊤ : Subgroup A)).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  refine le_trans ?_ (normalizer_le_normalizer_pPrimeGen (⊤ : Subgroup A))
  rw [normalizer_eq_top_iff.mpr inferInstance]

/-- A simple non-abelian group of order divisible by `p` has no normal `p`-complement. -/
lemma not_npc_of_simple {R : Type*} [Group R] [Finite R] [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) (hdvd : p ∣ Nat.card R) : ¬ NPC p (⊤ : Subgroup R) := by
  intro h
  haveI := pPrimeGen_top_normal (p := p) (A := R)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeGen p (⊤ : Subgroup R)) with hN | hN
  · have hP : IsPGroup p R := by
      intro g
      obtain ⟨k, hk⟩ := exists_pow_isPPrimeElt p g
      refine ⟨k, ?_⟩
      have := mem_pPrimeGen_of_isPPrimeElt (mem_top _) hk
      rw [hN, mem_bot] at this
      exact this
    haveI := hP.isNilpotent
    exact not_isSolvable_of_simple_nonab hnab inferInstance
  · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : y ∈ pGen p (pPrimeGen p (⊤ : Subgroup R)) := by
      rw [hN]
      exact mem_pGen_of_isPElt (mem_top _) ⟨1, by rw [pow_one, ← hy]; exact pow_orderOf_eq_one y⟩
    rw [h, mem_bot] at h1
    rw [h1, orderOf_one] at hy
    exact hp.out.one_lt.ne hy

instance kernelOf_components_normal (Y : Type) [Group Y] [Finite Y] :
    (kernelOf (components Y)).Normal :=
  kernelOf_normal (fun _ hS g => isComponent_conj hS g)

lemma map_map_conj {Y : Type*} [Group Y] [Finite Y] (L : Subgroup Y) (a b : Y) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map, conj_comp_conj]

end Core



section CoreThm

open CFSGOutside.NonsolubleLength

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Proposition in the proof of Theorem 1.1(b)** (Khukhro–Shumyatsky).  Let `p` be odd,
`G` not `p`-soluble, `Y = G/R_p(G)` and `K` the kernel of the action of `Y` on its components
(so `K/R_p` is `K_p(G)/R_p(G)`).  If all `p`-soluble subgroups of `Y` have `p`-length `≤ h`,
then `h ≥ 1` and every `p`-soluble subgroup `M/K` of `Y/K` has `p`-length `≤ h - 1`. -/
theorem pLength_quotient_kernel [ThompsonElementaryNormalPComplement.{0}] [Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] (hG : ¬ PSoluble p (⊤ : Subgroup G)) {h : ℕ}
    (hX : ∀ X : Subgroup (G ⧸ pSolRad p G), PSoluble p X → PLenLE p X h)
    (M : Subgroup (G ⧸ pSolRad p G)) (hKM : kernelOf (components (G ⧸ pSolRad p G)) ≤ M)
    (hM : PSolSec p (kernelOf (components (G ⧸ pSolRad p G))) M) :
    ∃ k, h = k + 1 ∧
      PLenLE p (M.map (QuotientGroup.mk' (kernelOf (components (G ⧸ pSolRad p G))))) k := by
  classical
  set Y := G ⧸ pSolRad p G
  have hF : fittingSubgroup Y = ⊥ := fittingSubgroup_quotient_pSolRad_eq_bot
  set K := kernelOf (components Y) with hKdef
  set V := layer Y
  have hFF := factorFamily_components hF
  haveI hVn : V.Normal := hFF.normal
  have hVK : V ≤ K := fun v hv => mem_kernelOf.2 fun S hS => hFF.normalizes S hS hv
  have hVM : V ≤ M := hVK.trans hKM
  have hVMs : PSolSec p V M := by
    obtain ⟨k, hk⟩ := dA_kernel_le_layer hF hCFSG
    exact (pSolSec_of_dA hk).trans hM
  -- a component exists, since `G` is not `p`-soluble
  obtain ⟨R₀, hR₀⟩ : ∃ R, IsComponent R := by
    by_contra hno
    push Not at hno
    have hV0 : V = ⊥ := by
      show layer Y = ⊥
      rw [layer.eq_sSup, sSup_eq_bot]
      intro K hK
      exact absurd hK (hno K)
    have hcen := centralizer_layer_eq_bot hF
    apply hG
    have htop : pSolRad p G = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (g : Y) ∈ centralizer (V : Set Y) := by
        rw [mem_centralizer_iff]
        intro v hv
        rw [hV0] at hv
        rw [mem_bot.mp hv, one_mul, mul_one]
      rw [hcen, mem_bot] at hg
      exact (QuotientGroup.eq_one_iff g).mp hg
    rw [← htop]
    exact pSoluble_pSolRad
  obtain ⟨P₀⟩ : Nonempty (Sylow p V) := inferInstance
  set P : Subgroup Y := (P₀ : Subgroup V).map V.subtype with hPdef
  have hPs : ABGLocalTools.IsSylowOf p P V := ⟨P₀, rfl⟩
  have hPV : P ≤ V := by rintro _ ⟨x, -, rfl⟩; exact x.2
  set NP := M ⊓ normalizer (P : Set Y) with hNPdef
  have hfr : M ≤ V ⊔ NP := le_sup_inf_normalizer hVM P₀
  have hNPs : PSoluble p NP := by
    have h1 : PSoluble p (V ⊓ NP) := (pSoluble_inf_normalizer_of_isSylowOf hPs).mono
      (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    have h2 := hVMs.inf NP
    rw [inf_eq_right.mpr (inf_le_left : NP ≤ M)] at h2
    exact h1.trans h2
  -- the orbits of `NP` on subgroups, with chosen representatives
  let rel : Subgroup Y → Subgroup Y → Prop :=
    fun L L' => ∃ g ∈ NP, L' = L.map (MulAut.conj g).toMonoidHom
  have hrel : Equivalence rel := by
    refine ⟨fun L => ⟨1, one_mem _, ?_⟩, ?_, ?_⟩
    · ext x; simp
    · rintro L L' ⟨g, hg, rfl⟩
      refine ⟨g⁻¹, inv_mem hg, ?_⟩
      rw [map_map_conj, inv_mul_cancel]
      ext x; simp
    · rintro L L' L'' ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
      exact ⟨g' * g, mul_mem hg' hg, map_map_conj _ _ _⟩
  let s : Setoid (Subgroup Y) := ⟨rel, hrel⟩
  let ρ : Subgroup Y → Subgroup Y := fun L => (Quotient.mk s L).out
  have hρ1 : ∀ L, rel (ρ L) L := fun L => Quotient.mk_out (s := s) L
  have hρ2 : ∀ L, ∀ x ∈ NP, ρ (L.map (MulAut.conj x).toMonoidHom) = ρ L := by
    intro L x hx
    show (Quotient.mk s _).out = (Quotient.mk s L).out
    congr 1
    apply Quotient.sound
    refine ⟨x⁻¹, inv_mem hx, ?_⟩
    rw [map_map_conj, inv_mul_cancel]
    ext y; simp
  choose a ha using hρ1
  have hρc : ∀ L, IsComponent L → IsComponent (ρ L) := by
    intro L hL
    have hLeq := (ha L).2
    have e : ρ L = L.map (MulAut.conj (a L)⁻¹).toMonoidHom :=
      calc ρ L = (ρ L).map (MulAut.conj ((a L)⁻¹ * a L)).toMonoidHom := by
            rw [inv_mul_cancel]; ext y; simp
        _ = ((ρ L).map (MulAut.conj (a L)).toMonoidHom).map
              (MulAut.conj (a L)⁻¹).toMonoidHom := (map_map_conj _ _ _).symm
        _ = L.map (MulAut.conj (a L)⁻¹).toMonoidHom := by rw [← hLeq]
    rw [e]
    exact isComponent_conj hL _
  -- Sylow subgroups of the components and the local subgroups `B_R`
  have hβ : ∀ R : Subgroup Y, IsComponent R → ∃ Q : Sylow p R,
      (Q : Subgroup R).map R.subtype = P ⊓ R ∧ ∃ B : Subgroup R, PSoluble p B ∧ ¬ NPC p B ∧
        ∀ σ : MulAut R, (Q : Subgroup R).map σ.toMonoidHom = Q → B.map σ.toMonoidHom ≤ B := by
    intro R hR
    obtain ⟨Q, hQ⟩ := ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPs (hFF.le R hR)
      (hFF.normalizes R hR)
    haveI := component_isSimple hF hR
    have hRn : ¬ NPC p (⊤ : Subgroup R) :=
      not_npc_of_simple (nonab_component hF ⟨R, hR⟩) (p_dvd_card_component hR)
    obtain ⟨B, hB⟩ := exists_pSoluble_not_npc hp2 _ R rfl Q hRn
    exact ⟨Q, hQ, B, hB⟩
  choose Q hQ B hB using hβ
  let Bt : Subgroup Y → Subgroup Y :=
    fun R => if hR : IsComponent R then (B R hR).map R.subtype else ⊥
  let BL : Subgroup Y → Subgroup Y :=
    fun L => (Bt (ρ L)).map (MulAut.conj (a L)).toMonoidHom
  have hBt_le : ∀ R, Bt R ≤ R := by
    intro R
    by_cases hR : IsComponent R
    · simp only [Bt, dif_pos hR]
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · simp only [Bt, dif_neg hR]
      exact bot_le
  have hBt_inv : ∀ R, IsComponent R → ∀ y ∈ NP, R.map (MulAut.conj y).toMonoidHom = R →
      (Bt R).map (MulAut.conj y).toMonoidHom = Bt R := by
    intro R hR y hy hRy
    simp only [Bt, dif_pos hR]
    set σ := restrictAut (MulAut.conj y) R hRy
    have hcomm : (MulAut.conj y).toMonoidHom.comp R.subtype = R.subtype.comp σ.toMonoidHom := by
      ext z; rfl
    have hPy : P.map (MulAut.conj y).toMonoidHom = P :=
      map_conj_eq_of_mem_normalizer (Subgroup.mem_inf.mp hy).2
    have hQσ : ((Q R hR : Sylow p R) : Subgroup R).map σ.toMonoidHom = Q R hR := by
      apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_map, ← hcomm, ← Subgroup.map_map, hQ R hR,
        Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective, hPy, hRy]
    have hle := (hB R hR).2.2 σ hQσ
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_map, hcomm, ← Subgroup.map_map]
      exact Subgroup.map_mono hle
    · exact (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
  have hBL_le : ∀ L, IsComponent L → BL L ≤ L := by
    intro L _
    calc BL L ≤ (ρ L).map (MulAut.conj (a L)).toMonoidHom := Subgroup.map_mono (hBt_le _)
      _ = L := (ha L).2.symm
  have hBL_conj : ∀ L, IsComponent L → ∀ x ∈ NP,
      (BL L).map (MulAut.conj x).toMonoidHom = BL (L.map (MulAut.conj x).toMonoidHom) := by
    intro L hL x hx
    have hρ' : ρ (L.map (MulAut.conj x).toMonoidHom) = ρ L := hρ2 L x hx
    have hR : IsComponent (ρ L) := hρc L hL
    have h1 : L = (ρ L).map (MulAut.conj (a L)).toMonoidHom := (ha L).2
    obtain ⟨ha'NP, h2'⟩ := ha (L.map (MulAut.conj x).toMonoidHom)
    rw [hρ'] at h2'
    show ((Bt (ρ L)).map (MulAut.conj (a L)).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      (Bt (ρ (L.map (MulAut.conj x).toMonoidHom))).map
        (MulAut.conj (a (L.map (MulAut.conj x).toMonoidHom))).toMonoidHom
    rw [hρ']
    generalize a (L.map (MulAut.conj x).toMonoidHom) = a' at ha'NP h2' ⊢
    have hy : a'⁻¹ * x * a L ∈ NP := mul_mem (mul_mem (inv_mem ha'NP) hx) (ha L).1
    have hRy : (ρ L).map (MulAut.conj (a'⁻¹ * x * a L)).toMonoidHom = ρ L :=
      calc (ρ L).map (MulAut.conj (a'⁻¹ * x * a L)).toMonoidHom
          = (((ρ L).map (MulAut.conj (a L)).toMonoidHom).map (MulAut.conj x).toMonoidHom).map
              (MulAut.conj a'⁻¹).toMonoidHom := by
            rw [map_map_conj, map_map_conj, mul_assoc]
        _ = ((ρ L).map (MulAut.conj a').toMonoidHom).map (MulAut.conj a'⁻¹).toMonoidHom := by
            rw [← h1, h2']
        _ = ρ L := by
            rw [map_map_conj, inv_mul_cancel]
            ext z; simp
    have hinv := hBt_inv (ρ L) hR _ hy hRy
    calc ((Bt (ρ L)).map (MulAut.conj (a L)).toMonoidHom).map (MulAut.conj x).toMonoidHom
        = (Bt (ρ L)).map (MulAut.conj (x * a L)).toMonoidHom := map_map_conj _ _ _
      _ = ((Bt (ρ L)).map (MulAut.conj (a'⁻¹ * x * a L)).toMonoidHom).map
            (MulAut.conj a').toMonoidHom := by
          rw [map_map_conj]
          congr 3
          group
      _ = (Bt (ρ L)).map (MulAut.conj a').toMonoidHom := by rw [hinv]
  have hBL_npc : ∀ L, IsComponent L → ¬ NPC p (BL L) := by
    intro L hL hN
    have hR := hρc L hL
    apply (hB (ρ L) hR).2.1
    have h1 := NPC.of_map_injective (MulAut.conj (a L)).injective hN
    simp only [Bt, dif_pos hR] at h1
    exact NPC.of_map_injective (ρ L).subtype_injective h1
  have hBL_ps : ∀ L, IsComponent L → PSoluble p (BL L) := by
    intro L hL
    have hR := hρc L hL
    have h1 := pSolSec_map (ρ L).subtype (hB (ρ L) hR).1
    rw [Subgroup.map_bot] at h1
    have h2 := pSolSec_map (MulAut.conj (a L)).toMonoidHom h1
    rw [Subgroup.map_bot] at h2
    have e : BL L = ((B (ρ L) hR).map (ρ L).subtype).map (MulAut.conj (a L)).toMonoidHom := by
      simp only [BL, Bt, dif_pos hR]
    rw [e]
    exact h2
  -- the join of the `B_L`
  set B0 := ⨆ L ∈ components Y, BL L with hB0def
  have hcompfin : (components Y).Finite := Set.toFinite _
  have hB0eq : B0 = ⨆ L ∈ hcompfin.toFinset, BL L := by
    simp only [B0, Set.Finite.mem_toFinset]
  have hB0s : PSoluble p B0 := by
    rw [hB0eq]
    have key : ∀ S : Finset (Subgroup Y), (∀ L ∈ S, IsComponent L) →
        PSoluble p (⨆ L ∈ S, BL L) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.notMem_empty, iSup_false, iSup_bot]
        exact ⟨0, le_rfl⟩
      | insert L₀ S hL₀ ih =>
        intro hS
        rw [Finset.iSup_insert]
        have hL₀c := hS L₀ (Finset.mem_insert_self _ _)
        have hrest := ih (fun L hL => hS L (Finset.mem_insert_of_mem hL))
        rw [sup_comm]
        refine pSoluble_sup_of_le_normalizer hrest (hBL_ps L₀ hL₀c) ?_
        refine le_trans ?_ (centralizer_le_normalizer' _)
        rw [Subgroup.le_centralizer_iff]
        refine iSup₂_le fun L hL => ?_
        have hLc := hS L (Finset.mem_insert_of_mem hL)
        have hne : L ≠ L₀ := fun h => hL₀ (h ▸ hL)
        rcases distinct_components_commute hLc hL₀c with h | h
        · exact absurd h hne
        · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
          exact (hBL_le L hLc).trans (this.trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hBL_le L₀ hL₀c))))
    exact key _ (fun L hL => hcompfin.mem_toFinset.mp hL)
  have hB0n : NP ≤ normalizer (B0 : Set Y) := by
    intro x hx
    apply mem_normalizer_of_map_conj_eq
    have hle : B0.map (MulAut.conj x).toMonoidHom ≤ B0 := by
      rw [hB0def, Subgroup.map_iSup]
      refine iSup_le fun L => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hL => ?_
      rw [hBL_conj L hL x hx]
      exact le_biSup BL (isComponent_conj hL x)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  set X := B0 ⊔ NP with hXdef
  have hXs : PSoluble p X := pSoluble_sup_of_le_normalizer hB0s hNPs hB0n
  have hB0V : B0 ≤ V := iSup₂_le fun L hL => (hBL_le L hL).trans (hFF.le L hL)
  have hXM : X ≤ M := sup_le (hB0V.trans hVM) inf_le_left
  have hPNP : P ≤ NP := le_inf (hPV.trans hVM) le_normalizer
  -- a nontrivial `p`-element of `P`
  obtain ⟨z, hzP, hz1⟩ : ∃ z ∈ P, z ≠ 1 := by
    have hQne : ((Q R₀ hR₀ : Sylow p R₀) : Subgroup R₀) ≠ ⊥ :=
      (Q R₀ hR₀).ne_bot_of_dvd_card (p_dvd_card_component hR₀)
    obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQne
    have hqP : (q : Y) ∈ P ⊓ R₀ := by
      rw [← hQ R₀ hR₀]
      exact ⟨q, hq, rfl⟩
    refine ⟨q, hqP.1, fun h => hq1 (Subtype.ext (Subtype.ext h))⟩
  have hzp : IsPElt p z := by
    obtain ⟨k, hk⟩ := (P₀.isPGroup'.map V.subtype) ⟨z, hzP⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hXh := hX X hXs
  rcases h with _ | k
  · exfalso
    unfold PLenLE at hXh
    rw [Function.iterate_zero, id] at hXh
    have := mem_pGen_of_isPElt ((hPNP.trans (le_sup_right : NP ≤ X)) hzP) hzp
    rw [hXh, mem_bot] at this
    exact hz1 this
  · refine ⟨k, rfl, ?_⟩
    set T := pGen p ((lowerStep p)^[k] X) with hTdef
    have hT : NPC p T := pLenLE_succ_iff.1 hXh
    have hXT : X ≤ normalizer (T : Set Y) := le_normalizer.trans
      ((normalizer_le_normalizer_lowerStep_iterate k X).trans
        (normalizer_le_normalizer_pGen _))
    have hTK : T ≤ K := by
      intro x hxT
      rw [mem_kernelOf]
      intro L hL
      by_contra hxL
      have hL' : IsComponent (L.map (MulAut.conj x).toMonoidHom) := isComponent_conj hL x
      have hne : L ≠ L.map (MulAut.conj x).toMonoidHom :=
        fun h => hxL (mem_normalizer_of_map_conj_eq h.symm)
      have hdisj := hFF.disj L hL _ hL' hne
      have hcomm : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, a * b = b * a := by
        rcases distinct_components_commute hL hL' with h | h
        · exact absurd h hne
        · intro a ha b hb
          exact (mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
      have hBX : BL L ≤ X := (le_biSup BL hL).trans le_sup_left
      exact hBL_npc L hL (npc_of_move hdisj hcomm hxT rfl (hBL_le L hL) hBX hXT hT)
    have hMX : M.map (QuotientGroup.mk' K) = X.map (QuotientGroup.mk' K) := by
      apply le_antisymm
      · calc M.map (QuotientGroup.mk' K) ≤ (V ⊔ NP).map (QuotientGroup.mk' K) :=
              Subgroup.map_mono hfr
          _ ≤ (K ⊔ X).map (QuotientGroup.mk' K) :=
              Subgroup.map_mono (sup_le_sup hVK le_sup_right)
          _ = X.map (QuotientGroup.mk' K) := by
              rw [Subgroup.map_sup]
              have : K.map (QuotientGroup.mk' K) = ⊥ := by
                rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
              rw [this, bot_sup_eq]
      · exact Subgroup.map_mono hXM
    unfold PLenLE
    rw [hMX, ← map_lowerStep_iterate, ← map_pGen, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hTK

end CoreThm


section Main

open CFSGOutside.NonsolubleLength

variable {p : ℕ} [hp : Fact p.Prime]

lemma pLenLE_quotient_pSolRad {G : Type} [Group G] [Finite G] {h : ℕ}
    (hH : ∀ H : Subgroup G, PSoluble p H → PLenLE p H h) :
    ∀ X : Subgroup (G ⧸ pSolRad p G), PSoluble p X → PLenLE p X h := by
  intro X hX
  obtain ⟨H, hHs, rfl⟩ := exists_pSoluble_lift (pSolRad p G) X hX
  exact (hH H hHs).map _

/-- **Khukhro–Shumyatsky, Theorem 1.1(b)**, in the working form: for `p` odd, if every
`p`-soluble subgroup of `G` has `p`-length at most `h`, then `λ_p(G) ≤ h`. -/
theorem nonPSolubleLengthLE_of_pLenLE [ThompsonElementaryNormalPComplement.{0}] [Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    (hp2 : p ≠ 2) : ∀ (h : ℕ) (G : Type) [Group G] [Finite G],
      (∀ H : Subgroup G, PSoluble p H → PLenLE p H h) → NonPSolubleLengthLE p G h := by
  intro h
  induction h with
  | zero =>
    intro G _ _ hH
    by_cases hG : PSoluble p (⊤ : Subgroup G)
    · exact nonPSolubleLengthLE_zero_of_pSoluble p G hG
    · exfalso
      obtain ⟨k, hk, -⟩ := pLength_quotient_kernel hCFSG hp2 hG (pLenLE_quotient_pSolRad hH)
        (kernelOf (components (G ⧸ pSolRad p G))) le_rfl (pSolSec_of_le le_rfl)
      omega
  | succ k ih =>
    intro G _ _ hH
    by_cases hG : PSoluble p (⊤ : Subgroup G)
    · exact (nonPSolubleLengthLE_zero_of_pSoluble p G hG).mono (Nat.zero_le _)
    · apply nonPSolubleLengthLE_succ_of_pKernel hCFSG
      apply ih
      intro H' hH'
      set R := pSolRad p G
      set Y := G ⧸ R
      set K := kernelOf (components Y)
      have hmap : (pKernel p G).map (QuotientGroup.mk' R) = K :=
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) _
      let ε : Y ⧸ K ≃* G ⧸ pKernel p G := (QuotientGroup.quotientMulEquivOfEq hmap).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient R (pKernel p G) pSolRad_le_pKernel)
      set Hb := H'.map ε.symm.toMonoidHom
      have hHb : PSoluble p Hb := by
        have := pSolSec_map ε.symm.toMonoidHom hH'
        rwa [Subgroup.map_bot] at this
      set M := Hb.comap (QuotientGroup.mk' K)
      have hKM : K ≤ M := by
        intro x hx
        show QuotientGroup.mk' K x ∈ Hb
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
        exact one_mem _
      have hM : PSolSec p K M := by
        have := pSolSec_comap (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) hHb
        rwa [comap_mk_bot] at this
      obtain ⟨k', hk', hlen⟩ := pLength_quotient_kernel hCFSG hp2 hG
        (pLenLE_quotient_pSolRad hH) M hKM hM
      obtain rfl : k = k' := by omega
      rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K)] at hlen
      have := hlen.map ε.toMonoidHom
      rwa [Subgroup.map_map, show ε.toMonoidHom.comp ε.symm.toMonoidHom = MonoidHom.id _ by
        ext x; simp, Subgroup.map_id] at this

end Main


/-! ### The paper's literal definitions and the crosswalk -/

section Literal

open CFSGOutside.KhukhroShumyatskyNonsolubleLength (PaperSeries PaperSeries.count card_filter_Ico_succ
  count_eq)

universe u

variable (p : ℕ) {X : Type u} [Group X]

variable {p} [hp : Fact p.Prime] [Finite X]

lemma eq_one_of_pow_coprime {Q : Type*} [Group Q] {q : Q} {m n : ℕ} (hmn : m.Coprime n)
    (hm : q ^ m = 1) (hn : q ^ n = 1) : q = 1 := by
  have : q ∈ (⊥ : Subgroup Q) :=
    mem_of_pow_mem_of_coprime hmn (by rw [hm]; exact one_mem _) (by rw [hn]; exact one_mem _)
  exact this

lemma pGen_le_of_pPrimeFactor {A B U : Subgroup X} (hAB : A ≤ B) (hf : PPrimeFactor p A B)
    (hUB : U ≤ B) : pGen p U ≤ A := by
  obtain ⟨_, hcop⟩ := hf
  rw [pGen, closure_le]
  rintro x ⟨hx, k, hk⟩
  have hq : ((⟨x, hUB hx⟩ : B) : B ⧸ A.subgroupOf B) = 1 := by
    apply eq_one_of_pow_coprime (Nat.Coprime.pow_right k hcop) pow_card_eq_one'
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hUB hx⟩ : B) ^ (p ^ k) = 1 := Subtype.ext hk
    rw [this, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hq
  exact hq

lemma pPrimeGen_le_of_pFactor {A B U : Subgroup X} (hAB : A ≤ B) (hf : PFactor p A B)
    (hUB : U ≤ B) : pPrimeGen p U ≤ A := by
  obtain ⟨_, hP⟩ := hf
  rw [pPrimeGen, closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  obtain ⟨k, hk⟩ := hP ((⟨x, hUB hx⟩ : B) : B ⧸ A.subgroupOf B)
  have hq : ((⟨x, hUB hx⟩ : B) : B ⧸ A.subgroupOf B) = 1 := by
    apply eq_one_of_pow_coprime (Nat.Coprime.pow_right k hm) _ hk
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hUB hx⟩ : B) ^ m = 1 := Subtype.ext hxm
    rw [this, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hq
  exact hq

lemma pGen_pGen (S : Subgroup X) : pGen p (pGen p S) = pGen p S := by
  refine le_antisymm (pGen_le p _) ?_
  rw [pGen, closure_le]
  rintro x ⟨hx, hpx⟩
  exact mem_pGen_of_isPElt (subset_closure ⟨hx, hpx⟩) hpx

open Classical in
/-- A paper series with `c` factors that are not `p'`-groups gives `p`-length `≤ c`. -/
lemma pLenLE_of_paperSeries (s : PaperSeries X (POrPPrime p)) :
    PLenLE p (⊤ : Subgroup X) (s.count (PPrimeFactor p)) := by
  let c : ℕ → ℕ := fun j =>
    ((Finset.Ico j s.n).filter fun i => ¬ PPrimeFactor p (s.G i) (s.G (i + 1))).card
  have key : ∀ d, ∀ j, j + d = s.n → pGen p ((lowerStep p)^[c j] ⊤) ≤ s.G j := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hc : c j = 0 := by simp [c, show j = s.n by omega]
      rw [hc, show j = s.n by omega, s.top]
      exact le_top
    | succ d ih =>
      intro j hj
      have hjn : j < s.n := by omega
      have ih' := ih (j + 1) (by omega)
      have hcj := card_filter_Ico_succ (fun i => ¬ PPrimeFactor p (s.G i) (s.G (i + 1))) hjn
      have hmono := s.mono j hjn
      by_cases hf : PPrimeFactor p (s.G j) (s.G (j + 1))
      · have hc : c j = c (j + 1) := by simp only [c, hcj, hf, not_true_eq_false, if_false,
          add_zero]
        rw [hc, ← pGen_pGen]
        exact pGen_le_of_pPrimeFactor hmono hf ih'
      · have hc : c j = c (j + 1) + 1 := by simp only [c, hcj, hf, not_false_eq_true, if_true]
        have hpf : PFactor p (s.G j) (s.G (j + 1)) := (s.factor j hjn).resolve_right hf
        rw [hc, Function.iterate_succ_apply']
        exact (pGen_le p _).trans (pPrimeGen_le_of_pFactor hmono hpf ih')
  have h0 := key s.n 0 (by omega)
  rw [s.zero, le_bot_iff] at h0
  unfold PLenLE
  rw [count_eq]
  exact h0

lemma pFactor_Dp_pGen (U : Subgroup X) [(Dp p U).Normal] :
    ∃ _ : ((Dp p U).subgroupOf (pGen p U)).Normal,
      IsPGroup p (pGen p U ⧸ (Dp p U).subgroupOf (pGen p U)) := by
  refine ⟨inferInstance, fun q => ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := exists_pow_isPPrimeElt p x
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
  exact ⟨mem_pPrimeGen_of_isPPrimeElt (pow_mem (pGen_le p U hx) _) hk, pow_mem hx _⟩

lemma pPrimeFactor_pGen (U : Subgroup X) [(pGen p U).Normal] :
    ∃ _ : ((pGen p U).subgroupOf U).Normal,
      Nat.Coprime (Nat.card (U ⧸ (pGen p U).subgroupOf U)) p := by
  refine ⟨inferInstance, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hxm⟩ := exists_coprime_pow_isPElt p x
  have h1 : ((⟨x, hx⟩ : U) : U ⧸ (pGen p U).subgroupOf U) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact mem_pGen_of_isPElt (pow_mem hx _) hxm
  have := orderOf_dvd_of_pow_eq_one h1
  rw [hq] at this
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 (Nat.coprime_comm.1 hm) this

lemma pGen_normal (S : Subgroup X) [S.Normal] : (pGen p S).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  refine le_trans ?_ (normalizer_le_normalizer_pGen S)
  rw [normalizer_eq_top_iff.mpr inferInstance]

/-- A `p`-soluble group (in the `Dp` sense) has a paper series. -/
lemma paperPSoluble_of_pSoluble (h : PSoluble p (⊤ : Subgroup X)) : paperPSoluble p X := by
  obtain ⟨n, hn⟩ := h
  let D : ℕ → Subgroup X := fun j => (Dp p)^[j] ⊤
  haveI hDn : ∀ j, (D j).Normal := fun j => Dp_iterate_normal p j ⊤
  have hDsucc : ∀ j, D (j + 1) = Dp p (D j) := fun j => Function.iterate_succ_apply' _ _ _
  let Gs : ℕ → Subgroup X := fun i => if i % 2 = 0 then D (n - i / 2) else pGen p (D (n - i / 2 - 1))
  have hev : ∀ j, Gs (2 * j) = D (n - j) := by
    intro j
    simp only [Gs, show 2 * j % 2 = 0 by omega, show 2 * j / 2 = j by omega, if_true]
  have hod : ∀ j, Gs (2 * j + 1) = pGen p (D (n - j - 1)) := by
    intro j
    simp only [Gs, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
    rfl
  have hnorm : ∀ i, (Gs i).Normal := by
    intro i
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev]; exact hDn _
    · rw [hod]; haveI := hDn (n - j - 1); exact pGen_normal _
  have hmono : ∀ i < 2 * n, Gs i ≤ Gs (i + 1) := by
    intro i hi
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev, hod, show n - j = (n - j - 1) + 1 by omega, hDsucc]
      exact inf_le_right
    · rw [hod, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, hev,
        show n - (j + 1) = n - j - 1 by omega]
      exact pGen_le p _
  have hfac : ∀ i < 2 * n, POrPPrime p (Gs i) (Gs (i + 1)) := by
    intro i hi
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev, hod, show n - j = (n - j - 1) + 1 by omega, hDsucc]
      haveI : (Dp p (D (n - j - 1))).Normal := by rw [← hDsucc]; exact hDn _
      exact Or.inl (pFactor_Dp_pGen _)
    · rw [hod, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, hev,
        show n - (j + 1) = n - j - 1 by omega]
      haveI := hDn (n - j - 1)
      haveI : (pGen p (D (n - j - 1))).Normal := pGen_normal _
      exact Or.inr (pPrimeFactor_pGen _)
  refine ⟨{ n := 2 * n, G := Gs, normal := fun i _ => hnorm i, mono := hmono, zero := ?_,
            top := ?_, factor := hfac }⟩
  · rw [show (0 : ℕ) = 2 * 0 from rfl, hev, Nat.sub_zero]
    exact le_bot_iff.1 hn
  · rw [hev, Nat.sub_self]
    rfl

lemma pSoluble_top_iff_subgroup (H : Subgroup X) :
    PSoluble p (⊤ : Subgroup H) ↔ PSoluble p H := by
  rw [← subgroupOf_self, pSoluble_subgroupOf_iff le_rfl]

/-- A `p`-soluble section (in the `Dp` sense) is `p`-soluble in the paper's sense. -/
lemma pSolFactor_of_pSolSec {A B : Subgroup X} [A.Normal] (h : PSolSec p A B) :
    PSolFactor p A B := by
  refine ⟨inferInstance, paperPSoluble_of_pSoluble ?_⟩
  obtain ⟨n, hn⟩ := h
  set φ := QuotientGroup.mk' (A.subgroupOf B)
  refine ⟨n, le_of_eq ?_⟩
  rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (A.subgroupOf B)) ⊤,
    comap_top, ← map_Dp_iterate, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro x hx
  rw [mem_subgroupOf]
  apply hn
  have := Subgroup.mem_map_of_mem B.subtype hx
  rwa [map_Dp_iterate, map_subtype_top] at this

/-- A series as in `λ_p(X) ≤ h` is a paper series with at most `h` non-`p`-soluble factors. -/
lemma exists_paperSeries_of_nonPSolubleLengthLE {h : ℕ} (H : NonPSolubleLengthLE p X h) :
    ∃ s : PaperSeries X (PSolOrSemisimpleP p), s.count (PSolFactor p) ≤ h := by
  classical
  obtain ⟨t⟩ := H
  have hex : ∃ s : PaperSeries X (PSolOrSemisimpleP p), s.count (PSolFactor p) ≤ h := by
    refine ⟨{ n := 2 * h + 1, G := t.G, normal := fun i _ => t.normal i, mono := t.mono,
              zero := t.zero, top := t.top, factor := fun i hi => ?_ }, ?_⟩
    · rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · haveI := t.normal (j + j)
        exact Or.inl (pSolFactor_of_pSolSec (by rw [← two_mul]; exact t.psol j (by omega)))
      · exact Or.inr (t.semisimple j (by omega))
    · rw [PaperSeries.count]
      refine (Finset.card_le_card (t := (Finset.range h).image fun j => 2 * j + 1) ?_).trans
        Finset.card_image_le |>.trans (by simp)
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_image, Finset.mem_range]
      rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exfalso
        apply hi.2
        haveI := t.normal (j + j)
        exact pSolFactor_of_pSolSec (by rw [← two_mul]; exact t.psol j (by omega))
      · exact ⟨j, by omega, rfl⟩
  exact hex

/-- From `λ_p(X) ≤ h` to the paper's non-`p`-soluble length. -/
lemma paperNonPSolubleLength_le {h : ℕ} (H : NonPSolubleLengthLE p X h) :
    paperNonPSolubleLength p X ≤ h := by
  obtain ⟨s, hs⟩ := exists_paperSeries_of_nonPSolubleLengthLE H
  unfold paperNonPSolubleLength
  exact (Nat.sInf_le (show s.count (PSolFactor p) ∈
    {k | ∃ s : PaperSeries X (PSolOrSemisimpleP p), s.count (PSolFactor p) = k} from
      ⟨s, rfl⟩)).trans hs

end Literal

/-! ### Crosswalks: the paper's definitions agree with the working ones -/

section Crosswalk

open CFSGOutside.KhukhroShumyatskyNonsolubleLength (PaperSeries PaperSeries.count card_filter_Ico_succ
  count_eq sInf_eq_of_bounds)

universe u

variable {p : ℕ} [hp : Fact p.Prime] {X : Type u} [Group X] [Finite X]

/-- `p`-solubility: the paper's definition agrees with the `Dp`-definition. -/
theorem paperPSoluble_iff : paperPSoluble p X ↔ PSoluble p (⊤ : Subgroup X) :=
  ⟨fun ⟨s⟩ => (pLenLE_of_paperSeries s).pSoluble, paperPSoluble_of_pSoluble⟩

/-- A paper `p`-soluble section is `p`-soluble in the `Dp` sense. -/
lemma pSolSec_of_pSolFactor {A B : Subgroup X} (h : PSolFactor p A B) : PSolSec p A B := by
  obtain ⟨_, hs⟩ := h
  obtain ⟨n, hn⟩ := paperPSoluble_iff.1 hs
  refine ⟨n, ?_⟩
  set φ := QuotientGroup.mk' (A.subgroupOf B)
  have h1 : ((Dp p)^[n] (⊤ : Subgroup B)).map φ = ⊥ := by
    rw [map_Dp_iterate, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_bot_iff.1 hn
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  have h2 := Subgroup.map_mono (f := B.subtype) h1
  rw [map_Dp_iterate, map_subtype_top, subgroupOf_map_subtype] at h2
  exact h2.trans inf_le_left

lemma pFactor_pPrimeGen (W : Subgroup X) [(pPrimeGen p W).Normal] :
    ∃ _ : ((pPrimeGen p W).subgroupOf W).Normal,
      IsPGroup p (W ⧸ (pPrimeGen p W).subgroupOf W) := by
  refine ⟨inferInstance, fun q => ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := exists_pow_isPPrimeElt p x
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
  exact mem_pPrimeGen_of_isPPrimeElt (pow_mem hx _) hk

lemma pPrimeGen_normal (S : Subgroup X) [S.Normal] : (pPrimeGen p S).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  refine le_trans ?_ (normalizer_le_normalizer_pPrimeGen S)
  rw [normalizer_eq_top_iff.mpr inferInstance]

lemma lowerStep_iterate_normal (n : ℕ) : ((lowerStep p)^[n] (⊤ : Subgroup X)).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  refine le_trans ?_ (normalizer_le_normalizer_lowerStep_iterate n (⊤ : Subgroup X))
  rw [normalizer_eq_top_iff.mpr inferInstance]

open Classical in
/-- The lower `p`-series of a group of `p`-length `≤ l` is a paper series with at most `l`
`p`-factors. -/
lemma exists_paperSeries_of_pLenLE {l : ℕ} (h : PLenLE p (⊤ : Subgroup X) l) :
    ∃ s : PaperSeries X (POrPPrime p), s.count (PPrimeFactor p) ≤ l := by
  let S : ℕ → Subgroup X := fun j => (lowerStep p)^[j] ⊤
  haveI hSn : ∀ j, (S j).Normal := fun j => lowerStep_iterate_normal j
  have hSsucc : ∀ j, S (j + 1) = pPrimeGen p (pGen p (S j)) :=
    fun j => Function.iterate_succ_apply' _ _ _
  -- ascending terms: `G (2i) = pGen (S (l - i))`, `G (2i+1) = S (l - i)`
  let Gs : ℕ → Subgroup X := fun i =>
    if i % 2 = 0 then pGen p (S (l - i / 2)) else S (l - i / 2)
  have hev : ∀ i, Gs (2 * i) = pGen p (S (l - i)) := by
    intro i
    simp only [Gs, show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega, if_true]
  have hod : ∀ i, Gs (2 * i + 1) = S (l - i) := by
    intro i
    simp only [Gs, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]
    rfl
  have hnorm : ∀ i, (Gs i).Normal := by
    intro i
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev]; exact pGen_normal _
    · rw [hod]; exact hSn _
  have hmono : ∀ i < 2 * l + 1, Gs i ≤ Gs (i + 1) := by
    intro i hi
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev, hod]; exact pGen_le p _
    · rw [hod, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, hev,
        show l - j = (l - (j + 1)) + 1 by omega, hSsucc]
      exact pPrimeGen_le p _
  have hfac : ∀ i < 2 * l + 1, POrPPrime p (Gs i) (Gs (i + 1)) := by
    intro i hi
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hev, hod]
      haveI : (pGen p (S (l - j))).Normal := pGen_normal _
      exact Or.inr (pPrimeFactor_pGen _)
    · rw [hod, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, hev,
        show l - j = (l - (j + 1)) + 1 by omega, hSsucc]
      haveI : (pGen p (S (l - (j + 1)))).Normal := pGen_normal _
      haveI : (pPrimeGen p (pGen p (S (l - (j + 1))))).Normal := pPrimeGen_normal _
      exact Or.inl (pFactor_pPrimeGen _)
  refine ⟨{ n := 2 * l + 1, G := Gs, normal := fun i _ => hnorm i, mono := hmono,
            zero := ?_, top := ?_, factor := hfac }, ?_⟩
  · rw [show (0 : ℕ) = 2 * 0 from rfl, hev, Nat.sub_zero]
    exact h
  · rw [hod, Nat.sub_self]
    rfl
  · rw [PaperSeries.count]
    refine (Finset.card_le_card (t := (Finset.range l).image fun j => 2 * j + 1) ?_).trans
      Finset.card_image_le |>.trans (by simp)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_image, Finset.mem_range]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · exfalso
      apply hi.2
      show PPrimeFactor p (Gs (2 * j)) (Gs (2 * j + 1))
      rw [hev, hod]
      haveI : (pGen p (S (l - j))).Normal := pGen_normal _
      exact pPrimeFactor_pGen _
    · exact ⟨j, by omega, rfl⟩

/-- **Crosswalk.** The paper's `p`-length is the least `l` with `p`-length `≤ l` in the sense of
the lower `p`-series. -/
theorem paperPLength_eq :
    paperPLength p X = sInf {l | PLenLE p (⊤ : Subgroup X) l} := by
  unfold paperPLength
  apply sInf_eq_of_bounds
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, pLenLE_of_paperSeries s, le_rfl⟩
  · intro l hl
    obtain ⟨s, hs⟩ := exists_paperSeries_of_pLenLE hl
    exact ⟨_, ⟨s, rfl⟩, hs⟩

/-- The one-term series `X = G₀ = G₁`. -/
def NSeriesP.topSeries : NSeriesP p X ⊤ 0 where
  G _ := ⊤
  normal _ := normal_top
  mono _ _ := le_rfl
  zero := rfl
  top := rfl
  psol _ _ := ⟨0, le_rfl⟩
  semisimple i hi := absurd hi (Nat.not_lt_zero _)

/-- Prepend a `p`-soluble factor `N/M` at the bottom. -/
def NSeriesP.consPSol {M N : Subgroup X} [hM : M.Normal] {h : ℕ} (t : NSeriesP p X N h)
    (hMN : M ≤ N) (hs : PSolSec p M N) : NSeriesP p X M h where
  G i := match i with
    | 0 => M
    | j + 1 => t.G (j + 1)
  normal i := match i with
    | 0 => hM
    | j + 1 => t.normal (j + 1)
  mono i hi := match i with
    | 0 => hMN.trans (by have := t.mono 0 (by omega); rwa [t.zero] at this)
    | j + 1 => t.mono (j + 1) hi
  zero := rfl
  top := t.top
  psol i hi := match i with
    | 0 => by
      show PSolSec p M (t.G 1)
      have := t.psol 0 (Nat.zero_le _)
      rw [show 2 * 0 = 0 from rfl, t.zero] at this
      exact hs.trans this
    | j + 1 => t.psol (j + 1) hi
  semisimple i hi := t.semisimple i hi

/-- Prepend a semisimple factor `N/M` at the bottom (as `M ≤ M ≤ N`). -/
def NSeriesP.consSS {M N : Subgroup X} [hM : M.Normal] {h : ℕ} (t : NSeriesP p X N h)
    (hMN : M ≤ N) (hs : SemisimplePFactor p M N) : NSeriesP p X M (h + 1) where
  G i := match i with
    | 0 => M
    | 1 => M
    | j + 2 => t.G j
  normal i := match i with
    | 0 => hM
    | 1 => hM
    | j + 2 => t.normal j
  mono i hi := match i with
    | 0 => le_rfl
    | 1 => by show M ≤ t.G 0; rw [t.zero]; exact hMN
    | j + 2 => t.mono j (by omega)
  zero := rfl
  top := t.top
  psol i hi := match i with
    | 0 => ⟨0, le_rfl⟩
    | j + 1 => t.psol j (by omega)
  semisimple i hi := match i with
    | 0 => by show SemisimplePFactor p M (t.G 0); rw [t.zero]; exact hs
    | j + 1 => t.semisimple j (by omega)

open Classical in
lemma nseriesP_of_paperSeries (s : PaperSeries X (PSolOrSemisimpleP p)) :
    ∀ m j, j + m = s.n → Nonempty (NSeriesP p X (s.G j)
      ((Finset.Ico j s.n).filter fun i => ¬ PSolFactor p (s.G i) (s.G (i + 1))).card) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    subst hj
    simp only [add_zero, Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    rw [s.top]
    exact ⟨NSeriesP.topSeries⟩
  | succ m ih =>
    intro j hj
    obtain ⟨t⟩ := ih (j + 1) (by omega)
    have hjn : j < s.n := by omega
    rw [card_filter_Ico_succ _ hjn]
    haveI := s.normal j (by omega)
    by_cases hsol : PSolFactor p (s.G j) (s.G (j + 1))
    · rw [if_neg (not_not.2 hsol), add_zero]
      exact ⟨NSeriesP.consPSol t (s.mono j hjn) (pSolSec_of_pSolFactor hsol)⟩
    · rw [if_pos hsol]
      exact ⟨NSeriesP.consSS t (s.mono j hjn) ((s.factor j hjn).resolve_left hsol)⟩

lemma nonPSolubleLengthLE_of_paperSeries (s : PaperSeries X (PSolOrSemisimpleP p)) :
    NonPSolubleLengthLE p X (s.count (PSolFactor p)) := by
  obtain ⟨t⟩ := nseriesP_of_paperSeries s s.n 0 (by omega)
  rw [count_eq]
  exact ⟨t.cast s.zero⟩

/-- **Crosswalk.** The paper's non-`p`-soluble length (minimum number of non-`p`-soluble factors
over normal series with `p`-soluble or semisimple factors) is the least `h` admitting an
alternating series `1 = G₀ ≤ ⋯ ≤ G_{2h+1} = X`. -/
theorem paperNonPSolubleLength_eq :
    paperNonPSolubleLength p X = sInf {h | NonPSolubleLengthLE p X h} := by
  unfold paperNonPSolubleLength
  apply sInf_eq_of_bounds
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, nonPSolubleLengthLE_of_paperSeries s, le_rfl⟩
  · intro h hh
    obtain ⟨s, hs⟩ := exists_paperSeries_of_nonPSolubleLengthLE hh
    exact ⟨_, ⟨s, rfl⟩, hs⟩

end Crosswalk

section Final

open CFSGOutside.KhukhroShumyatskyNonsolubleLength (PaperSeries PaperSeries.count)

variable {p : ℕ} [hp : Fact p.Prime]

lemma bddAbove_paperPLength (G : Type) [Group G] [Finite G] :
    BddAbove {k | ∃ H : Subgroup G, paperPSoluble p H ∧ paperPLength p H = k} := by
  refine (Set.Finite.bddAbove ((Set.finite_range fun H : Subgroup G => paperPLength p H).subset ?_))
  rintro _ ⟨H, -, rfl⟩
  exact ⟨H, rfl⟩

/-- **Theorem 1.1(b) (Khukhro–Shumyatsky).** For an odd prime `p`, the non-`p`-soluble length
`λ_p(G)` of a finite group `G` does not exceed the maximum `p`-length of `p`-soluble subgroups of
`G`.  All invariants are the paper's literal definitions. -/
theorem theorem_1_1_b [ThompsonElementaryNormalPComplement.{0}] [Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (hp2 : p ≠ 2) (G : Type)
    [Group G] [Finite G] : paperNonPSolubleLength p G ≤ paperMaxPLength p G := by
  apply paperNonPSolubleLength_le
  apply nonPSolubleLengthLE_of_pLenLE hCFSG hp2
  intro H hH
  have hps : paperPSoluble p H := paperPSoluble_of_pSoluble ((pSoluble_top_iff_subgroup H).2 hH)
  have hle : paperPLength p H ≤ paperMaxPLength p G :=
    le_csSup (bddAbove_paperPLength G) ⟨H, hps, rfl⟩
  obtain ⟨s⟩ := hps
  have hne : {k | ∃ s : PaperSeries H (POrPPrime p), s.count (PPrimeFactor p) = k}.Nonempty :=
    ⟨_, s, rfl⟩
  obtain ⟨s', hs'⟩ := Nat.sInf_mem hne
  have h1 := (pLenLE_of_paperSeries s').mono (hs'.le.trans hle)
  have h2 := h1.map H.subtype
  rwa [map_subtype_top] at h2

end Final

end CFSGOutside.KhukhroShumyatskyNonsolubleLength
