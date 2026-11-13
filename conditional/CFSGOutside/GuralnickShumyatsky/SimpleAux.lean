import CFSGOutside.Corpus.CfsgClassification
import CFSGOutside.Corpus.Defs.Conjugate
import CFSGOutside.Corpus.I713PPrimeHolds
import CFSGOutside.Corpus.OddOrder
import CFSGOutside.GuralnickShumyatsky.Gen
import CFSGOutside.GuralnickShumyatsky.PerfectFix

/-!
# Auxiliary results for the characteristically simple case
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup
open scoped Pointwise
open CFSGOutside.Corpus (conjugate)
open CFSGOutside.Corpus.Open (IsCatalogGroup IsElemAbelian pRank)

variable {X : Type} [Group X]

/-- The direct-factor decomposition of a minimal normal subgroup. -/
structure Decomp (G : Subgroup X) where
  r : ℕ
  hr : 1 ≤ r
  S : Fin r → Subgroup X
  le : ∀ i, S i ≤ G
  simple : ∀ i, IsSimpleGroup (S i)
  conj : ∀ i j, ∃ g : X, S j = conjugate (S i) g
  nrm : ∀ i, ((S i).subgroupOf G).Normal
  ne_bot : G ≠ ⊥
  perf : ⁅G, G⁆ = G
  e : ((i : Fin r) → S i) ≃* G
  he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : X) = x i

namespace Decomp

variable {G : Subgroup X} (D : Decomp G)

theorem single (i : Fin D.r) (s : D.S i) : (D.e (Pi.mulSingle i s) : X) = s := by
  rw [D.he i]
  · simp
  · intro j hj; simp [Pi.mulSingle_eq_of_ne hj]

theorem normal' {i : Fin D.r} {g : X} (hg : g ∈ G) {s : X} (hs : s ∈ D.S i) :
    g * s * g⁻¹ ∈ D.S i := by
  have := (D.nrm i).conj_mem ⟨s, D.le i hs⟩ (by simpa [mem_subgroupOf] using hs) ⟨g, hg⟩
  simpa [mem_subgroupOf] using this

theorem comm {i j : Fin D.r} (hij : i ≠ j) {s t : X} (hs : s ∈ D.S i) (ht : t ∈ D.S j) :
    s * t = t * s := by
  have h1 := D.single i ⟨s, hs⟩
  have h2 := D.single j ⟨t, ht⟩
  have : D.e (Pi.mulSingle i ⟨s, hs⟩) * D.e (Pi.mulSingle j ⟨t, ht⟩) =
      D.e (Pi.mulSingle j ⟨t, ht⟩) * D.e (Pi.mulSingle i ⟨s, hs⟩) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Pi.mulSingle_commute hij _ _
  have := congrArg Subtype.val this
  simpa [h1, h2] using this

theorem inf_eq_bot {i j : Fin D.r} (hij : i ≠ j) : D.S i ⊓ D.S j = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hi, hj⟩
  have h1 := D.single i ⟨x, hi⟩
  have h2 := D.single j ⟨x, hj⟩
  have : D.e (Pi.mulSingle i ⟨x, hi⟩) = D.e (Pi.mulSingle j ⟨x, hj⟩) :=
    Subtype.ext (h1.trans h2.symm)
  have := D.e.injective this
  have := congrArg Subtype.val (congrFun this i)
  simp [Pi.mulSingle_eq_of_ne hij] at this
  simpa using this

theorem G_le_iSup : G ≤ ⨆ i, D.S i := by
  classical
  intro g hg
  obtain ⟨y, hy⟩ := D.e.surjective ⟨g, hg⟩
  have hg' : g = ((D.e y : G) : X) := by rw [hy]
  rw [hg']
  have h := Submonoid.iSup_map_mulSingle (M := fun i => D.S i) (P := fun _ => ⊤)
  have hy' : y ∈ Submonoid.pi Set.univ (fun i => (⊤ : Submonoid (D.S i))) := fun i _ => trivial
  rw [← h] at hy'
  have hle : (⨆ i, Submonoid.map (MonoidHom.mulSingle (fun i => D.S i) i) (⊤ : Submonoid (D.S i)))
      ≤ (⨆ i, D.S i).toSubmonoid.comap (G.subtype.comp D.e.toMonoidHom) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨t, -, rfl⟩
    show ((D.e (Pi.mulSingle i t) : G) : X) ∈ ⨆ i, D.S i
    rw [D.single]
    exact mem_iSup_of_mem i t.2
  exact hle hy'

theorem iSup_eq : (⨆ i, D.S i) = G := le_antisymm (iSup_le D.le) D.G_le_iSup

theorem exists_noncomm (i : Fin D.r) :
    ∃ s ∈ D.S i, ∃ t ∈ D.S i, s * t ≠ t * s := by
  by_contra h
  push Not at h
  have hall : ∀ j, ∀ s ∈ D.S j, ∀ t ∈ D.S j, s * t = t * s := by
    intro j s hs t ht
    obtain ⟨g, hg⟩ := D.conj i j
    rw [hg] at hs ht
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hs
    obtain ⟨y, hy, rfl⟩ := mem_map.1 ht
    have := h x hx y hy
    change g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [this]
      _ = _ := by group
  apply D.ne_bot
  have : ⁅G, G⁆ ≤ ⊥ := by
    rw [commutator_le]
    intro g1 hg1 g2 hg2
    obtain ⟨y, hy⟩ := D.e.surjective ⟨g1, hg1⟩
    obtain ⟨z, hz⟩ := D.e.surjective ⟨g2, hg2⟩
    have hyz : y * z = z * y := by
      funext j
      exact Subtype.ext (hall j _ (y j).2 _ (z j).2)
    have : D.e y * D.e z = D.e z * D.e y := by rw [← map_mul, ← map_mul, hyz]
    rw [hy, hz] at this
    have h' : g1 * g2 = g2 * g1 := congrArg Subtype.val this
    rw [mem_bot]
    simp [commutatorElement_def, h']
  rw [← D.perf]
  exact le_bot_iff.1 this

theorem perfect (i : Fin D.r) :
    commutator (D.S i) = ⊤ := by
  haveI := D.simple i
  haveI : (commutator (D.S i)).Normal := inferInstance
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator (D.S i)) with h | h
  · exfalso
    obtain ⟨s, hs, t, ht, hne⟩ := D.exists_noncomm i
    apply hne
    have := commutator_mem_commutator (H₁ := (⊤ : Subgroup (D.S i))) (H₂ := ⊤)
      (g₁ := ⟨s, hs⟩) (g₂ := ⟨t, ht⟩) trivial trivial
    rw [← commutator_def, h, mem_bot] at this
    have := congrArg Subtype.val this
    have h3 : s * t * s⁻¹ = t := by simpa [commutatorElement_def, mul_inv_eq_one] using this
    exact mul_inv_eq_iff_eq_mul.1 h3
  · exact h

theorem nontriv (j : Fin D.r) : ∃ s ∈ D.S j, s ≠ 1 := by
  obtain ⟨s, hs, t, ht, hne⟩ := D.exists_noncomm j
  by_cases h : s = 1
  · subst h; exact absurd (by simp) hne
  · exact ⟨s, hs, h⟩

theorem eq_of_mem_iff {i j : Fin D.r} (h : ∀ x, x ∈ D.S i ↔ x ∈ D.S j) : i = j := by
  by_contra hij
  obtain ⟨s, hs, hs1⟩ := D.nontriv i
  have : s ∈ D.S i ⊓ D.S j := ⟨hs, (h s).1 hs⟩
  rw [D.inf_eq_bot hij, mem_bot] at this
  exact hs1 this

/-- A nontrivial normal subgroup of a simple subgroup is the whole subgroup. -/
theorem simple_eq {V U : Subgroup X} [IsSimpleGroup V] (hU : U ≤ V)
    (hn : ∀ v ∈ V, ∀ u ∈ U, v * u * v⁻¹ ∈ U) (hne : ∃ u ∈ U, u ≠ 1) : U = V := by
  have hN : (U.subgroupOf V).Normal := ⟨fun u hu v => by
    simpa [mem_subgroupOf] using hn v.1 v.2 u.1 hu⟩
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨u, hu, hu1⟩ := hne
    have : (⟨u, hU hu⟩ : V) ∈ U.subgroupOf V := hu
    rw [h, mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  · exact le_antisymm hU (subgroupOf_eq_top.1 h)

/-- `b S i b⁻¹ = S j`. -/
def Conj (b : X) (i j : Fin D.r) : Prop := ∀ x, b * x * b⁻¹ ∈ D.S j ↔ x ∈ D.S i

theorem Conj.unique {b : X} {i j j' : Fin D.r} (h : D.Conj b i j) (h' : D.Conj b i j') : j = j' :=
  D.eq_of_mem_iff fun x => by
    obtain ⟨y, hy⟩ : ∃ y, x = b * y * b⁻¹ := ⟨b⁻¹ * x * b, by group⟩
    subst hy
    rw [h, h']

theorem Conj.unique' {b : X} {i i' j : Fin D.r} (h : D.Conj b i j) (h' : D.Conj b i' j) : i = i' :=
  D.eq_of_mem_iff fun x => by rw [← h, ← h']

theorem cc1 (b x : X) : b⁻¹ * (b * x * b⁻¹) * b = x := by group
theorem cc2 (b x : X) : b * (b⁻¹ * x * b) * b⁻¹ = x := by group

theorem exists_conj {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (i : Fin D.r) :
    ∃ j, D.Conj b i j := by
  have hb' : ∀ x, b⁻¹ * x * b ∈ G ↔ x ∈ G := fun x => by
    rw [← hb (b⁻¹ * x * b), cc2]
  -- T = {x | b⁻¹ x b ∈ S i}
  have hTn : ∀ g ∈ G, ∀ t, b⁻¹ * t * b ∈ D.S i → b⁻¹ * (g * t * g⁻¹) * b ∈ D.S i := by
    intro g hg t ht
    have := D.normal' ((hb' g).2 hg) ht
    convert this using 1
    group
  -- step a
  obtain ⟨j, t, ht, s, hs, hne⟩ : ∃ j, ∃ t, b⁻¹ * t * b ∈ D.S i ∧ ∃ s ∈ D.S j, t * s ≠ s * t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s1, hs1, s2, hs2, hne⟩ := D.exists_noncomm i
    apply hne
    have h1 : b * s1 * b⁻¹ ∈ G := (hb s1).2 (D.le i hs1)
    have h2 : b * s2 * b⁻¹ ∈ G := (hb s2).2 (D.le i hs2)
    have hmem : ∀ t, b⁻¹ * t * b ∈ D.S i → t ∈ centralizer ({b * s1 * b⁻¹} : Set X) → True :=
      fun _ _ _ => trivial
    have hcen : (⨆ j, D.S j) ≤ centralizer ({b * s1 * b⁻¹} : Set X) := by
      refine iSup_le fun j => ?_
      intro s hs
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcon j (b * s1 * b⁻¹) (by rw [cc1]; exact hs1) s hs
    have h2' : b * s2 * b⁻¹ ∈ centralizer ({b * s1 * b⁻¹} : Set X) := by
      apply hcen; rw [D.iSup_eq]; exact h2
    rw [mem_centralizer_iff] at h2'
    have := h2' _ rfl
    have h3 : b * (s1 * s2) * b⁻¹ = b * (s2 * s1) * b⁻¹ := by
      calc b * (s1 * s2) * b⁻¹ = b * s1 * b⁻¹ * (b * s2 * b⁻¹) := by group
        _ = _ := this
        _ = _ := by group
    simpa using h3
  -- step b
  have hc_ne : t * s * t⁻¹ * s⁻¹ ≠ 1 := by
    intro h
    apply hne
    have : t * s * t⁻¹ = s := by rwa [mul_inv_eq_one] at h
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have htG : t ∈ G := by
    have := (hb _).2 (D.le i ht)
    have e : b * (b⁻¹ * t * b) * b⁻¹ = t := by group
    rwa [e] at this
  have hsG : s ∈ G := D.le j hs
  have hcS : t * s * t⁻¹ * s⁻¹ ∈ D.S j := mul_mem (D.normal' htG hs) (inv_mem hs)
  have hcT : b⁻¹ * (t * s * t⁻¹ * s⁻¹) * b ∈ D.S i := by
    have e1 : b⁻¹ * (t * s * t⁻¹ * s⁻¹) * b = (b⁻¹ * t * b) * (b⁻¹ * (s * t⁻¹ * s⁻¹) * b) := by
      group
    rw [e1]
    refine mul_mem ht (hTn s hsG t⁻¹ ?_)
    have : b⁻¹ * t⁻¹ * b = (b⁻¹ * t * b)⁻¹ := by group
    rw [this]; exact inv_mem ht
  let T : Subgroup X := (D.S i).comap (MulAut.conj b⁻¹).toMonoidHom
  have memT : ∀ x, x ∈ T ↔ b⁻¹ * x * b ∈ D.S i := fun x => by
    simp [T, MulAut.conj_apply]
  haveI := D.simple j
  have h1 : D.S j ⊓ T = D.S j := by
    refine simple_eq inf_le_left ?_ ⟨_, ⟨hcS, (memT _).2 hcT⟩, hc_ne⟩
    intro v hv u hu
    refine ⟨mul_mem (mul_mem hv hu.1) ((D.S j).inv_mem hv), (memT _).2 ?_⟩
    exact hTn v (D.le j hv) u ((memT _).1 hu.2)
  have hST : ∀ x ∈ D.S j, b⁻¹ * x * b ∈ D.S i := fun x hx => by
    have : x ∈ D.S j ⊓ T := by rw [h1]; exact hx
    exact (memT x).1 this.2
  haveI := D.simple i
  let U : Subgroup X := (D.S j).comap (MulAut.conj b).toMonoidHom
  have memU : ∀ x, x ∈ U ↔ b * x * b⁻¹ ∈ D.S j := fun x => by
    simp [U, MulAut.conj_apply]
  obtain ⟨s0, hs0, hs01⟩ := D.nontriv j
  have h2 : U = D.S i := by
    refine simple_eq ?_ ?_ ⟨b⁻¹ * s0 * b, (memU _).2 (by rw [cc2]; exact hs0), ?_⟩
    · intro y hy
      have := hST _ ((memU y).1 hy)
      rwa [cc1] at this
    · intro v hv u hu
      rw [memU]
      have := D.normal' ((hb v).2 (D.le i hv)) ((memU u).1 hu)
      convert this using 1
      group
    · intro h
      apply hs01
      have : s0 = b * (b⁻¹ * s0 * b) * b⁻¹ := by group
      rw [h] at this
      simpa using this
  refine ⟨j, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have := (memU x).2 hx
    rwa [h2] at this
  · have := h2 ▸ hx
    exact (memU x).1 this

/-- The induced permutation of the factors. -/
noncomputable def sigma {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) : Equiv.Perm (Fin D.r) :=
  Equiv.ofBijective (fun i => Classical.choose (D.exists_conj hb i)) (by
    rw [← Finite.injective_iff_bijective]
    intro i i' h
    have h1 := Classical.choose_spec (D.exists_conj hb i)
    have h2 := Classical.choose_spec (D.exists_conj hb i')
    simp only at h
    rw [h] at h1
    exact Conj.unique' D h1 h2)

theorem sigma_spec {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (i : Fin D.r) :
    D.Conj b i (D.sigma hb i) := Classical.choose_spec (D.exists_conj hb i)

/-- Conjugation by `b` on `G`. -/
def cG (b : X) (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) : G ≃* G where
  toFun g := ⟨b * g * b⁻¹, (hb g).2 g.2⟩
  invFun g := ⟨b⁻¹ * g * b, by
    have := (hb (b⁻¹ * g * b)).1
    rw [cc2] at this
    exact (hb _).1 (by rw [cc2]; exact g.2)⟩
  left_inv g := Subtype.ext (by simp only; group)
  right_inv g := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- The induced automorphism of `∏ S i`. -/
noncomputable def tau (b : X) (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) :
    (∀ i, D.S i) →* (∀ i, D.S i) :=
  D.e.symm.toMonoidHom.comp ((cG b hb).toMonoidHom.comp D.e.toMonoidHom)

theorem e_tau {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (y : ∀ i, D.S i) :
    ((D.e (D.tau b hb y) : G) : X) = b * (D.e y : X) * b⁻¹ := by
  simp [tau, cG]

theorem e_tau_iter {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (y : ∀ i, D.S i) (n : ℕ) :
    ((D.e ((D.tau b hb)^[n] y) : G) : X) = b ^ n * (D.e y : X) * (b ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', e_tau, ih, pow_succ']
    group

theorem tau_iter_q {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) {q : ℕ} (hq : b ^ q = 1)
    (y : ∀ i, D.S i) : (D.tau b hb)^[q] y = y := by
  apply D.e.injective
  apply Subtype.ext
  rw [D.e_tau_iter, hq]; simp

theorem pi_hom_ext {ι : Type*} [Finite ι] [DecidableEq ι] {M : ι → Type*} [∀ i, Group (M i)]
    {N : Type*} [Group N] (f g : (∀ i, M i) →* N)
    (h : ∀ i (z : M i), f (Pi.mulSingle i z) = g (Pi.mulSingle i z)) : f = g := by
  ext y
  have hy : y ∈ Submonoid.pi Set.univ (fun i => (⊤ : Submonoid (M i))) := fun i _ => trivial
  rw [← Submonoid.iSup_map_mulSingle] at hy
  have : (⨆ i, Submonoid.map (MonoidHom.mulSingle M i) (⊤ : Submonoid (M i))) ≤
      MonoidHom.eqLocusM f g := by
    refine iSup_le fun i => ?_
    rintro _ ⟨z, -, rfl⟩
    exact h i z
  exact this hy

/-- Conjugation by `b` from `S i` to `S (σ i)`. -/
noncomputable def phi {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (i : Fin D.r) :
    D.S i →* D.S (D.sigma hb i) where
  toFun z := ⟨b * z * b⁻¹, (D.sigma_spec hb i z).2 z.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem tau_single {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (k : Fin D.r) (z : D.S k) :
    D.tau b hb (Pi.mulSingle k z) = Pi.mulSingle (D.sigma hb k) (D.phi hb k z) := by
  apply D.e.injective
  apply Subtype.ext
  rw [D.e_tau, D.single, D.single]
  rfl

theorem tau_apply {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) (y : ∀ i, D.S i) (i : Fin D.r) :
    D.tau b hb y (D.sigma hb i) = D.phi hb i (y i) := by
  classical
  have := congrArg (fun f => f y) (pi_hom_ext
    ((Pi.evalMonoidHom (fun j => D.S j) (D.sigma hb i)).comp (D.tau b hb))
    ((D.phi hb i).comp (Pi.evalMonoidHom (fun j => D.S j) i)) (by
      intro k z
      simp only [MonoidHom.coe_comp, Function.comp_apply, Pi.evalMonoidHom_apply]
      rw [D.tau_single]
      by_cases hk : k = i
      · subst hk; simp
      · rw [Pi.mulSingle_eq_of_ne (fun h => hk (D.sigma hb |>.injective h).symm),
          Pi.mulSingle_eq_of_ne (Ne.symm hk)]
        simp))
  simpa using this

theorem cen_le_commutator {b : X} (hb : ∀ x, b * x * b⁻¹ ∈ G ↔ x ∈ G) {q : ℕ} (hq : q.Prime)
    (hbq : b ^ q = 1) (hfree : ∀ i, ¬ D.Conj b i i) :
    cen G b ≤ ⁅cen G b, cen G b⁆ := by
  classical
  set E := MonoidHom.eqLocus (D.tau b hb) (MonoidHom.id _) with hE
  have hcomm := fixed_le_commutator (H := fun i => D.S i) (fun i => D.perfect i)
    (D.sigma hb) (D.phi hb) (D.tau b hb) (fun y i => D.tau_apply hb y i) hq
    (fun i h => hfree i (by simpa [h] using D.sigma_spec hb i))
    (fun y => D.tau_iter_q hb hbq y)
  let f : (∀ i, D.S i) →* X := G.subtype.comp D.e.toMonoidHom
  have hmapE : E.map f ≤ cen G b := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : D.tau b hb y = y := hy
    have := D.e_tau hb y
    rw [hy'] at this
    refine ⟨(D.e y).2, ?_⟩
    show f y ∈ centralizer ({b} : Set X)
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show h * (D.e y : X) = (D.e y : X) * h
    exact mul_inv_eq_iff_eq_mul.1 this.symm
  have hle : cen G b ≤ E.map f := by
    rintro x ⟨hxG, hxc⟩
    have hxc : x ∈ centralizer ({b} : Set X) := hxc
    rw [mem_centralizer_iff] at hxc
    have hc := hxc b rfl
    refine ⟨D.e.symm ⟨x, hxG⟩, ?_, by
      show ((D.e (D.e.symm ⟨x, hxG⟩) : G) : X) = x
      rw [MulEquiv.apply_symm_apply]⟩
    show D.tau b hb _ = _
    apply D.e.injective
    apply Subtype.ext
    rw [D.e_tau]
    simp only [MulEquiv.apply_symm_apply]
    rw [hc]
    simp
  calc cen G b ≤ E.map f := hle
    _ ≤ (⁅E, E⁆).map f := map_mono hcomm
    _ = ⁅E.map f, E.map f⁆ := map_commutator E E f
    _ ≤ _ := commutator_mono hmapE hmapE

end Decomp

theorem perfect_ne_bot_not_odd [CFSGOutside.Corpus.OddOrder.{0}]
    [Finite X] {G : Subgroup X} (hG1 : G ≠ ⊥) (hperf : ⁅G, G⁆ = G)
    (hodd : Odd (Nat.card G)) : False := by
  haveI : Nontrivial G := (Subgroup.nontrivial_iff_ne_bot G).2 hG1
  haveI : Group.IsSolvable G :=
    CFSGOutside.Corpus.OddOrder.isSolvable_of_odd_natCard G hodd
  have h1 : (commutator G).map G.subtype = (⊤ : Subgroup G).map G.subtype := by
    rw [commutator_def, map_commutator, Subgroup.map_top, range_subtype, hperf]
  have h2 : commutator G = ⊤ := Subgroup.map_injective G.subtype_injective h1
  have := IsSolvable.commutator_lt_top_of_nontrivial G
  rw [h2] at this
  exact lt_irrefl _ this

theorem q_ne_two [CFSGOutside.Corpus.OddOrder.{0}]
    [Finite X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A) (hG1 : G ≠ ⊥)
    (hperf : ⁅G, G⁆ = G) : q ≠ 2 := by
  rintro rfl
  apply perfect_ne_bot_not_odd hG1 hperf
  have := hA.coprime
  rw [Nat.odd_iff]
  omega

theorem G_normal {G A : Subgroup X} {q : ℕ} (hA : CopAct q G A) (hGA : G ⊔ A = ⊤) : G.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hGA]
  exact sup_le le_normalizer hA.norm

theorem CopAct.conj_mem_iff {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A) {b : X} (hb : b ∈ A)
    (x : X) : b * x * b⁻¹ ∈ G ↔ x ∈ G := by
  have := mem_normalizer_iff.1 (hA.norm hb) x
  exact this.symm

theorem Decomp.normal_iff {G : Subgroup X} (D : Decomp G) {i : Fin D.r} {g : X} (hg : g ∈ G)
    {s : X} : g * s * g⁻¹ ∈ D.S i ↔ s ∈ D.S i := by
  refine ⟨fun h => ?_, D.normal' hg⟩
  have := D.normal' (G.inv_mem hg) h
  have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
  rwa [e] at this

theorem Decomp.exists_A_conj {q : ℕ} {G A : Subgroup X} (D : Decomp G) (hA : CopAct q G A)
    (hGA : G ⊔ A = ⊤) (i j : Fin D.r) : ∃ a ∈ A, D.Conj a i j := by
  haveI := G_normal hA hGA
  obtain ⟨g, hg⟩ := D.conj j i
  have hgx : ∀ x, x ∈ D.S i ↔ g * x * g⁻¹ ∈ D.S j := by
    intro x
    rw [hg]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      have e : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
        simp [MulAut.conj_apply]; group
      rw [e]; exact hy
    · intro hx
      refine mem_map.2 ⟨g * x * g⁻¹, hx, ?_⟩
      simp [MulAut.conj_apply]; group
  have hg' : g ∈ (G : Set X) * (A : Set X) := by
    rw [← Subgroup.normal_mul, hGA]; trivial
  obtain ⟨h, hh, a, ha, rfl⟩ := hg'
  refine ⟨a, ha, fun x => ?_⟩
  rw [hgx x]
  have e : h * a * x * (h * a)⁻¹ = h * (a * x * a⁻¹) * h⁻¹ := by group
  rw [e, D.normal_iff hh]

theorem Decomp.conj_self {q : ℕ} {G A : Subgroup X} (D : Decomp G) (hA : CopAct q G A)
    (hGA : G ⊔ A = ⊤) {b : X} (hb : b ∈ A) {i : Fin D.r} (hi : D.Conj b i i) (j : Fin D.r) :
    D.Conj b j j := by
  obtain ⟨a, ha, hac⟩ := D.exists_A_conj hA hGA i j
  intro x
  have hba : b * a = a * b := hA.comm b hb a ha
  obtain ⟨y, rfl⟩ : ∃ y, x = a * y * a⁻¹ := ⟨a⁻¹ * x * a, by group⟩
  have e : b * (a * y * a⁻¹) * b⁻¹ = a * (b * y * b⁻¹) * a⁻¹ :=
    calc b * (a * y * a⁻¹) * b⁻¹ = (b * a) * y * (b * a)⁻¹ := by group
      _ = (a * b) * y * (a * b)⁻¹ := by rw [hba]
      _ = _ := by group
  rw [e, hac, hac, hi]

theorem Decomp.centralize_all {q : ℕ} {G A : Subgroup X} (D : Decomp G) (hA : CopAct q G A)
    (hGA : G ⊔ A = ⊤) {a₀ : X} (ha₀ : a₀ ∈ A) {i₀ : Fin D.r}
    (h : ∀ t ∈ D.S i₀, a₀ * t = t * a₀) : ∀ i, ∀ s ∈ D.S i, a₀ * s = s * a₀ := by
  intro i s hs
  obtain ⟨a, ha, hac⟩ := D.exists_A_conj hA hGA i₀ i
  have ht : a⁻¹ * s * a ∈ D.S i₀ := by
    rw [← hac]
    have e : a * (a⁻¹ * s * a) * a⁻¹ = s := by group
    rwa [e]
  have h1 : a₀ * a = a * a₀ := hA.comm _ ha₀ _ ha
  have h2 : a₀ * a⁻¹ = a⁻¹ * a₀ := hA.comm _ ha₀ _ (A.inv_mem ha)
  have h3 := h _ ht
  calc a₀ * s = (a₀ * a) * (a⁻¹ * s * a) * a⁻¹ := by group
    _ = (a * a₀) * (a⁻¹ * s * a) * a⁻¹ := by rw [h1]
    _ = a * (a₀ * (a⁻¹ * s * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * s * a) * a₀) * a⁻¹ := by rw [h3]
    _ = a * (a⁻¹ * s * a) * (a₀ * a⁻¹) := by group
    _ = a * (a⁻¹ * s * a) * (a⁻¹ * a₀) := by rw [h2]
    _ = s * a₀ := by group

theorem Decomp.card_stab_lt [CFSGOutside.Corpus.CfsgClassification]
    [CFSGOutside.Corpus.I713PPrimeHolds]
    [Finite X] {q : ℕ} {G A : Subgroup X} (D : Decomp G)
    (hA : CopAct q G A) (hq2 : q ≠ 2) (i₀ : Fin D.r)
    (hfaith : ∀ a₀ ∈ A, a₀ ≠ 1 → ∃ t ∈ D.S i₀, a₀ * t ≠ t * a₀) :
    Nat.card (A ⊓ normalizer (D.S i₀ : Set X) : Subgroup X) < q ^ 2 := by
  by_contra hge
  push Not at hge
  have hq : q.Prime := hA.prime
  haveI : Fact q.Prime := ⟨hq⟩
  set N : Subgroup X := A ⊓ normalizer (D.S i₀ : Set X) with hN
  have hNn : N ≤ normalizer (D.S i₀ : Set X) := inf_le_right
  letI : MulDistribMulAction ↥N ↥(D.S i₀) := conjAction hNn
  let ρ : ↥N →* MulAut ↥(D.S i₀) := MulDistribMulAction.toMulAut ↥N ↥(D.S i₀)
  have hρ : ∀ (n : N) (s : D.S i₀), ((ρ n s : D.S i₀) : X) = n * s * (n : X)⁻¹ := fun n s => rfl
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    by_contra hn1
    have hn1' : (n : X) ≠ 1 := fun h => hn1 (Subtype.ext h)
    obtain ⟨t, ht, hne⟩ := hfaith n n.2.1 hn1'
    apply hne
    have := congrArg (fun f => ((f ⟨t, ht⟩ : D.S i₀) : X)) hn
    simp only [hρ] at this
    simp only [MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hpg : IsPGroup q N := fun g => ⟨1, Subtype.ext (by
    simpa using hA.exp g.1 g.2.1)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hk2 : 2 ≤ k := by
    rw [hk] at hge
    exact (Nat.pow_le_pow_iff_right hq.one_lt).1 hge
  have hcardE : Nat.card ρ.range = q ^ k := by
    rw [← hk]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcomm : ∀ n m : N, n * m = m * n := fun n m =>
    Subtype.ext (hA.comm _ n.2.1 _ m.2.1)
  have hE : IsElemAbelian q ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨n, hn⟩ := a.2
      obtain ⟨m, hm⟩ := b.2
      apply Subtype.ext
      show (a : MulAut ↥(D.S i₀)) * b = b * a
      rw [← hn, ← hm, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨n, rfl⟩ := hx
      rw [← map_pow]
      have : n ^ q = 1 := Subtype.ext (by simpa using hA.exp n.1 n.2.1)
      rw [this, map_one]
  haveI := D.simple i₀
  obtain ⟨s, hs, t, ht, hne⟩ := D.exists_noncomm i₀
  have hcat : IsCatalogGroup ↥(D.S i₀) :=
    CFSGOutside.Corpus.CfsgClassification.cfsg_classification _
  have hnd : ¬ q ∣ Nat.card ↥(D.S i₀) := fun h =>
    hA.coprime (h.trans (Subgroup.card_dvd_of_le (D.le i₀)))
  have h17 := CFSGOutside.Corpus.I713PPrimeHolds.i_7_13_1_pPrime_holds q hq hq2 ↥(D.S i₀) inferInstance
    ⟨⟨s, hs⟩, ⟨t, ht⟩, fun h => hne (congrArg Subtype.val h)⟩ hcat hnd
  have hbdd : BddAbove {k | ∃ E : Subgroup (MulAut ↥(D.S i₀)), E ≤ ⊤ ∧ IsElemAbelian q E ∧
      Nat.card E = q ^ k} := by
    refine ⟨Nat.card (MulAut ↥(D.S i₀)), ?_⟩
    rintro k ⟨E', -, -, hc⟩
    have h1 : k < q ^ k := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E' ≤ Nat.card (MulAut ↥(D.S i₀)) := Subgroup.card_le_card_group E'
    omega
  have : k ≤ pRank q (⊤ : Subgroup (MulAut ↥(D.S i₀))) :=
    le_csSup hbdd ⟨ρ.range, le_top, hE, hcardE⟩
  omega

theorem le_gens {P G A : Subgroup X} {b : X} (hb : b ∈ A) (hb1 : b ≠ 1) :
    P ⊓ ⁅cen G b, cen G b⁆ ≤ gens P G A :=
  le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)

theorem main_core [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [Finite X] {q p : ℕ} [Fact p.Prime] {G A P : Subgroup X} (D : Decomp G)
    (hA : CopAct q G A) (hA3 : q ^ 3 ≤ Nat.card A) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set X)) (hq2 : q ≠ 2) (hGA : G ⊔ A = ⊤) :
    P ≤ gens P G A := by
  have hq := hA.prime
  haveI : Fact q.Prime := ⟨hq⟩
  let i₀ : Fin D.r := ⟨0, D.hr⟩
  have hPG := hP.le
  by_cases h1 : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ ∀ t ∈ D.S i₀, a₀ * t = t * a₀
  · obtain ⟨a₀, ha₀, ha₁, hc⟩ := h1
    have hall := D.centralize_all hA hGA ha₀ hc
    have hGc : G ≤ centralizer ({a₀} : Set X) := by
      rw [← D.iSup_eq]
      refine iSup_le fun i s hs => ?_
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hall i s hs
    have hcen : cen G a₀ = G := le_antisymm inf_le_left (le_inf le_rfl hGc)
    intro x hx
    refine le_gens ha₀ ha₁ ⟨hx, ?_⟩
    rw [hcen, D.perf]
    exact hPG hx
  · push Not at h1
    have hN := D.card_stab_lt hA hq2 i₀ h1
    have hq2' : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq.pos (by norm_num)
    have hPA : CopAct q P A :=
      { prime := hq
        norm := hAP
        coprime := fun h => hA.coprime (h.trans (Subgroup.card_dvd_of_le hPG))
        comm := hA.comm
        exp := hA.exp }
    refine (iSup_cenS_eq hPA (hq2'.trans hA3)).symm.le.trans ?_
    refine iSup₂_le fun Y hY => ?_
    obtain ⟨b, hbY, hbn⟩ : ∃ b ∈ Y, ¬ D.Conj b i₀ i₀ := by
      by_contra hcon
      push Not at hcon
      have hYN : Y ≤ A ⊓ normalizer (D.S i₀ : Set X) := fun b hb =>
        ⟨hY.1 hb, mem_normalizer_iff.2 fun x => (hcon b hb x).symm⟩
      have h2 : Nat.card Y ≤ Nat.card (A ⊓ normalizer (D.S i₀ : Set X) : Subgroup X) :=
        Subgroup.card_le_of_le hYN
      have h3 := hY.card_le hA
      have h4 : q * q ^ 2 ≤ q * Nat.card Y := by
        calc q * q ^ 2 = q ^ 3 := by ring
          _ ≤ _ := hA3
          _ ≤ _ := h3
      have := Nat.le_of_mul_le_mul_left h4 hq.pos
      omega
    have hbA : b ∈ A := hY.1 hbY
    have hb1 : b ≠ 1 := fun h => hbn (by subst h; intro x; simp)
    have hfree : ∀ i, ¬ D.Conj b i i := fun i hi => hbn (D.conj_self hA hGA hbA hi i₀)
    have hcl := D.cen_le_commutator (hA.conj_mem_iff hbA) hq (hA.exp b hbA) hfree
    rintro x ⟨hxP, hxc⟩
    have hxc' : x ∈ centralizer (Y : Set X) := hxc
    rw [mem_centralizer_iff] at hxc'
    have hxcen : x ∈ cen G b :=
      ⟨hPG hxP, mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; subst hh; exact hxc' _ hbY⟩
    exact le_gens hbA hb1 ⟨hxP, hcl hxcen⟩

end CFSGOutside.GuralnickShumyatsky
