import CFSGOutside.HallPaige.Sporadic.B.Witness
import CFSGOutside.HallPaige.OrbitalMatching
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Transport

/-!
# The Baby Monster `B`

`B` acts by conjugation on its class `2A` of involutions (`BabyInv 0` in the corpus model
`NativeSporadic.B ≤ GL₄₃₇₀(𝔽₂)`), with point stabilizer `H = C(τ₁)`. By the corpus theorems
`babyTableIII` and `babyTableIV`, the `H`-orbits on `2A` are `{τ₁}` and the four orbitals `D₀ … D₃`
(`τ₁ s ∈ 2B`, `τ₁ s ∈ 2C`, `τ₁ s` of order 3, `τ₁ s` of order 4 with square in `2B`), of sizes
`3968055, 23113728, 2370830336, 11174042880`, each `H`-transitive.

The Wilcox criterion with `ψ = id` fails for `B` (`D₁` has no triangle). We use the flow form
`hasCompleteMapping_of_flow` (`HallPaige/OrbitalMatching.lean`) with the flow (rows and columns indexed
by `D₀, D₁, D₂, D₃, {τ₁}`)

```
  n₀  0   0    0          0
  0   0   0    n₁         0
  0   0   n₂   0          0
  0   n₁  0    n₃ - n₁    0
  0   0   0    0          1
```

(a 2-cycle between `D₁` and `D₃`, see a generator script). Each positive
entry `(j, l)` has a witness triangle `(t₀, p, q)` of `2A` elements with orbitals `j, l, j`:

* `(0, 0)`: `(s₄, e s₄ e⁻¹, e² s₄ e⁻²)`;
* `(1, 3)`: `(τ₁, α, s₄)`;
* `(2, 2)`: `(τ₁, s, τ₁ s τ₁)` for any `s ∈ D₂` (nonempty by `babyTableIV`);
* `(3, 1)`: `(α, p, τ₁)` with `p = a₁ τ₁ a₁⁻¹`;
* `(3, 3)`: `(τ₁, p, s₄)`.

`H` is good (it contains the Klein group `⟨τ₁, α⟩`) and proper, so it has a complete mapping inside the
minimal counterexample. The corpus `nonempty_mulEquiv` transports the result to `TauCeti`'s `B`.
-/

namespace CFSGOutside.HallPaige.B

open MulAction CFSGOutside.Corpus.B CFSGOutside.Corpus.B.Blueprint CFSGOutside.Corpus.B.Monster.GMS

local notation "𝔹" => NativeSporadic.B

-- Elaboration unfolds the large literal matrices in a few unification problems.
set_option maxRecDepth 100000

/-- The class `2A` of the corpus model. -/
abbrev TwoA : Type := {s : 𝔹 // BabyInv 0 s}

/-- `B` acts on `2A` by conjugation. -/
instance : MulAction 𝔹 TwoA where
  smul g s := ⟨g * s.1 * g⁻¹, (babyInv_conj_iff g s.1).2 s.2⟩
  one_smul s := Subtype.ext (show 1 * s.1 * 1⁻¹ = s.1 by simp)
  mul_smul g h s := Subtype.ext (show g * h * s.1 * (g * h)⁻¹ = g * (h * s.1 * h⁻¹) * g⁻¹ by group)

theorem smul_val (g : 𝔹) (s : TwoA) : (g • s).1 = g * s.1 * g⁻¹ := rfl

section Action

variable [Theorems]

/-- The base point `τ₁`. -/
noncomputable def x₀ : TwoA := ⟨tau, tau_babyInv⟩

/-- The suborbit of a point: `k` (as `Fin.castSucc k`) for the orbital `Dₖ`, `4` for `τ₁` itself. -/
noncomputable def lab (y : TwoA) : Fin 5 := by
  classical
  exact if h : ∃ k : Fin 4, BabyOrbit k tau y.1 then (Classical.choose h).castSucc else Fin.last 4

theorem lab_castSucc_iff (y : TwoA) (k : Fin 4) : lab y = k.castSucc ↔ BabyOrbit k tau y.1 := by
  unfold lab
  split_ifs with h
  · constructor
    · intro e
      rw [← Fin.castSucc_injective _ e]
      exact Classical.choose_spec h
    · intro hk
      rw [babyOrbit_unique (Classical.choose_spec h) hk]
  · constructor
    · intro e
      exact absurd e.symm (Fin.castSucc_lt_last k).ne
    · intro hk
      exact absurd ⟨k, hk⟩ h

theorem lab_last_iff (y : TwoA) : lab y = Fin.last 4 ↔ y.1 = tau := by
  unfold lab
  split_ifs with h
  · constructor
    · intro e
      exact absurd e (Fin.castSucc_lt_last _).ne
    · intro e
      obtain ⟨k, hk⟩ := h
      rw [e] at hk
      exact absurd hk (not_babyOrbit_self tau_mul_self)
  · simp only [true_iff]
    by_contra hne
    exact h ((Theorems.babyTableIV tau tau_babyInv).1 y.1 y.2 hne)

theorem stabilizer_eq : stabilizer 𝔹 x₀ = Subgroup.centralizer ({tau} : Set 𝔹) := by
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, smul_val]
  change g * tau * g⁻¹ = tau ↔ _
  rw [mul_inv_eq_iff_eq_mul]

theorem lab_smul {h : 𝔹} (hh : h ∈ Subgroup.centralizer ({tau} : Set 𝔹)) (y : TwoA) :
    lab (h • y) = lab y := by
  have hc : h * tau * h⁻¹ = tau := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    rw [mul_inv_eq_iff_eq_mul]
    first | exact hh | exact hh.symm
  have key : ∀ j, lab (h • y) = j ↔ lab y = j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [lab_last_iff, lab_last_iff, smul_val]
      constructor
      · intro e
        exact mul_left_cancel (mul_right_cancel (e.trans hc.symm))
      · intro e
        rw [e, hc]
    | cast k =>
      rw [lab_castSucc_iff, lab_castSucc_iff, smul_val]
      have := babyOrbit_conj_iff (k := k) h tau y.1
      rwa [hc] at this
  exact (key (lab y)).2 rfl

theorem lab_eq_iff (y y' : TwoA) : lab y = lab y' ↔ ∃ h ∈ stabilizer 𝔹 x₀, h • y = y' := by
  constructor
  · intro e
    rcases Fin.eq_castSucc_or_eq_last (lab y) with ⟨k, hk⟩ | hl
    · have h1 := (lab_castSucc_iff y k).1 hk
      have h2 := (lab_castSucc_iff y' k).1 (e ▸ hk)
      obtain ⟨g, hg, hgy⟩ :=
        (Theorems.babyTableIV tau tau_babyInv).2.1 k y.1 y'.1 y.2 y'.2 h1 h2
      exact ⟨g, stabilizer_eq ▸ hg, Subtype.ext hgy⟩
    · have h1 := (lab_last_iff y).1 hl
      have h2 := (lab_last_iff y').1 (e ▸ hl)
      exact ⟨1, Subgroup.one_mem _, by rw [one_smul]; exact Subtype.ext (h1.trans h2.symm)⟩
  · rintro ⟨h, hh, rfl⟩
    exact (lab_smul (stabilizer_eq ▸ hh) y).symm

/-- The suborbit sizes. -/
def sz : Fin 5 → ℕ := ![3968055, 23113728, 2370830336, 11174042880, 1]

theorem card_lab (j : Fin 5) : Nat.card {y : TwoA // lab y = j} = sz j := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
  · rw [Nat.card_congr (Equiv.subtypeEquivRight fun y => lab_castSucc_iff y k),
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun s => BabyInv 0 s)
        (fun s => BabyOrbit k tau s))]
    have h := (Theorems.babyTableIV tau tau_babyInv).2.2 k
    rw [← Nat.card_coe_set_eq] at h
    have h' : Nat.card {s // BabyInv 0 s ∧ BabyOrbit k tau s} = babyOrbitSize k := h
    rw [h']
    fin_cases k <;> rfl
  · refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨x₀, ?_⟩⟩⟩
    · exact Subtype.ext (((lab_last_iff _).1 a.2).trans ((lab_last_iff _).1 b.2).symm)
    · exact (lab_last_iff x₀).2 rfl

/-- The flow: the diagonal of suborbit sizes, with a 2-cycle between `D₁` and `D₃`. -/
def flow : Fin 5 → Fin 5 → ℕ :=
  ![![3968055, 0, 0, 0, 0], ![0, 0, 0, 23113728, 0], ![0, 0, 2370830336, 0, 0],
    ![0, 23113728, 0, 11150929152, 0], ![0, 0, 0, 0, 1]]

theorem flow_row (j : Fin 5) : ∑ l, flow j l = Nat.card {y : TwoA // lab y = j} := by
  rw [card_lab, Fin.sum_univ_five]
  fin_cases j <;> rfl

theorem flow_col (l : Fin 5) : ∑ j, flow j l = Nat.card {y : TwoA // lab y = l} := by
  rw [card_lab, Fin.sum_univ_five]
  fin_cases l <;> rfl

/-- A witness triangle `(t₀, p, q)` with orbitals `j, l, j` gives the witness of the flow entry
`(j, l)`. -/
theorem witness {t₀ p q : 𝔹} (h₀ : BabyInv 0 t₀) (hp : BabyInv 0 p) (hq : BabyInv 0 q)
    {j l : Fin 4} (hjp : BabyOrbit j t₀ p) (hlq : BabyOrbit l t₀ q) (hpq : BabyOrbit j p q) :
    ∃ g g' : 𝔹, lab (g • x₀) = j.castSucc ∧ lab (g' • x₀) = l.castSucc ∧
      lab ((g⁻¹ * g') • x₀) = j.castSucc := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Theorems.babyTableIII.2 0 t₀ tau h₀ tau_babyInv)
  obtain ⟨g, hg⟩ := isConj_iff.1
    (Theorems.babyTableIII.2 0 tau (c * p * c⁻¹) tau_babyInv ((babyInv_conj_iff c p).2 hp))
  obtain ⟨g', hg'⟩ := isConj_iff.1
    (Theorems.babyTableIII.2 0 tau (c * q * c⁻¹) tau_babyInv ((babyInv_conj_iff c q).2 hq))
  refine ⟨g, g', ?_, ?_, ?_⟩
  · rw [lab_castSucc_iff, smul_val]
    show BabyOrbit j tau (g * tau * g⁻¹)
    rw [hg, ← hc, babyOrbit_conj_iff]
    exact hjp
  · rw [lab_castSucc_iff, smul_val]
    show BabyOrbit l tau (g' * tau * g'⁻¹)
    rw [hg', ← hc, babyOrbit_conj_iff]
    exact hlq
  · rw [lab_castSucc_iff, smul_val]
    show BabyOrbit j tau (g⁻¹ * g' * tau * (g⁻¹ * g')⁻¹)
    have h1 := (babyOrbit_conj_iff g⁻¹ (c * p * c⁻¹) (c * q * c⁻¹)).2
      ((babyOrbit_conj_iff c p q).2 hpq)
    have e1 : g⁻¹ * (c * p * c⁻¹) * g⁻¹⁻¹ = tau := by rw [← hg]; group
    have e2 : g⁻¹ * (c * q * c⁻¹) * g⁻¹⁻¹ = g⁻¹ * g' * tau * (g⁻¹ * g')⁻¹ := by rw [← hg']; group
    rwa [e1, e2] at h1

theorem ee_cube : ee ^ 3 = 1 := by
  refine eq_one_of_mat ?_
  rw [mat, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
  exact e3_cube

theorem exists_orbit_two : ∃ s, BabyInv 0 s ∧ BabyOrbit 2 tau s := by
  have h := (Theorems.babyTableIV tau tau_babyInv).2.2 2
  have hne : {s | BabyInv 0 s ∧ BabyOrbit 2 tau s}.ncard ≠ 0 := by
    rw [h]
    simp [babyOrbitSize]
  exact Set.nonempty_of_ncard_ne_zero hne

theorem flow_witness (j l : Fin 5) (hF : 0 < flow j l) :
    ∃ g g' : 𝔹, lab (g • x₀) = j ∧ lab (g' • x₀) = l ∧ lab ((g⁻¹ * g') • x₀) = j := by
  have hjl : (j, l) ∈ [(0, 0), (1, 3), (2, 2), (3, 1), (3, 3), (4, 4)] := by
    revert hF
    revert j l
    decide
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hjl
  have hτ := tau_babyInv
  have hs := sFour_babyInv
  have hp := pp_babyInv
  have tauinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_self
  rcases hjl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `(s₄, e s₄ e⁻¹, e² s₄ e⁻²)`
    have h01 := sFour_conj_orbit
    have h02 : BabyOrbit 0 sFour (ee ^ 2 * sFour * (ee ^ 2)⁻¹) := by
      have := (babyOrbit_conj_iff (ee ^ 2) (ee * sFour * ee⁻¹) sFour).2
        ((babyOrbit_comm _ _).2 h01)
      have e : ee ^ 2 * (ee * sFour * ee⁻¹) * (ee ^ 2)⁻¹ = ee ^ 3 * sFour * (ee ^ 3)⁻¹ := by group
      rwa [e, ee_cube, one_mul, inv_one, mul_one] at this
    have h12 : BabyOrbit 0 (ee * sFour * ee⁻¹) (ee ^ 2 * sFour * (ee ^ 2)⁻¹) := by
      have := (babyOrbit_conj_iff ee sFour (ee * sFour * ee⁻¹)).2 h01
      have e : ee * (ee * sFour * ee⁻¹) * ee⁻¹ = ee ^ 2 * sFour * (ee ^ 2)⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      rwa [e] at this
    exact witness (j := 0) (l := 0) hs ((babyInv_conj_iff _ _).2 hs) ((babyInv_conj_iff _ _).2 hs)
      h01 h02 h12
  · -- `(τ₁, α, s₄)`
    exact witness (j := 1) (l := 3) hτ alpha_babyInv hs tau_alpha_orbit tau_sFour_orbit
      alpha_sFour_orbit
  · -- `(τ₁, s, τ₁ s τ₁)`
    obtain ⟨s, hs2, h2⟩ := exists_orbit_two
    have h3 : orderOf (s * tau) = 3 := (babyOrbit_comm tau s).2 h2
    have hq : BabyOrbit 2 tau (tau * s * tau⁻¹) := by
      have := (babyOrbit_conj_iff tau tau s).2 h2
      rwa [show tau * tau * tau⁻¹ = tau by group] at this
    have hpq : BabyOrbit 2 s (tau * s * tau⁻¹) := by
      show orderOf (s * (tau * s * tau⁻¹)) = 3
      have e : s * (tau * s * tau⁻¹) = (s * tau)⁻¹ := by
        rw [tauinv, eq_inv_iff_mul_eq_one]
        have := pow_orderOf_eq_one (s * tau)
        rw [h3] at this
        rw [← this, pow_succ, pow_succ, pow_one]
        simp only [mul_assoc]
      rw [e, orderOf_inv, h3]
    exact witness (j := 2) (l := 2) hτ hs2 ((babyInv_conj_iff _ _).2 hs2) h2 hq hpq
  · -- `(α, p, τ₁)`
    exact witness (j := 3) (l := 1) alpha_babyInv hp hτ alpha_pp_orbit
      ((babyOrbit_comm _ _).2 tau_alpha_orbit) ((babyOrbit_comm _ _).2 tau_pp_orbit)
  · -- `(τ₁, p, s₄)`
    exact witness (j := 3) (l := 3) hτ hp hs tau_pp_orbit tau_sFour_orbit pp_sFour_orbit
  · -- the trivial suborbit
    refine ⟨1, 1, ?_, ?_, ?_⟩ <;> exact (lab_last_iff _).2 (by simp [smul_val, x₀])

theorem tau_mem : tau ∈ stabilizer 𝔹 x₀ := by
  rw [stabilizer_eq, Subgroup.mem_centralizer_singleton_iff]

theorem alpha_mem : alpha ∈ stabilizer 𝔹 x₀ := by
  rw [stabilizer_eq, Subgroup.mem_centralizer_singleton_iff]
  exact tau_comm_alpha.symm

theorem isGood_stabilizer : IsGood (stabilizer 𝔹 x₀) := by
  have hτ2 : tau ^ 2 = 1 := by
    have := pow_orderOf_eq_one tau
    rwa [tau_babyInv.1] at this
  have hα2 : alpha ^ 2 = 1 := by
    have := pow_orderOf_eq_one alpha
    rwa [alpha_babyInv.1] at this
  have ne1 : ∀ x : 𝔹, orderOf x = 2 → x ≠ 1 := fun x h h1 => by
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)
  exact Subgroup.isGood_of_commuting_involutions _ tau_mem alpha_mem hτ2 hα2 tau_comm_alpha
    (ne1 _ tau_babyInv.1) (ne1 _ alpha_babyInv.1) tau_ne_alpha

theorem stabilizer_ne_top : stabilizer 𝔹 x₀ ≠ ⊤ := by
  intro htop
  obtain ⟨c, hc⟩ := isConj_iff.1 (Theorems.babyTableIII.2 0 tau alpha tau_babyInv alpha_babyInv)
  have hcm : c ∈ stabilizer 𝔹 x₀ := htop ▸ Subgroup.mem_top c
  rw [mem_stabilizer_iff, Subtype.ext_iff, smul_val] at hcm
  exact tau_ne_alpha (hcm.symm.trans hc)

theorem exists_smul_eq (y : TwoA) : ∃ g : 𝔹, g • x₀ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Theorems.babyTableIII.2 0 tau y.1 tau_babyInv y.2)
  exact ⟨c, Subtype.ext hc⟩

/-- **The corpus model of `B` has a complete mapping** if its proper good subgroups do. -/
theorem hasCompleteMapping_model (hP : ProperSubgroupsAdmissible 𝔹) : HasCompleteMapping 𝔹 := by
  have hH : HasCompleteMapping (stabilizer 𝔹 x₀) := hP _ stabilizer_ne_top isGood_stabilizer
  exact @hasCompleteMapping_of_flow 𝔹 TwoA (Fin 5) _ _ finite_model _ _ x₀ exists_smul_eq hH lab
    lab_eq_iff flow flow_row flow_col flow_witness

/-- `HasCompleteMapping.of_mulEquiv` with `Mul` instances only, so that the instances of the corpus
isomorphism are used as they are (unifying them with group-derived ones unfolds the model). -/
theorem hasCompleteMapping_of_mulEquiv' {G H : Type*} [Mul G] [Mul H] (e : G ≃* H)
    (h : HasCompleteMapping G) : HasCompleteMapping H := by
  obtain ⟨θ, hθ, hm⟩ := h
  refine ⟨fun y => e (θ (e.symm y)), e.bijective.comp (hθ.comp e.symm.bijective), ?_⟩
  have : (fun y => y * e (θ (e.symm y))) = e ∘ (fun x => x * θ x) ∘ e.symm := by
    funext y
    simp
  rw [this]
  exact e.bijective.comp (hm.comp e.symm.bijective)

/-- `B` has a complete mapping if its proper good subgroups do. -/
theorem hasCompleteMapping_B (hP : ProperSubgroupsAdmissible TauCeti.SporadicName.B.Group) :
    HasCompleteMapping TauCeti.SporadicName.B.Group := by
  obtain ⟨e⟩ := Theorems.nonempty_mulEquiv
  have h1 : ProperSubgroupsAdmissible 𝔹 := ProperSubgroupsAdmissible.of_mulEquiv e.symm hP
  exact hasCompleteMapping_of_mulEquiv' e (hasCompleteMapping_model h1)

end Action

end CFSGOutside.HallPaige.B

namespace CFSGOutside.HallPaige

open CFSGOutside.Corpus.B

/-- **The catalogue case of the Baby Monster `B`.** -/
theorem catalogueCase_B [Theorems] : CatalogueCase (.sporadic .B) :=
  fun _ hP => B.hasCompleteMapping_B hP

end CFSGOutside.HallPaige
