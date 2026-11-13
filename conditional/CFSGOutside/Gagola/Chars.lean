import Mathlib
import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# A small calculus of complex characters of finite groups

Class functions `G → ℂ`, the pairing `ip f g = |G|⁻¹ ∑ f(x) g(x⁻¹)`, the irreducible characters
`Irr G` (TauCeti's `irreducibleCharacters ℂ G`), their orthonormality and completeness, characters with
natural multiplicities (`IsNatComb`), pulling back along homomorphisms, and induction from a subgroup with
Frobenius reciprocity.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

/-- The irreducible complex characters of `G`. -/
abbrev Irr (G : Type*) [Group G] : Set (G → ℂ) := TauCeti.irreducibleCharacters ℂ G

/-- Class functions. -/
def IsClassFn {G : Type*} [Group G] (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

section Basic

variable {G : Type*} [Group G] [Fintype G]

/-- The pairing of class functions, `|G|⁻¹ ∑ₓ f(x) g(x⁻¹)`. -/
def ip (f g : G → ℂ) : ℂ := (Nat.card G : ℂ)⁻¹ * ∑ x : G, f x * g x⁻¹

theorem ip_add_left (f f' g : G → ℂ) : ip (f + f') g = ip f g + ip f' g := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem ip_smul_left (c : ℂ) (f g : G → ℂ) : ip (c • f) g = c * ip f g := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]; ring

theorem ip_sub_left (f f' g : G → ℂ) : ip (f - f') g = ip f g - ip f' g := by
  simp only [ip, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem ip_zero_left (g : G → ℂ) : ip 0 g = 0 := by simp [ip]

theorem ip_sum_left {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (g : G → ℂ) :
    ip (∑ i ∈ s, f i) g = ∑ i ∈ s, ip (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_left, ih]

theorem ip_comm (f g : G → ℂ) : ip f g = ip g f := by
  simp only [ip]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

theorem ip_smul_right (c : ℂ) (f g : G → ℂ) : ip f (c • g) = c * ip f g := by
  rw [ip_comm, ip_smul_left, ip_comm]

theorem ip_sum_right {ι : Type*} (s : Finset ι) (f : G → ℂ) (g : ι → G → ℂ) :
    ip f (∑ i ∈ s, g i) = ∑ i ∈ s, ip f (g i) := by
  rw [ip_comm, ip_sum_left]; simp_rw [ip_comm f]

theorem isClassFn_add {f g : G → ℂ} (hf : IsClassFn f) (hg : IsClassFn g) : IsClassFn (f + g) :=
  fun x h => by simp [hf x h, hg x h]

theorem isClassFn_sub {f g : G → ℂ} (hf : IsClassFn f) (hg : IsClassFn g) : IsClassFn (f - g) :=
  fun x h => by simp [hf x h, hg x h]

theorem isClassFn_smul (c : ℂ) {f : G → ℂ} (hf : IsClassFn f) : IsClassFn (c • f) :=
  fun x h => by simp [hf x h]

theorem isClassFn_zero : IsClassFn (0 : G → ℂ) := fun _ _ => rfl

theorem isClassFn_sum {ι : Type*} (s : Finset ι) {f : ι → G → ℂ} (hf : ∀ i ∈ s, IsClassFn (f i)) :
    IsClassFn (∑ i ∈ s, f i) := by
  intro x h
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hf i hi x h

theorem IsClassFn.conj_eq {f : G → ℂ} (hf : IsClassFn f) (g h : G) : f (h⁻¹ * g * h) = f g := by
  simpa using hf g h⁻¹

theorem IsClassFn.mul_comm {f : G → ℂ} (hf : IsClassFn f) (a b : G) : f (a * b) = f (b * a) := by
  have := hf (b * a) a
  rw [← this]; congr 1; group

end Basic

section Irr

variable {G : Type*} [Group G] [Fintype G]

theorem irr_isClassFn {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsClassFn χ := by
  obtain ⟨n, ρ, -, rfl⟩ := hχ
  intro g h
  exact Representation.char_conj ρ g h

/-- Orthonormality of the irreducible characters. -/
theorem ip_irr {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    ip χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  obtain ⟨m, σ, hσ, rfl⟩ := hψ
  have h := Representation.char_orthonormal ρ σ
  simp only [ip]
  by_cases he : ρ.character = σ.character
  · rw [if_pos he, ← he]
    have h' := Representation.char_orthonormal ρ ρ
    rwa [if_pos ⟨Representation.Equiv.refl ρ⟩] at h'
  · rw [if_neg he, h, if_neg]
    rintro ⟨e⟩
    exact he (Representation.char_iso e).symm

theorem ip_irr_self {χ : G → ℂ} (hχ : χ ∈ Irr G) : ip χ χ = 1 := by
  rw [ip_irr hχ hχ, if_pos rfl]

theorem irr_one {χ : G → ℂ} (hχ : χ ∈ Irr G) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  exact ⟨Module.finrank ℂ (Fin n → ℂ), hρ.finrank_pos, Representation.char_one ρ⟩

/-- The irreducible characters as a finset. -/
def irrFinset (G : Type*) [Group G] [Fintype G] : Finset (G → ℂ) :=
  Finset.univ.image (TauCeti.irreducibleCharacter ℂ (G := G))

theorem mem_irrFinset {χ : G → ℂ} : χ ∈ irrFinset G ↔ χ ∈ Irr G := by
  simp only [irrFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact TauCeti.irreducibleCharacter_mem ℂ i
  · intro h; exact TauCeti.exists_irreducibleCharacter_eq ℂ h

/-- Completeness: a class function is the sum of its components along the irreducible characters. -/
theorem classFn_eq_sum {f : G → ℂ} (hf : IsClassFn f) : f = ∑ ψ ∈ irrFinset G, ip f ψ • ψ := by
  let b := TauCeti.basisIrreducibleCharacter ℂ G
  let f' : TauCeti.ClassFunction ℂ G := ⟨f, fun g h => hf g h⟩
  have hsum := b.sum_repr f'
  have hfun : f = ∑ i, (b.repr f') i • TauCeti.irreducibleCharacter ℂ i := by
    funext g
    calc f g = (f' : G → ℂ) g := rfl
      _ = ((∑ i, (b.repr f') i • b i : TauCeti.ClassFunction ℂ G) : G → ℂ) g := by rw [hsum]
      _ = _ := by
        rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, TauCeti.basisIrreducibleCharacter_apply]
  -- the coefficients are the pairings
  have hcoef : ∀ j, ip f (TauCeti.irreducibleCharacter ℂ j) = (b.repr f') j := by
    intro j
    conv_lhs => rw [hfun]
    rw [ip_sum_left]
    simp_rw [ip_smul_left]
    rw [Finset.sum_eq_single j]
    · rw [ip_irr_self (TauCeti.irreducibleCharacter_mem ℂ j), mul_one]
    · intro i _ hij
      rw [ip_irr (TauCeti.irreducibleCharacter_mem ℂ i) (TauCeti.irreducibleCharacter_mem ℂ j),
        if_neg (fun h => hij (TauCeti.irreducibleCharacter_injective ℂ h)), mul_zero]
    · simp
  conv_lhs => rw [hfun]
  rw [irrFinset, Finset.sum_image (fun i _ j _ h => TauCeti.irreducibleCharacter_injective ℂ h)]
  exact Finset.sum_congr rfl fun i _ => by rw [hcoef]

end Irr

section NatComb

variable {G : Type*} [Group G] [Fintype G]

/-- The character of a finite-dimensional complex representation. -/
def IsChar (f : G → ℂ) : Prop := ∃ (n : ℕ) (ρ : Representation ℂ G (Fin n → ℂ)), ρ.character = f

/-- Class functions with natural multiplicities: exactly the characters, as combinations of `Irr G`. -/
def IsNatComb (f : G → ℂ) : Prop := IsClassFn f ∧ ∀ ψ ∈ Irr G, ∃ n : ℕ, ip f ψ = n

theorem IsChar.isNatComb {f : G → ℂ} (hf : IsChar f) : IsNatComb f := by
  obtain ⟨n, σ, rfl⟩ := hf
  refine ⟨fun g h => Representation.char_conj σ g h, fun ψ hψ => ?_⟩
  obtain ⟨m, ρ, hρ, rfl⟩ := hψ
  exact ⟨_, Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ⟩

theorem irr_isChar {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsChar χ := by
  obtain ⟨n, ρ, -, rfl⟩ := hχ
  exact ⟨n, ρ, rfl⟩

theorem irr_isNatComb {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsNatComb χ := (irr_isChar hχ).isNatComb

theorem isNatComb_zero : IsNatComb (0 : G → ℂ) :=
  ⟨isClassFn_zero, fun ψ _ => ⟨0, by rw [ip_zero_left]; simp⟩⟩

theorem IsNatComb.add {f g : G → ℂ} (hf : IsNatComb f) (hg : IsNatComb g) : IsNatComb (f + g) := by
  refine ⟨isClassFn_add hf.1 hg.1, fun ψ hψ => ?_⟩
  obtain ⟨a, ha⟩ := hf.2 ψ hψ
  obtain ⟨b, hb⟩ := hg.2 ψ hψ
  exact ⟨a + b, by rw [ip_add_left, ha, hb]; push_cast; ring⟩

theorem IsNatComb.nsmul {f : G → ℂ} (hf : IsNatComb f) (n : ℕ) : IsNatComb ((n : ℂ) • f) := by
  refine ⟨isClassFn_smul _ hf.1, fun ψ hψ => ?_⟩
  obtain ⟨a, ha⟩ := hf.2 ψ hψ
  exact ⟨n * a, by rw [ip_smul_left, ha]; push_cast; ring⟩

theorem isNatComb_sum {ι : Type*} (s : Finset ι) {f : ι → G → ℂ} (hf : ∀ i ∈ s, IsNatComb (f i)) :
    IsNatComb (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isNatComb_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The multiplicity of `ψ` in `f`, as a natural number. -/
def mult (f ψ : G → ℂ) : ℕ := ⌊(ip f ψ).re⌋₊

theorem IsNatComb.mult_eq {f ψ : G → ℂ} (hf : IsNatComb f) (hψ : ψ ∈ Irr G) :
    (mult f ψ : ℂ) = ip f ψ := by
  obtain ⟨n, hn⟩ := hf.2 ψ hψ
  rw [mult, hn]
  simp

theorem irr_mult {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    mult χ ψ = if χ = ψ then 1 else 0 := by
  have h := (irr_isNatComb hχ).mult_eq hψ
  rw [ip_irr hχ hψ] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- A natural combination is the sum of its constituents with multiplicities. -/
theorem IsNatComb.eq_sum {f : G → ℂ} (hf : IsNatComb f) :
    f = ∑ ψ ∈ irrFinset G, (mult f ψ : ℂ) • ψ := by
  conv_lhs => rw [classFn_eq_sum hf.1]
  exact Finset.sum_congr rfl fun ψ hψ => by rw [hf.mult_eq (mem_irrFinset.mp hψ)]

/-- The pairing of two natural combinations is a natural number. -/
theorem ip_natComb {f g : G → ℂ} (hf : IsNatComb f) (hg : IsNatComb g) :
    ip f g = ∑ ψ ∈ irrFinset G, ((mult f ψ * mult g ψ : ℕ) : ℂ) := by
  conv_lhs => rw [hf.eq_sum, hg.eq_sum]
  rw [ip_sum_left]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  rw [ip_smul_left, ip_sum_right]
  rw [Finset.sum_eq_single ψ]
  · rw [ip_smul_right, ip_irr_self (mem_irrFinset.mp hψ)]; push_cast; ring
  · intro φ hφ hne
    rw [ip_smul_right, ip_irr (mem_irrFinset.mp hψ) (mem_irrFinset.mp hφ), if_neg (Ne.symm hne)]
    simp
  · intro h; exact absurd hψ h

theorem ip_natComb_self {f : G → ℂ} (hf : IsNatComb f) :
    ip f f = ∑ ψ ∈ irrFinset G, ((mult f ψ ^ 2 : ℕ) : ℂ) := by
  rw [ip_natComb hf hf]; simp [sq]

/-- `f ≤ g` for natural combinations: `g - f` is a natural combination. -/
def CharLE (f g : G → ℂ) : Prop := IsNatComb (g - f)

theorem CharLE.mult_le {f g ψ : G → ℂ} (hf : IsNatComb f) (h : CharLE f g) (hψ : ψ ∈ Irr G) :
    mult f ψ ≤ mult g ψ := by
  have hg : IsNatComb g := by simpa using hf.add h
  have h1 := hf.mult_eq hψ
  have h2 := hg.mult_eq hψ
  have h3 := h.mult_eq hψ
  rw [ip_sub_left, ← h1, ← h2] at h3
  have : (mult g ψ : ℂ) = mult f ψ + mult (g - f) ψ := by rw [h3]; ring
  have : mult g ψ = mult f ψ + mult (g - f) ψ := by exact_mod_cast this
  omega

/-- The degree of a natural combination. -/
theorem IsNatComb.one_eq {f : G → ℂ} (hf : IsNatComb f) :
    ∃ d : ℕ, f 1 = d ∧ (d = 0 → f = 0) := by
  have hsum := hf.eq_sum
  choose deg hdeg using fun ψ : {ψ // ψ ∈ irrFinset G} => irr_one (mem_irrFinset.mp ψ.2)
  refine ⟨∑ ψ ∈ (irrFinset G).attach, mult f ψ * deg ψ, ?_, ?_⟩
  · conv_lhs => rw [hsum]
    rw [Finset.sum_apply, ← Finset.sum_attach]
    push_cast
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Pi.smul_apply, (hdeg ψ).2, smul_eq_mul]
  · intro h0
    rw [hsum]
    refine Finset.sum_eq_zero fun ψ hψ => ?_
    have hle : mult f ψ * deg ⟨ψ, hψ⟩ = 0 :=
      Finset.sum_eq_zero_iff.mp h0 ⟨ψ, hψ⟩ (Finset.mem_attach _ _)
    have hpos := (hdeg ⟨ψ, hψ⟩).1
    have : mult f ψ = 0 := by
      rcases Nat.mul_eq_zero.mp hle with h | h
      · exact h
      · omega
    rw [this]; simp

end NatComb

section IrrCrit

variable {G : Type*} [Group G] [Fintype G]

/-- A natural combination of norm one is irreducible. -/
theorem irr_of_natComb {f : G → ℂ} (hf : IsNatComb f) (h1 : ip f f = 1) : f ∈ Irr G := by
  rw [ip_natComb_self hf] at h1
  have hN : ∑ ψ ∈ irrFinset G, mult f ψ ^ 2 = 1 := by exact_mod_cast h1
  obtain ⟨ψ, hψ, hne⟩ : ∃ ψ ∈ irrFinset G, mult f ψ ^ 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero hc] at hN
    exact zero_ne_one hN
  have hsplit := Finset.add_sum_erase (irrFinset G) (fun φ => mult f φ ^ 2) hψ
  rw [hN] at hsplit
  have hpos : 1 ≤ mult f ψ ^ 2 := Nat.one_le_iff_ne_zero.mpr hne
  have hrest : ∑ φ ∈ (irrFinset G).erase ψ, mult f φ ^ 2 = 0 := by omega
  have hψ1 : mult f ψ = 1 := by
    have : mult f ψ ^ 2 = 1 := by omega
    rcases Nat.lt_or_ge (mult f ψ) 2 with h | h
    · interval_cases (mult f ψ) <;> simp_all
    · nlinarith
  have hzero : ∀ φ ∈ (irrFinset G).erase ψ, mult f φ = 0 := fun φ hφ => by
    have := Finset.sum_eq_zero_iff.mp hrest φ hφ
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have : f = ψ := by
    rw [hf.eq_sum, ← Finset.add_sum_erase _ _ hψ, hψ1, Finset.sum_eq_zero fun φ hφ => by
      rw [hzero φ hφ]; simp]
    simp
  rw [this]; exact mem_irrFinset.mp hψ

/-- An irreducible constituent lies below. -/
theorem charLE_of_mult_pos {f ψ : G → ℂ} (hf : IsNatComb f) (hψ : ψ ∈ Irr G) (h : 1 ≤ mult f ψ) :
    CharLE ψ f := by
  refine ⟨isClassFn_sub hf.1 (irr_isClassFn hψ), fun φ hφ => ?_⟩
  rw [ip_sub_left, ← hf.mult_eq hφ, ← (irr_isNatComb hψ).mult_eq hφ, irr_mult hψ hφ]
  by_cases he : ψ = φ
  · subst he
    refine ⟨mult f ψ - 1, ?_⟩
    rw [if_pos rfl]; push_cast [h]; ring
  · exact ⟨mult f φ, by rw [if_neg he]; simp⟩

theorem mult_nsmul {f ψ : G → ℂ} (hf : IsNatComb f) (n : ℕ) (hψ : ψ ∈ Irr G) :
    mult ((n : ℂ) • f) ψ = n * mult f ψ := by
  have h := (hf.nsmul n).mult_eq hψ
  rw [ip_smul_left, ← hf.mult_eq hψ] at h
  exact_mod_cast h

theorem mult_sum {ι : Type*} (s : Finset ι) {f : ι → G → ℂ} (hf : ∀ i ∈ s, IsNatComb (f i))
    {ψ : G → ℂ} (hψ : ψ ∈ Irr G) : mult (∑ i ∈ s, f i) ψ = ∑ i ∈ s, mult (f i) ψ := by
  have h := (isNatComb_sum s hf).mult_eq hψ
  rw [ip_sum_left] at h
  have : ((mult (∑ i ∈ s, f i) ψ : ℕ) : ℂ) = ((∑ i ∈ s, mult (f i) ψ : ℕ) : ℂ) := by
    rw [h]; push_cast
    exact Finset.sum_congr rfl fun i hi => ((hf i hi).mult_eq hψ).symm
  exact_mod_cast this

end IrrCrit

section Pull

variable {G L : Type*} [Group G] [Fintype G] [Group L] [Fintype L]

/-- Pulling back a function along a homomorphism (restriction, when `φ` is an inclusion). -/
def pull (φ : L →* G) (f : G → ℂ) : L → ℂ := fun l => f (φ l)

@[simp] theorem pull_apply (φ : L →* G) (f : G → ℂ) (l : L) : pull φ f l = f (φ l) := rfl

theorem pull_sub (φ : L →* G) (f g : G → ℂ) : pull φ (f - g) = pull φ f - pull φ g := rfl
theorem pull_smul (φ : L →* G) (c : ℂ) (f : G → ℂ) : pull φ (c • f) = c • pull φ f := rfl
theorem pull_sum {ι : Type*} (φ : L →* G) (s : Finset ι) (f : ι → G → ℂ) :
    pull φ (∑ i ∈ s, f i) = ∑ i ∈ s, pull φ (f i) := by
  funext l; simp [pull, Finset.sum_apply]

theorem IsClassFn.pull {f : G → ℂ} (hf : IsClassFn f) (φ : L →* G) : IsClassFn (pull φ f) :=
  fun g h => by simp only [pull_apply, map_mul, map_inv]; exact hf _ _

theorem IsChar.pull {f : G → ℂ} (hf : IsChar f) (φ : L →* G) : IsChar (pull φ f) := by
  obtain ⟨n, ρ, rfl⟩ := hf
  refine ⟨n, ρ.comp φ, ?_⟩
  funext l
  rfl

theorem IsNatComb.pull {f : G → ℂ} (hf : IsNatComb f) (φ : L →* G) : IsNatComb (pull φ f) := by
  rw [hf.eq_sum, pull_sum]
  refine isNatComb_sum _ fun ψ hψ => ?_
  rw [pull_smul]
  exact ((irr_isChar (mem_irrFinset.mp hψ)).pull φ).isNatComb.nsmul _

theorem CharLE.pull {f g : G → ℂ} (h : CharLE f g) (φ : L →* G) : CharLE (pull φ f) (pull φ g) := by
  unfold CharLE; rw [← pull_sub]; exact IsNatComb.pull h φ

theorem ip_pull_mulEquiv (e : L ≃* G) (f g : G → ℂ) :
    ip (pull e.toMonoidHom f) (pull e.toMonoidHom g) = ip f g := by
  simp only [ip, pull_apply]
  rw [Nat.card_congr e.toEquiv]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun l => by simp)

theorem irr_pull_mulEquiv (e : L ≃* G) {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    pull e.toMonoidHom χ ∈ Irr L :=
  irr_of_natComb ((irr_isNatComb hχ).pull _) (by rw [ip_pull_mulEquiv, ip_irr_self hχ])

end Pull

section Ind

variable {G L : Type*} [Group G] [Fintype G] [Group L] [Fintype L]

/-- The induced class function along an injective homomorphism `ι : L → G`:
`f^G(g) = |L|⁻¹ ∑ₓ f°(x g x⁻¹)`, where `f°` extends `f` by zero off the image of `ι`. -/
def indHom (ι : L →* G) (f : L → ℂ) : G → ℂ :=
  fun g => (Nat.card L : ℂ)⁻¹ * ∑ x : G, Function.extend ι f 0 (x * g * x⁻¹)

theorem indHom_isClassFn (ι : L →* G) (f : L → ℂ) : IsClassFn (indHom ι f) := by
  intro g h
  simp only [indHom]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun x => by
    simp only [Equiv.coe_mulRight]; congr 1; group)

theorem sum_extend {ι : L →* G} (hι : Function.Injective ι) (F : L → ℂ) (χ : G → ℂ) :
    ∑ y : G, Function.extend ι F 0 y * χ y = ∑ l : L, F l * χ (ι l) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨ι, hι⟩))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [hι.extend_apply]
  · intro y _ hy
    have : ¬ ∃ l, ι l = y := fun ⟨l, hl⟩ => hy (Finset.mem_map.mpr ⟨l, Finset.mem_univ _, hl⟩)
    rw [Function.extend_apply' _ _ _ this]
    simp

/-- Frobenius reciprocity. -/
theorem ip_indHom {ι : L →* G} (hι : Function.Injective ι) (f : L → ℂ) {χ : G → ℂ}
    (hχ : IsClassFn χ) : ip (indHom ι f) χ = ip f (pull ι χ) := by
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have key : ∀ x : G, ∑ g : G, Function.extend ι f 0 (x * g * x⁻¹) * χ g⁻¹ =
      ∑ y : G, Function.extend ι f 0 y * χ y⁻¹ := by
    intro x
    exact Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      congr 1
      rw [show (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ by group, hχ])
  have h2 : ∑ y : G, Function.extend ι f 0 y * χ y⁻¹ = ∑ l : L, f l * pull ι χ l⁻¹ := by
    rw [sum_extend hι f (fun y => χ y⁻¹)]
    simp [pull]
  have e1 : ∀ g : G, ((Nat.card L : ℂ)⁻¹ * ∑ x : G, Function.extend ι f 0 (x * g * x⁻¹)) * χ g⁻¹ =
      (Nat.card L : ℂ)⁻¹ * ∑ x : G, Function.extend ι f 0 (x * g * x⁻¹) * χ g⁻¹ := by
    intro g; rw [mul_assoc, Finset.sum_mul]
  simp only [ip, indHom]
  rw [Finset.sum_congr rfl fun g _ => e1 g, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => key x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h2,
    ← Nat.card_eq_fintype_card]
  field_simp

theorem IsNatComb.indHom {ι : L →* G} (hι : Function.Injective ι) {f : L → ℂ} (hf : IsNatComb f) :
    IsNatComb (Gagola.indHom ι f) := by
  refine ⟨indHom_isClassFn ι f, fun ψ hψ => ?_⟩
  rw [ip_indHom hι f (irr_isClassFn hψ), ip_natComb hf ((irr_isNatComb hψ).pull ι)]
  exact ⟨∑ φ ∈ irrFinset L, mult f φ * mult (Gagola.pull ι ψ) φ, by push_cast; rfl⟩

end Ind

section IndSubgroup

variable {G : Type*} [Group G] [Fintype G]

/-- Induction from a subgroup. -/
abbrev ind (L : Subgroup G) (f : L → ℂ) : G → ℂ := indHom L.subtype f

theorem ip_ind (L : Subgroup G) (f : L → ℂ) {χ : G → ℂ} (hχ : IsClassFn χ) :
    ip (ind L f) χ = ip f (pull L.subtype χ) := ip_indHom (Subgroup.subtype_injective L) f hχ

theorem IsNatComb.ind {L : Subgroup G} {f : L → ℂ} (hf : IsNatComb f) : IsNatComb (ind L f) :=
  hf.indHom (Subgroup.subtype_injective L)

theorem ind_apply_of_normal (L : Subgroup G) [hL : L.Normal] (f : L → ℂ) (l : L) :
    ind L f l = (Nat.card L : ℂ)⁻¹ * ∑ x : G, f ⟨x * l * x⁻¹, hL.conj_mem _ l.2 x⟩ := by
  simp only [ind, indHom]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Subgroup.subtype_injective L).extend_apply f 0 ⟨x * l * x⁻¹, hL.conj_mem _ l.2 x⟩

end IndSubgroup


end

end CFSGOutside.Gagola
