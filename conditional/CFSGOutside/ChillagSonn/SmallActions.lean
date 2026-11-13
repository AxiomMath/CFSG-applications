import CFSGOutside.Corpus.FrattiniQuotientFacts
import CFSGOutside.ChillagSonn.Metacyclic

/-!
# Chillag–Sonn: small automorphism groups (Lemma 1.8, Step 4)

Two facts replacing the paper's appeals to Schur–Zassenhaus and to the solvability of `Aut(S)`:

* in `Aut(S)`, `S` elementary abelian of order `r²` (`r` odd), a Klein four-group contains the inversion map;
  automorphisms of a group of prime order commute;
* a perfect group centralizes every normal metacyclic 2-subgroup `S`: it acts trivially on `S/Φ(S)` (whose
  automorphism group embeds in `Sym(4)`, which is solvable), hence as a 2-group (Burnside), hence trivially.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus OrderReductions.FrattiniAutomorphisms

section Klein

variable {S : Type} [CommGroup S] [Finite S] {r : ℕ} [hr : Fact r.Prime]

/-- The fixed points of `t`. -/
private def fixSub (t : MulAut S) : Subgroup S where
  carrier := {x | t x = x}
  mul_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [map_mul, ha, hb]
  one_mem' := map_one t
  inv_mem' {a} ha := by simp only [Set.mem_ofPred_eq] at *; rw [map_inv, ha]

/-- The points inverted by `t`. -/
private def negSub (t : MulAut S) : Subgroup S where
  carrier := {x | t x = x⁻¹}
  mul_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [map_mul, ha, hb, mul_inv]
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, inv_one]
  inv_mem' {a} ha := by simp only [Set.mem_ofPred_eq] at *; rw [map_inv, ha]

omit [Finite S] in
/-- In a group of odd prime exponent, `x ^ 2 = 1` forces `x = 1`. -/
private theorem eq_one_of_sq_eq_one (hr2 : r ≠ 2) (hexp : ∀ x : S, x ^ r = 1) {x : S} (hx : x ^ 2 = 1) :
    x = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨hx, hexp x⟩
  rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Nat.prime_two hr.out).mpr (Ne.symm hr2)), pow_one] at h

/-- If `a * b = r²` with `a, b ≠ 1`, then `a = b = r`. -/
private theorem eq_of_mul_eq_sq {a b : ℕ} (h : a * b = r ^ 2) (ha : a ≠ 1) (hb : b ≠ 1) : a = r ∧ b = r := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hr.out).mp (Dvd.intro b h)
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hr.out).mp (Dvd.intro_left _ h)
  rw [← pow_add] at h
  have := Nat.pow_right_injective hr.out.two_le h
  interval_cases i <;> interval_cases j <;> simp_all

/-- An involution preserving a subgroup `C` of order `r` acts on `C` trivially or by inversion. -/
private theorem sign_of_card_prime (hexp : ∀ x : S, x ^ r = 1) (C : Subgroup S) (hC : Nat.card C = r)
    {σ : MulAut S} (hσ : σ ^ 2 = 1) (hσC : ∀ x ∈ C, σ x ∈ C) :
    (∀ x ∈ C, σ x = x) ∨ (∀ x ∈ C, σ x = x⁻¹) := by
  have := isCyclic_of_prime_card hC
  obtain ⟨m, hm⟩ := ((σ.toMonoidHom.comp C.subtype).codRestrict C fun x ↦ hσC x x.2).map_cyclic
  have hm' : ∀ x ∈ C, σ x = x ^ m := fun x hx ↦ congrArg Subtype.val (hm ⟨x, hx⟩)
  have : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (hC ▸ hr.out.one_lt)
  obtain ⟨⟨g, hgC⟩, hg1⟩ := exists_ne (1 : C)
  have hog : orderOf g = r := orderOf_eq_prime (hexp g) fun h ↦ hg1 (Subtype.ext h)
  have h2 : σ (σ g) = g := by rw [← MulAut.mul_apply, ← sq, hσ]; rfl
  rw [hm' _ (hσC g hgC), hm' g hgC, ← zpow_mul] at h2
  have hd := orderOf_dvd_iff_zpow_eq_one.mpr (show g ^ ((m - 1) * (m + 1)) = 1 by
    rw [show (m - 1) * (m + 1) = m * m - 1 by ring, zpow_sub_one, h2, mul_inv_cancel])
  rw [hog] at hd
  have hx : ∀ x : S, ∀ k : ℤ, (r : ℤ) ∣ k → x ^ k = 1 := fun x k hk ↦ orderOf_dvd_iff_zpow_eq_one.mp
    ((Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one (hexp x))).trans hk)
  rcases (Nat.prime_iff_prime_int.mp hr.out).dvd_or_dvd hd with h | h
  · refine Or.inl fun x hxC ↦ ?_
    rw [hm' x hxC, ← sub_add_cancel m 1, zpow_add_one, hx x _ h, one_mul]
  · exact Or.inr fun x hxC ↦ by rw [hm' x hxC]; exact eq_inv_of_mul_eq_one_left (by rw [← zpow_add_one, hx x _ h])

/-- `exists_inversion_of_klein` for a commutative group. -/
private theorem klein_aux (hr2 : r ≠ 2) (hexp : ∀ x : S, x ^ r = 1) (hcard : Nat.card S = r ^ 2)
    {t u : MulAut S} (ht : t ^ 2 = 1) (hu : u ^ 2 = 1) (htu : t * u = u * t) (ht1 : t ≠ 1) (hu1 : u ≠ 1)
    (hne : t ≠ u) :
    (∀ x, t x = x⁻¹) ∨ (∀ x, u x = x⁻¹) ∨ (∀ x, (t * u) x = x⁻¹) := by
  by_cases hti : ∀ x, t x = x⁻¹
  · exact Or.inl hti
  simp only [not_forall] at hti
  obtain ⟨y, hy⟩ := hti
  obtain ⟨z, hz⟩ : ∃ z, t z ≠ z := by
    by_contra! h
    exact ht1 (MulEquiv.ext h)
  have htt : ∀ x, t (t x) = x := fun x ↦ by rw [← MulAut.mul_apply, ← sq, ht]; rfl
  have hut : ∀ x, t (u x) = u (t x) := fun x ↦ by rw [← MulAut.mul_apply, htu]; rfl
  obtain ⟨h, hh⟩ : ∃ h : ℕ, 2 * h = r + 1 := by
    obtain ⟨k, hk⟩ := hr.out.odd_of_ne_two hr2
    exact ⟨k + 1, by omega⟩
  set A := fixSub t
  set B := negSub t
  have hA : ∀ x, x ∈ A ↔ t x = x := fun _ ↦ Iff.rfl
  have hB : ∀ x, x ∈ B ↔ t x = x⁻¹ := fun _ ↦ Iff.rfl
  have hdec : ∀ x, ∃ α ∈ A, ∃ β ∈ B, x = α * β := fun x ↦
    ⟨(x * t x) ^ h, by rw [hA, map_pow, map_mul, htt, mul_comm],
      (x * (t x)⁻¹) ^ h, by rw [hB, map_pow, map_mul, map_inv, htt, ← inv_pow, mul_inv_rev, inv_inv],
      by rw [← mul_pow, mul_mul_mul_comm, mul_inv_cancel, mul_one, ← sq, ← pow_mul, hh, pow_succ, hexp, one_mul]⟩
  let f := A.subtype.coprod B.subtype
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun ⟨a, b⟩ hab ↦ ?_
    have hab' : (a : S) = (b : S)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have ha1 : (a : S) = 1 := eq_one_of_sq_eq_one hr2 hexp (by
      have h1 : t a = a := a.2
      have h2 : t a = (a : S)⁻¹ := by rw [hab', map_inv, (hB _).mp b.2, inv_inv]
      rw [sq, ← mul_inv_cancel (a : S), ← h2, h1])
    have hb1 : (b : S) = 1 := by rw [← inv_inj, ← hab', ha1, inv_one]
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hsurj : Function.Surjective f := fun x ↦ by
    obtain ⟨α, hα, β, hβ, rfl⟩ := hdec x
    exact ⟨(⟨α, hα⟩, ⟨β, hβ⟩), rfl⟩
  have hcAB : Nat.card A * Nat.card B = r ^ 2 := by
    rw [← Nat.card_prod, ← hcard]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  have hA1 : Nat.card A ≠ 1 := fun h1 ↦ by
    have hm : y * t y ∈ A := by rw [hA, map_mul, htt, mul_comm]
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hm
    exact hy (eq_inv_of_mul_eq_one_right hm)
  have hB1 : Nat.card B ≠ 1 := fun h1 ↦ by
    have hm : z * (t z)⁻¹ ∈ B := by rw [hB, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hz hm.symm
  obtain ⟨hAr, hBr⟩ := eq_of_mul_eq_sq hcAB hA1 hB1
  have huA : ∀ x ∈ A, u x ∈ A := fun x hx ↦ by rw [hA, hut, (hA x).mp hx]
  have huB : ∀ x ∈ B, u x ∈ B := fun x hx ↦ by rw [hB, hut, (hB x).mp hx, map_inv]
  rcases sign_of_card_prime hexp A hAr hu huA with hua | hua <;>
    rcases sign_of_card_prime hexp B hBr hu huB with hub | hub
  · exact absurd (MulEquiv.ext fun x ↦ by
      obtain ⟨α, hα, β, hβ, rfl⟩ := hdec x
      rw [map_mul, hua α hα, hub β hβ]; rfl) hu1
  · exact absurd (MulEquiv.ext fun x ↦ by
      obtain ⟨α, hα, β, hβ, rfl⟩ := hdec x
      rw [map_mul, map_mul, hua α hα, hub β hβ, (hA α).mp hα, (hB β).mp hβ]) hne
  · refine Or.inr (Or.inr fun x ↦ ?_)
    obtain ⟨α, hα, β, hβ, rfl⟩ := hdec x
    rw [MulAut.mul_apply, map_mul, hua α hα, hub β hβ, map_mul, map_inv, (hA α).mp hα, (hB β).mp hβ, mul_inv]
  · refine Or.inr (Or.inl fun x ↦ ?_)
    obtain ⟨α, hα, β, hβ, rfl⟩ := hdec x
    rw [map_mul, hua α hα, hub β hβ, mul_inv]

end Klein

/-- In `Aut(S)`, `S` abelian of order `r²` and exponent `r` (`r` an odd prime), any two distinct commuting
nontrivial involutions `t`, `u`: one of `t`, `u`, `t * u` is the inversion map. -/
theorem exists_inversion_of_klein {S : Type} [Group S] [Finite S] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hcomm : ∀ a b : S, a * b = b * a) (hexp : ∀ x : S, x ^ r = 1) (hcard : Nat.card S = r ^ 2)
    {t u : MulAut S} (ht : t ^ 2 = 1) (hu : u ^ 2 = 1) (htu : t * u = u * t) (ht1 : t ≠ 1) (hu1 : u ≠ 1)
    (hne : t ≠ u) :
    (∀ x, t x = x⁻¹) ∨ (∀ x, u x = x⁻¹) ∨ (∀ x, (t * u) x = x⁻¹) := by
  let : CommGroup S := { ‹Group S› with mul_comm := hcomm }
  exact klein_aux hr2 hexp hcard ht hu htu ht1 hu1 hne

/-- The automorphisms of a group of prime order commute. -/
theorem mulAut_comm_of_card_prime {S : Type} [Group S] [Finite S] {r : ℕ} [Fact r.Prime]
    (hcard : Nat.card S = r) (σ τ : MulAut S) : σ * τ = τ * σ := by
  have := isCyclic_of_prime_card hcard
  obtain ⟨m, hm⟩ := σ.toMonoidHom.map_cyclic
  obtain ⟨n, hn⟩ := τ.toMonoidHom.map_cyclic
  have hm' : ∀ x, σ x = x ^ m := hm
  have hn' : ∀ x, τ x = x ^ n := hn
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply, hm' (τ x), hn' x, hn' (σ x), hm' x, ← zpow_mul, ← zpow_mul, mul_comm]

/-- A homomorphism from a perfect group to a solvable group is trivial. -/
private theorem eq_one_of_perfect {G H : Type*} [Group G] [Group H] [Group.IsSolvable H]
    (hperf : commutator G = ⊤) (f : G →* H) (g : G) : f g = 1 := by
  have : Group.IsPerfect G := ⟨hperf⟩
  have := Group.IsPerfect.range f
  rcases subsingleton_or_nontrivial f.range with h | h
  · exact congrArg Subtype.val (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)
  · exact (Group.IsPerfect.not_isSolvable f.range inferInstance).elim

/-- A perfect group acting on a normal metacyclic 2-subgroup centralizes it. -/
theorem le_center_of_perfect [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}] {G : Type}
    [Group G] [Finite G] (hperf : commutator G = ⊤) (S : Subgroup G) [S.Normal] (hS2 : IsPGroup 2 S)
    (hSm : IsMetacyclic S) : S ≤ Subgroup.center G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hexp, -⟩ := FrattiniElementaryQuotient.frattini_elementary_quotient hS2
  have hV : Nat.card (S ⧸ frattini S) ≤ 4 := Nat.le_of_dvd (by norm_num)
    ((hSm.of_surjective _ (QuotientGroup.mk'_surjective _)).card_dvd_sq hexp)
  have := Equiv.Perm.isSolvable hV
  have : Group.IsSolvable (MulAut (S ⧸ frattini S)) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b h ↦ MulEquiv.ext (Equiv.ext_iff.mp h)
  have hker : ∀ g : G, MulAut.conjNormal g ∈ (quotientAutomorphism (frattini S)).ker := fun g ↦
    eq_one_of_perfect hperf ((quotientAutomorphism (frattini S)).comp MulAut.conjNormal) g
  have := (FrattiniAutomorphismKernel.frattini_automorphism_kernel hS2).2.isNilpotent
  intro s hs
  refine Subgroup.mem_center_iff.mpr fun g ↦ ?_
  have h1 := congrArg Subtype.val (eq_one_of_perfect hperf (MulAut.conjNormal.codRestrict _ hker) g)
  have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨s, hs⟩)
  rw [MonoidHom.codRestrict_apply, MulAut.conjNormal_apply] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSGOutside.ChillagSonn
