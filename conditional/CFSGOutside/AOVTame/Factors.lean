import CFSGOutside.AOVTame.FusionPres
import CFSGOutside.Corpus.GoldschmidtTheoremA

/-!
# AOV tameness: direct factors of a Sylow 2-subgroup (AOV Lemma 3.4, Proposition 3.5)

For a finite group `G` with Sylow 2-subgroup `T` satisfying the group-level consequences of
reducedness (`Good`), a *direct decomposition* `T = X × Y` into strongly closed subgroups gives,
by Goldschmidt's Theorem A, normal subgroups `N_X × N_Y` of odd index. Using the focal subgroup
theorem (`foc(T) = T`), two decompositions have a common refinement (AOV Lemma 3.4); hence minimal
factors are permuted by fusion-preserving automorphisms (AOV Proposition 3.5).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] (T : Sylow 2 G)

/-- The group-level consequences of `F_T(G)` being reduced (with `O(G) = 1`). -/
structure Good : Prop where
  odd : goldschmidtOddCore G = ⊥
  two : ∀ D : Subgroup G, D.Normal → IsPGroup 2 D → D = ⊥
  norm : ∀ G₀ : Subgroup G, G₀.Normal → (T : Subgroup G) ≤ G₀ → ¬ 2 ∣ G₀.index →
    ∀ P : Subgroup G, P ≤ T → ∀ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ T →
      ∃ g₀ ∈ G₀, ∀ x ∈ P, g₀⁻¹ * x * g₀ = g⁻¹ * x * g
  foc : (T : Subgroup G) ≤ commutator G

/-- A direct decomposition `T = X × Y` into strongly closed subgroups. -/
structure Decomp (X Y : Subgroup G) : Prop where
  leX : X ≤ T
  leY : Y ≤ T
  inf : X ⊓ Y = ⊥
  comm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x
  sup : ∀ t ∈ (T : Subgroup G), ∃ x ∈ X, ∃ y ∈ Y, t = x * y
  scX : fusionStronglyClosed (X : Set G) T
  scY : fusionStronglyClosed (Y : Set G) T

variable {T}

lemma Decomp.symm {X Y : Subgroup G} (h : Decomp T X Y) : Decomp T Y X where
  leX := h.leY
  leY := h.leX
  inf := by rw [inf_comm]; exact h.inf
  comm y hy x hx := (h.comm x hx y hy).symm
  sup t ht := by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.sup t ht
    exact ⟨y, hy, x, hx, (h.comm x hx y hy)⟩
  scX := h.scY
  scY := h.scX

/-- Uniqueness of the decomposition. -/
lemma Decomp.unique {X Y : Subgroup G} (h : Decomp T X Y) {x x' y y' : G} (hx : x ∈ X)
    (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y) (e : x * y = x' * y') : x = x' ∧ y = y' := by
  have h1 : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [e]
      _ = y' * y⁻¹ := by group
  have h2 : x'⁻¹ * x ∈ X ⊓ Y := mem_inf.2 ⟨mul_mem (inv_mem hx') hx, h1 ▸ mul_mem hy' (inv_mem hy)⟩
  rw [h.inf, mem_bot] at h2
  have hxx : x = x' := by rw [← mul_inv_cancel_left x' x, h2, mul_one]
  subst hxx
  exact ⟨rfl, mul_left_cancel e⟩

/-- `X ∩ Y'`-type products: the subgroup `A B` of two commuting subgroups. -/
def prodSub (A B : Subgroup G) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
      _ = a * a' * (b * b') := by group
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    have := hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
    exact this.symm

section Goldschmidt
variable [GoldschmidtTheoremA] (hG : Good T) {X Y : Subgroup G} (h : Decomp T X Y)
include hG h

/-- Goldschmidt: the normal closures commute and meet trivially. -/
lemma Decomp.goldschmidt :
    ⁅normalClosure (X : Set G), normalClosure (Y : Set G)⁆ = ⊥ ∧
      normalClosure (X : Set G) ⊓ normalClosure (Y : Set G) = ⊥ := by
  have hcomm : ⁅X, Y⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (h.comm x hx y hy).symm
  have hG' := GoldschmidtTheoremA.theoremA T T h.leX h.leY h.scX h.scY hcomm h.inf
  rw [hG.odd, le_bot_iff] at hG'
  refine ⟨hG', ?_⟩
  set D := normalClosure (X : Set G) ⊓ normalClosure (Y : Set G)
  have hcD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    have : (⁅x, y⁆ : G) ∈ ⁅normalClosure (X : Set G), normalClosure (Y : Set G)⁆ :=
      commutator_mem_commutator (mem_inf.1 hx).1 (mem_inf.1 hy).2
    rw [hG', mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hn : Nat.card D ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  let Dm : Subgroup G :=
    { carrier := {x | x ∈ D ∧ x ^ m = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := by
        rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [(Commute.mul_pow (hcD x hx y hy) m), hxm, hym, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxm⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩ }
  have hDmn : Dm.Normal := ⟨fun x ⟨hx, hxm⟩ g =>
    ⟨(inferInstance : D.Normal).conj_mem x hx g, by rw [conj_pow, hxm]; group⟩⟩
  have hDmo : Odd (Nat.card Dm) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hzm : z ^ m = 1 := Subtype.ext z.2.2
    have := orderOf_dvd_of_pow_eq_one hzm
    rw [hz] at this
    exact hm.not_two_dvd_nat this
  have hDm : Dm ≤ ⊥ := hG.odd ▸ le_sSup ⟨hDmn, hDmo⟩
  have hDp : IsPGroup 2 D := by
    intro x
    refine ⟨k, Subtype.ext ?_⟩
    have hx1 : (x : G) ^ (2 ^ k * m) = 1 := by
      rw [← hkm]
      have := pow_card_eq_one' (G := D) (x := x)
      exact congrArg Subtype.val this
    have : (x : G) ^ 2 ^ k ∈ Dm := ⟨pow_mem x.2 _, by rw [← pow_mul, hx1]⟩
    simpa using hDm this
  exact hG.two D inferInstance hDp

lemma Decomp.commute_N {a b : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : b ∈ normalClosure (Y : Set G)) : a * b = b * a := by
  have : (⁅a, b⁆ : G) ∈ ⁅normalClosure (X : Set G), normalClosure (Y : Set G)⁆ :=
    commutator_mem_commutator ha hb
  rw [(h.goldschmidt hG).1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

lemma Decomp.eq_one_N {a : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : a ∈ normalClosure (Y : Set G)) : a = 1 := by
  have : a ∈ normalClosure (X : Set G) ⊓ normalClosure (Y : Set G) := mem_inf.2 ⟨ha, hb⟩
  rwa [(h.goldschmidt hG).2, mem_bot] at this

/-- Uniqueness of decompositions in `N_X × N_Y`. -/
lemma Decomp.unique_N {a a' b b' : G} (ha : a ∈ normalClosure (X : Set G))
    (ha' : a' ∈ normalClosure (X : Set G)) (hb : b ∈ normalClosure (Y : Set G))
    (hb' : b' ∈ normalClosure (Y : Set G)) (e : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [e]
      _ = b' * b⁻¹ := by group
  have h2 := h.eq_one_N hG (mul_mem (inv_mem ha') ha) (h1 ▸ mul_mem hb' (inv_mem hb))
  have hxx : a = a' := by rw [← mul_inv_cancel_left a' a, h2, mul_one]
  subst hxx
  exact ⟨rfl, mul_left_cancel e⟩

/-- Every conjugation in `T` is induced by `N_X N_Y`. -/
lemma Decomp.realize {P : Subgroup G} (hP : P ≤ T) {g : G}
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ T) :
    ∃ a ∈ normalClosure (X : Set G), ∃ b ∈ normalClosure (Y : Set G),
      ∀ x ∈ P, (a * b)⁻¹ * x * (a * b) = g⁻¹ * x * g := by
  set N := normalClosure (X : Set G) ⊔ normalClosure (Y : Set G)
  have hTN : (T : Subgroup G) ≤ N := by
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := h.sup t ht
    exact mul_mem (mem_sup_left (subset_normalClosure hx)) (mem_sup_right (subset_normalClosure hy))
  have hidx : ¬ 2 ∣ N.index := fun h2 => T.not_dvd_index (h2.trans (index_dvd_of_le hTN))
  obtain ⟨g₀, hg₀, hx⟩ := hG.norm N inferInstance hTN hidx P hP g hg
  have hg₀' : g₀ ∈ ((normalClosure (X : Set G) ⊔ normalClosure (Y : Set G) : Subgroup G) : Set G) := hg₀
  rw [mul_normal] at hg₀'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg₀'
  exact ⟨a, ha, b, hb, hx⟩

/-- Conjugating `x = x₁ x₂` by `a b ∈ N_X N_Y` conjugates the components separately. -/
lemma Decomp.conj_components {a b x₁ x₂ : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : b ∈ normalClosure (Y : Set G)) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ Y) :
    (a * b)⁻¹ * (x₁ * x₂) * (a * b) = (a⁻¹ * x₁ * a) * (b⁻¹ * x₂ * b) := by
  have c1 := h.commute_N hG (subset_normalClosure hx₁) hb
  have c2 := h.commute_N hG ha (subset_normalClosure hx₂)
  calc (a * b)⁻¹ * (x₁ * x₂) * (a * b) = b⁻¹ * (a⁻¹ * x₁ * (x₂ * a)) * b := by group
    _ = b⁻¹ * (a⁻¹ * x₁ * (a * x₂)) * b := by
        rw [show x₂ * a = a * x₂ from c2.symm]
    _ = b⁻¹ * (a⁻¹ * x₁ * a) * x₂ * b := by group
    _ = (a⁻¹ * x₁ * a) * (b⁻¹ * x₂ * b) := by
        have hc : b⁻¹ * (a⁻¹ * x₁ * a) = (a⁻¹ * x₁ * a) * b⁻¹ :=
          (h.commute_N hG (by
            have := (normalClosure_normal (s := (X : Set G))).conj_mem x₁ (subset_normalClosure hx₁) a⁻¹
            simpa using this) (inv_mem hb)).symm
        rw [hc]; group

/-- If `x₁ x₂ ∈ T`-conjugates stay in `T`, the conjugated components lie in `X` and `Y`. -/
lemma Decomp.conj_mem_X {a b x₁ x₂ : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : b ∈ normalClosure (Y : Set G)) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ Y)
    (hT : (a * b)⁻¹ * (x₁ * x₂) * (a * b) ∈ (T : Subgroup G)) :
    a⁻¹ * x₁ * a ∈ X ∧ b⁻¹ * x₂ * b ∈ Y := by
  obtain ⟨w₁, hw₁, w₂, hw₂, e⟩ := h.sup _ hT
  rw [h.conj_components hG ha hb hx₁ hx₂] at e
  have hNX : a⁻¹ * x₁ * a ∈ normalClosure (X : Set G) := by
    have := (normalClosure_normal (s := (X : Set G))).conj_mem x₁ (subset_normalClosure hx₁) a⁻¹
    simpa using this
  have hNY : b⁻¹ * x₂ * b ∈ normalClosure (Y : Set G) := by
    have := (normalClosure_normal (s := (Y : Set G))).conj_mem x₂ (subset_normalClosure hx₂) b⁻¹
    simpa using this
  obtain ⟨e1, e2⟩ := h.unique_N hG hNX (subset_normalClosure hw₁) hNY (subset_normalClosure hw₂) e
  exact ⟨e1 ▸ hw₁, e2 ▸ hw₂⟩

end Goldschmidt

section DoubleDecomp
variable [GoldschmidtTheoremA] (hG : Good T) {X Y X' Y' : Subgroup G} (h : Decomp T X Y)
  (h' : Decomp T X' Y')

/-- `(X ∩ X')(X ∩ Y')`. -/
def interProd (X X' Y' : Subgroup G) (h' : Decomp T X' Y') : Subgroup G :=
  prodSub (X ⊓ X') (X ⊓ Y') (fun a ha b hb => h'.comm a (mem_inf.1 ha).2 b (mem_inf.1 hb).2)

lemma interProd_le (h' : Decomp T X' Y') : interProd X X' Y' h' ≤ X := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem (mem_inf.1 ha).1 (mem_inf.1 hb).1

include hG h h' in
/-- The focal elements of `X` lie in `(X ∩ X')(X ∩ Y')`. -/
lemma foc_X {x a : G} (hx : x ∈ X) (hax : a⁻¹ * x * a ∈ X) :
    x⁻¹ * (a⁻¹ * x * a) ∈ interProd X X' Y' h' := by
  have hxT : x ∈ (T : Subgroup G) := h.leX hx
  have hP : zpowers x ≤ T := (zpowers_le).2 hxT
  have hPg : (zpowers x).map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have : (MulAut.conj a⁻¹) (x ^ k) = (a⁻¹ * x * a) ^ k := by
      have := map_zpow (MulAut.conj a⁻¹) x k
      simpa [MulAut.conj_apply] using this
    change (MulAut.conj a⁻¹) (x ^ k) ∈ (T : Subgroup G)
    rw [this]; exact zpow_mem (h.leX hax) k
  obtain ⟨c, hc, d, hd, hcd⟩ := h'.realize hG hP hPg
  have hcdx := hcd x (mem_zpowers x)
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h'.sup x hxT
  have hT : (c * d)⁻¹ * (x₁ * x₂) * (c * d) ∈ (T : Subgroup G) := by
    rw [hcdx]; exact h.leX hax
  obtain ⟨m1, m2⟩ := h'.conj_mem_X hG hc hd hx₁ hx₂ hT
  have hcx₂ : c * x₂ = x₂ * c := h'.commute_N hG hc (subset_normalClosure hx₂)
  have hdx₁ : x₁ * d = d * x₁ := h'.commute_N hG (subset_normalClosure hx₁) hd
  -- `c⁻¹ x c ∈ X` and `d⁻¹ x d ∈ X` by strong closure
  have ec : c⁻¹ * (x₁ * x₂) * c = (c⁻¹ * x₁ * c) * x₂ := by
    calc c⁻¹ * (x₁ * x₂) * c = c⁻¹ * x₁ * (x₂ * c) := by group
      _ = c⁻¹ * x₁ * (c * x₂) := by rw [hcx₂]
      _ = _ := by group
  have ed : d⁻¹ * (x₁ * x₂) * d = x₁ * (d⁻¹ * x₂ * d) := by
    calc d⁻¹ * (x₁ * x₂) * d = d⁻¹ * (x₁ * d) * (d⁻¹ * x₂ * d) := by group
      _ = d⁻¹ * (d * x₁) * (d⁻¹ * x₂ * d) := by rw [hdx₁]
      _ = _ := by group
  have hcX : c⁻¹ * (x₁ * x₂) * c ∈ X :=
    h.scX _ hx c (by rw [ec]; exact mul_mem (h'.leX m1) (h'.leY hx₂))
  have hdX : d⁻¹ * (x₁ * x₂) * d ∈ X :=
    h.scX _ hx d (by rw [ed]; exact mul_mem (h'.leX hx₁) (h'.leY m2))
  have hx₂c : x₂ * (x₁⁻¹ * (c⁻¹ * x₁ * c)) = (x₁⁻¹ * (c⁻¹ * x₁ * c)) * x₂ :=
    (h'.comm _ (mul_mem (inv_mem hx₁) m1) x₂ hx₂).symm
  refine ⟨x₁⁻¹ * (c⁻¹ * x₁ * c), mem_inf.2 ⟨?_, mul_mem (inv_mem hx₁) m1⟩,
    x₂⁻¹ * (d⁻¹ * x₂ * d), mem_inf.2 ⟨?_, mul_mem (inv_mem hx₂) m2⟩, ?_⟩
  · have : x₁⁻¹ * (c⁻¹ * x₁ * c) = (x₁ * x₂)⁻¹ * (c⁻¹ * (x₁ * x₂) * c) := by
      rw [ec]
      calc x₁⁻¹ * (c⁻¹ * x₁ * c) = x₂⁻¹ * (x₂ * (x₁⁻¹ * (c⁻¹ * x₁ * c))) := by group
        _ = x₂⁻¹ * ((x₁⁻¹ * (c⁻¹ * x₁ * c)) * x₂) := by rw [hx₂c]
        _ = _ := by group
    rw [this]; exact mul_mem (inv_mem hx) hcX
  · have : x₂⁻¹ * (d⁻¹ * x₂ * d) = (x₁ * x₂)⁻¹ * (d⁻¹ * (x₁ * x₂) * d) := by
      rw [ed]; group
    rw [this]; exact mul_mem (inv_mem hx) hdX
  · rw [← hcdx, h'.conj_components hG hc hd hx₁ hx₂]
    calc (x₁ * x₂)⁻¹ * ((c⁻¹ * x₁ * c) * (d⁻¹ * x₂ * d)) =
        x₂⁻¹ * (x₁⁻¹ * (c⁻¹ * x₁ * c)) * (d⁻¹ * x₂ * d) := by group
      _ = x₂⁻¹ * ((x₁⁻¹ * (c⁻¹ * x₁ * c)) * x₂) * x₂⁻¹ * (d⁻¹ * x₂ * d) := by group
      _ = x₂⁻¹ * (x₂ * (x₁⁻¹ * (c⁻¹ * x₁ * c))) * x₂⁻¹ * (d⁻¹ * x₂ * d) := by rw [hx₂c]
      _ = _ := by group

include hG h h' in
/-- The focal elements of `T` lie in `(X ∩ X')(X ∩ Y')(Y ∩ X')(Y ∩ Y')`. -/
lemma foc_T {w a : G} (hw : w ∈ (T : Subgroup G)) (haw : a⁻¹ * w * a ∈ (T : Subgroup G)) :
    w⁻¹ * (a⁻¹ * w * a) ∈ prodSub (interProd X X' Y' h') (interProd Y X' Y' h')
      (fun u hu v hv => h.comm u (interProd_le h' hu) v (interProd_le h' hv)) := by
  have hP : zpowers w ≤ T := (zpowers_le).2 hw
  have hPg : (zpowers w).map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have : (MulAut.conj a⁻¹) (w ^ k) = (a⁻¹ * w * a) ^ k := by
      have := map_zpow (MulAut.conj a⁻¹) w k
      simpa [MulAut.conj_apply] using this
    change (MulAut.conj a⁻¹) (w ^ k) ∈ (T : Subgroup G)
    rw [this]; exact zpow_mem haw k
  obtain ⟨c, hc, d, hd, hcd⟩ := h.realize hG hP hPg
  have hcdw := hcd w (mem_zpowers w)
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := h.sup w hw
  have hT : (c * d)⁻¹ * (w₁ * w₂) * (c * d) ∈ (T : Subgroup G) := by rw [hcdw]; exact haw
  obtain ⟨m1, m2⟩ := h.conj_mem_X hG hc hd hw₁ hw₂ hT
  have hcw : c⁻¹ * w₁ * c = (c⁻¹) * w₁ * (c⁻¹)⁻¹ := by group
  have f1 := foc_X hG h h' (x := w₁) (a := c) hw₁ m1
  have f2 := foc_X hG h.symm h' (x := w₂) (a := d) hw₂ m2
  refine ⟨_, f1, _, f2, ?_⟩
  rw [← hcdw, h.conj_components hG hc hd hw₁ hw₂]
  have hcomm : w₂ * (w₁⁻¹ * (c⁻¹ * w₁ * c)) = (w₁⁻¹ * (c⁻¹ * w₁ * c)) * w₂ :=
    (h.comm _ (mul_mem (inv_mem hw₁) m1) w₂ hw₂).symm
  calc (w₁ * w₂)⁻¹ * ((c⁻¹ * w₁ * c) * (d⁻¹ * w₂ * d)) =
      w₂⁻¹ * (w₁⁻¹ * (c⁻¹ * w₁ * c)) * (d⁻¹ * w₂ * d) := by group
    _ = w₂⁻¹ * ((w₁⁻¹ * (c⁻¹ * w₁ * c)) * w₂) * w₂⁻¹ * (d⁻¹ * w₂ * d) := by group
    _ = w₂⁻¹ * (w₂ * (w₁⁻¹ * (c⁻¹ * w₁ * c))) * w₂⁻¹ * (d⁻¹ * w₂ * d) := by rw [hcomm]
    _ = _ := by group

include hG h h' in
/-- **Double decomposition** (AOV Lemma 3.4): `X = (X ∩ X')(X ∩ Y')`. -/
theorem Decomp.refine {x : G} (hx : x ∈ X) : x ∈ interProd X X' Y' h' := by
  set R := prodSub (interProd X X' Y' h') (interProd Y X' Y' h')
    (fun u hu v hv => h.comm u (interProd_le h' hu) v (interProd_le h' hv))
  have hfoc : (T : Subgroup G).focalSubgroup ≤ R := by
    rw [focalSubgroup_def, closure_le]
    rintro g ⟨hgT, y, hy, u, rfl⟩
    have e : ⁅y, u⁆ = y⁻¹⁻¹ * ((u⁻¹)⁻¹ * y⁻¹ * u⁻¹) := by
      rw [commutatorElement_def]; group
    have hw : y⁻¹ ∈ (T : Subgroup G) := inv_mem hy
    have haw : (u⁻¹)⁻¹ * y⁻¹ * u⁻¹ ∈ (T : Subgroup G) := by
      have : (u⁻¹)⁻¹ * y⁻¹ * u⁻¹ = y⁻¹ * ⁅y, u⁆ := by rw [commutatorElement_def]; group
      rw [this]; exact mul_mem hw hgT
    rw [e]
    exact foc_T hG h h' hw haw
  have hTR : (T : Subgroup G) ≤ R := by
    have := commutator_inf_eq_focalSubgroup T
    intro t ht
    apply hfoc
    rw [← this]
    exact mem_inf.2 ⟨hG.foc ht, ht⟩
  obtain ⟨u, hu, v, hv, e⟩ := hTR (h.leX hx)
  obtain ⟨-, hv1⟩ := h.unique hx (interProd_le h' hu) (one_mem Y) (interProd_le h' hv)
    (by rw [mul_one]; exact e)
  rw [e, ← hv1, mul_one]; exact hu

end DoubleDecomp

section Closure

lemma sc_inf {X X' : Subgroup G} (hX : fusionStronglyClosed (X : Set G) T)
    (hX' : fusionStronglyClosed (X' : Set G) T) : fusionStronglyClosed ((X ⊓ X' : Subgroup G) : Set G) T :=
  fun a ha g hg => mem_inf.2 ⟨hX a (mem_inf.1 ha).1 g hg, hX' a (mem_inf.1 ha).2 g hg⟩

variable [GoldschmidtTheoremA] (hG : Good T) {X Y : Subgroup G} (h : Decomp T X Y)
include hG h

/-- A product `A B` with `A ≤ X`, `B ≤ Y` strongly closed is strongly closed. -/
lemma Decomp.sc_prodSub {A B : Subgroup G} (hAX : A ≤ X) (hBY : B ≤ Y)
    (hA : fusionStronglyClosed (A : Set G) T) (hB : fusionStronglyClosed (B : Set G) T) :
    fusionStronglyClosed (prodSub A B (fun a ha b hb => h.comm a (hAX ha) b (hBY hb)) : Set G) T := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ g hg
  have hab : a * b ∈ (T : Subgroup G) := mul_mem (h.leX (hAX ha)) (h.leY (hBY hb))
  have hP : zpowers (a * b) ≤ T := (zpowers_le).2 hab
  have hPg : (zpowers (a * b)).map (MulAut.conj g⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have : (MulAut.conj g⁻¹) ((a * b) ^ k) = (g⁻¹ * (a * b) * g) ^ k := by
      have := map_zpow (MulAut.conj g⁻¹) (a * b) k
      simpa [MulAut.conj_apply] using this
    change (MulAut.conj g⁻¹) ((a * b) ^ k) ∈ (T : Subgroup G)
    rw [this]; exact zpow_mem hg k
  obtain ⟨c, hc, d, hd, hcd⟩ := h.realize hG hP hPg
  have e := hcd (a * b) (mem_zpowers _)
  have hT : (c * d)⁻¹ * (a * b) * (c * d) ∈ (T : Subgroup G) := by rw [e]; exact hg
  obtain ⟨m1, m2⟩ := h.conj_mem_X hG hc hd (hAX ha) (hBY hb) hT
  rw [← e, h.conj_components hG hc hd (hAX ha) (hBY hb)]
  exact ⟨_, hA a ha c (h.leX m1), _, hB b hb d (h.leY m2), rfl⟩

variable {X' Y' : Subgroup G} (h' : Decomp T X' Y')
include h'

/-- The common refinement: `X ∩ X'` is a direct factor, with complement `(X ∩ Y') Y`. -/
lemma Decomp.inf_decomp :
    Decomp T (X ⊓ X') (prodSub (X ⊓ Y') Y (fun a ha b hb => h.comm a (mem_inf.1 ha).1 b hb)) where
  leX := inf_le_left.trans h.leX
  leY := by rintro _ ⟨a, ha, b, hb, rfl⟩; exact mul_mem (h.leX (mem_inf.1 ha).1) (h.leY hb)
  inf := by
    rw [eq_bot_iff]
    rintro e ⟨he, ⟨a, ha, b, hb, rfl⟩⟩
    have hbX : b ∈ X := by
      have := mul_mem (inv_mem (mem_inf.1 ha).1) (mem_inf.1 he).1
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ X ⊓ Y := mem_inf.2 ⟨hbX, hb⟩
      rwa [h.inf, mem_bot] at this
    subst hb1
    rw [mul_one] at he ⊢
    have : a ∈ X' ⊓ Y' := mem_inf.2 ⟨(mem_inf.1 he).2, (mem_inf.1 ha).2⟩
    rwa [h'.inf] at this
  comm := by
    rintro x hx _ ⟨a, ha, b, hb, rfl⟩
    have c1 : x * a = a * x := h'.comm x (mem_inf.1 hx).2 a (mem_inf.1 ha).2
    have c2 : x * b = b * x := h.comm x (mem_inf.1 hx).1 b hb
    calc x * (a * b) = (x * a) * b := by group
      _ = a * (x * b) := by rw [c1]; group
      _ = a * b * x := by rw [c2]; group
  sup := by
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := h.sup t ht
    obtain ⟨u, hu, v, hv, rfl⟩ := h.refine hG h' hx
    exact ⟨u, hu, v * y, ⟨v, hv, y, hy, rfl⟩, by group⟩
  scX := sc_inf h.scX h'.scX
  scY := h.sc_prodSub hG (A := X ⊓ Y') (B := Y) inf_le_left le_rfl (sc_inf h.scX h'.scY) h.scY

end Closure

section Minimal
variable (T)

/-- `X` is a direct factor of `T`. -/
def IsFactor (X : Subgroup G) : Prop := ∃ Y, Decomp T X Y

/-- `X` is a minimal nontrivial direct factor (the factor of an indecomposable factor). -/
def IsMinFactor (X : Subgroup G) : Prop :=
  IsFactor T X ∧ X ≠ ⊥ ∧ ∀ X' : Subgroup G, IsFactor T X' → X' ≤ X → X' = ⊥ ∨ X' = X

variable {T} [GoldschmidtTheoremA] (hG : Good T)
include hG

lemma IsMinFactor.le_or {X X' Y' : Subgroup G} (hX : IsMinFactor T X) (h' : Decomp T X' Y') :
    X ≤ X' ∨ X ≤ Y' := by
  obtain ⟨⟨Y, h⟩, hne, hmin⟩ := hX
  rcases hmin _ ⟨_, h.inf_decomp hG h'⟩ inf_le_left with h1 | h1
  · right
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := h.refine hG h' hx
    rw [h1, mem_bot] at hu
    rw [hu, one_mul]; exact (mem_inf.1 hv).2
  · left
    rw [← h1]; exact inf_le_right

end Minimal

end AndersenOliverVentura.Tame
