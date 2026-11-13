import CFSGOutside.Common.NonsolubleLength

/-!
# Operations on series of nonsoluble length

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780.

The series `NSeries` of `CFSGOutside.NonsolubleLength` can be lengthened by trivial factors
(`NSeries.lengthen`) and concatenated across two normal subgroups (`NSeries.interConcat`): from series of `X`
starting at `K_B` and at `K_A`, the series `K_A ∩ K_B ≤ K_A ∩ G^B_1 ≤ ⋯ ≤ K_A ≤ G^A_1 ≤ ⋯ ≤ X` of length the sum.
This is the series construction in the proof of Theorem 1.1. A normal subgroup of a finite direct product of
nonabelian simple groups is again such a product (`isSemisimpleProd_of_normal`), so soluble and semisimple
sections stay so after intersecting with a normal subgroup.
-/

namespace CFSGOutside.KhukhroShumyatskyFactorizedLength

open Subgroup CFSGOutside.NonsolubleLength

universe u

section Semisimple

/-- A normal subgroup of a finite direct product of nonabelian simple groups is again such a
product (namely of the factors it contains). -/
lemma isSemisimpleProd_of_normal {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, Group (S i)]
    (hS : ∀ i, IsSimpleGroup (S i)) (hnab : ∀ i, ∃ a b : S i, a * b ≠ b * a)
    (W : Subgroup (∀ i, S i)) [hW : W.Normal] : IsSemisimpleProd W := by
  classical
  haveI := Fintype.ofFinite ι
  let I : Set ι := {i | ∀ s : S i, Pi.mulSingle i s ∈ W}
  have hcenter : ∀ i (z : S i), (∀ g, z * g = g * z) → z = 1 := by
    intro i z hz
    haveI := hS i
    rcases (inferInstance : (center (S i)).Normal).eq_bot_or_eq_top with h | h
    · have : z ∈ center (S i) := mem_center_iff.2 fun g => (hz g).symm
      rwa [h, mem_bot] at this
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab i
      have : b ∈ center (S i) := h ▸ mem_top b
      exact hab (mem_center_iff.1 this a)
  have hout : ∀ w ∈ W, ∀ i ∉ I, w i = 1 := by
    intro w hw i hi
    haveI := hS i
    let Wi : Subgroup (S i) := W.comap (MonoidHom.mulSingle S i)
    have hWi : Wi = ⊥ := by
      rcases (hW.comap (MonoidHom.mulSingle S i)).eq_bot_or_eq_top with h | h
      · exact h
      · exact absurd (fun s => by
          have : s ∈ Wi := by
            show s ∈ comap (MonoidHom.mulSingle S i) W
            rw [h]; exact mem_top s
          exact this) hi
    refine hcenter i (w i) fun g => ?_
    have hc : w * Pi.mulSingle i g * w⁻¹ * (Pi.mulSingle i g)⁻¹ ∈ W := by
      have := hW.conj_mem _ (inv_mem hw) (Pi.mulSingle i g)
      simpa [mul_assoc] using mul_mem hw this
    have hc' : w * Pi.mulSingle i g * w⁻¹ * (Pi.mulSingle i g)⁻¹ =
        Pi.mulSingle i (w i * g * (w i)⁻¹ * g⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hc'] at hc
    have : w i * g * (w i)⁻¹ * g⁻¹ ∈ Wi := hc
    rw [hWi, mem_bot] at this
    have h2 := this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  let φ : W →* (∀ i : I, S i) :=
    { toFun := fun w i => (w : ∀ i, S i) i.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [mem_bot]
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · exact congrFun hw ⟨i, hi⟩
    · exact hout w w.2 i hi
  have hsurj : Function.Surjective φ := by
    intro f
    let g : ∀ i, S i := fun j => if h : j ∈ I then f ⟨j, h⟩ else 1
    have hg : g ∈ W := by
      rw [← Finset.noncommProd_mulSingle g]
      refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
      by_cases hj : j ∈ I
      · exact hj (g j)
      · simp [g, hj]
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    simp [φ, g, i.2]
  exact ⟨I, fun i => S i, fun i => inferInstance, inferInstance, fun i => hS i,
    fun i => hnab i, ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩⟩

lemma isSemisimpleProd_of_subsingleton (Y : Type u) [Group Y] [Subsingleton Y] :
    IsSemisimpleProd Y :=
  ⟨PEmpty, fun _ => PUnit, fun _ => inferInstance, inferInstance, fun i => i.elim,
    fun i => i.elim,
    ⟨{ toFun := fun _ => 1, invFun := fun _ => 1, left_inv := fun _ => Subsingleton.elim _ _,
       right_inv := fun _ => funext fun i => i.elim, map_mul' := fun _ _ => by simp }⟩⟩

end Semisimple

section Factors

variable {X : Type u} [Group X] [Finite X]

lemma solubleFactor_inf {N M : Subgroup X} (K : Subgroup X) [N.Normal] [K.Normal]
    (h : SolubleFactor N M) : SolubleFactor (K ⊓ N) (K ⊓ M) := by
  obtain ⟨k, hk⟩ := solubleFactor_iff.1 h
  exact solubleFactor_iff.2 ⟨k, le_inf ((dA_le k _).trans inf_le_left)
    ((dA_mono k inf_le_right).trans hk)⟩

lemma semisimpleFactor_inf {N M : Subgroup X} (K : Subgroup X) [N.Normal] [K.Normal]
    (h : SemisimpleFactor N M) : SemisimpleFactor (K ⊓ N) (K ⊓ M) := by
  obtain ⟨_, ι, S, _, hfin, hS, hnab, ⟨e⟩⟩ := h
  refine ⟨inferInstance, ?_⟩
  let ψ : (K ⊓ M : Subgroup X) →* M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' _).comp (inclusion inf_le_right)
  have hker : ψ.ker = (K ⊓ N).subgroupOf (K ⊓ M) := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
  set R := ψ.range
  haveI hR : R.Normal := by
    refine ⟨fun r hr q => ?_⟩
    obtain ⟨x, rfl⟩ := hr
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
    refine ⟨⟨(m : X) * x * (m : X)⁻¹, ‹K.Normal›.conj_mem _ (mem_inf.1 x.2).1 m,
      M.mul_mem (M.mul_mem m.2 (mem_inf.1 x.2).2) (M.inv_mem m.2)⟩, ?_⟩
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  haveI := hfin
  haveI : (R.map e.toMonoidHom).Normal := hR.map e.toMonoidHom e.surjective
  have hss := isSemisimpleProd_of_normal hS hnab (R.map e.toMonoidHom)
  exact hss.of_mulEquiv (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans (R.equivMapOfInjective _ e.injective))

lemma solubleFactor_self (A : Subgroup X) [A.Normal] : SolubleFactor A A :=
  solubleFactor_iff.2 ⟨0, le_rfl⟩

lemma semisimpleFactor_self (A : Subgroup X) : SemisimpleFactor A A := by
  haveI := subsingleton_quotient_self A
  haveI : (A.subgroupOf A).Normal := by rw [subgroupOf_self]; exact normal_top
  exact ⟨this, isSemisimpleProd_of_subsingleton _⟩

/-- Lengthen a series by trivial factors. -/
def NSeries.lengthen {N : Subgroup X} {h h' : ℕ} (s : NSeries X N h) (hh : h ≤ h') : NSeries X N h' where
  G i := s.G (min i (2 * h + 1))
  normal i := s.normal _
  mono i hi := by
    by_cases hi' : i < 2 * h + 1
    · rw [min_eq_left hi'.le, min_eq_left (Nat.succ_le_of_lt hi')]; exact s.mono i hi'
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
  zero := by simp [s.zero]
  top := by rw [min_eq_right (by omega)]; exact s.top
  sol i hi := by
    by_cases hi' : i ≤ h
    · rw [min_eq_left (by omega), min_eq_left (by omega)]; exact s.sol i hi'
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
      haveI := s.normal (2 * h + 1)
      exact solubleFactor_self _
  semisimple i hi := by
    by_cases hi' : i < h
    · rw [min_eq_left (by omega), min_eq_left (by omega)]; exact s.semisimple i hi'
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
      exact semisimpleFactor_self _

lemma NonsolubleLengthLE.mono {h h' : ℕ} (hh : h ≤ h') (H : NonsolubleLengthLE X h) :
    NonsolubleLengthLE X h' :=
  let ⟨s⟩ := H; ⟨NSeries.lengthen s hh⟩

/-- Given a series from `K_B` and a series from `K_A` (both to `X`), the series
`K_A ∩ K_B ≤ K_A ∩ G^B_1 ≤ ⋯ ≤ K_A ≤ G^A_1 ≤ ⋯ ≤ X`. -/
def NSeries.interConcat {KA KB : Subgroup X} [hKA : KA.Normal] {a b : ℕ} (sB : NSeries X KB b)
    (sA : NSeries X KA a) : NSeries X (KA ⊓ KB) (b + a) := by
  let G' : ℕ → Subgroup X := fun i => if i ≤ 2 * b then KA ⊓ sB.G i else sA.G (i - 2 * b)
  have hlo : ∀ i, i ≤ 2 * b → G' i = KA ⊓ sB.G i := fun i hi => if_pos hi
  have hhi : ∀ i, 2 * b < i → G' i = sA.G (i - 2 * b) := fun i hi => if_neg (by omega)
  have hnormal : ∀ i, (G' i).Normal := by
    intro i
    by_cases hi : i ≤ 2 * b
    · rw [hlo i hi]; haveI := sB.normal i; infer_instance
    · rw [hhi i (by omega)]; exact sA.normal _
  exact
  { G := G'
    normal := hnormal
    mono := fun i hi => by
      by_cases h1 : i < 2 * b
      · rw [hlo i h1.le, hlo (i + 1) h1]; exact inf_le_inf_left _ (sB.mono i (by omega))
      · by_cases h2 : i = 2 * b
        · subst h2
          rw [hlo _ le_rfl, hhi _ (by omega), show 2 * b + 1 - 2 * b = 0 + 1 by omega]
          have := sA.mono 0 (by omega)
          rw [sA.zero] at this
          exact inf_le_left.trans this
        · rw [hhi i (by omega), hhi (i + 1) (by omega), show i + 1 - 2 * b = i - 2 * b + 1 by omega]
          exact sA.mono _ (by omega)
    zero := by rw [hlo 0 (Nat.zero_le _), sB.zero]
    top := by
      rw [hhi _ (by omega), show 2 * (b + a) + 1 - 2 * b = 2 * a + 1 by omega]; exact sA.top
    sol := fun i hi => by
      by_cases h1 : i < b
      · rw [hlo _ (by omega), hlo _ (by omega)]
        haveI := sB.normal (2 * i)
        exact solubleFactor_inf KA (sB.sol i h1.le)
      · by_cases h2 : i = b
        · subst h2
          rw [hlo _ le_rfl, hhi _ (by omega), show 2 * i + 1 - 2 * i = 1 by omega]
          haveI := sB.normal (2 * i)
          haveI := sA.normal 0
          obtain ⟨k, hk⟩ := solubleFactor_iff.1 (sA.sol 0 (Nat.zero_le _))
          obtain ⟨j, hj⟩ := solubleFactor_iff.1 (sB.sol i le_rfl)
          rw [sB.top] at hj
          refine solubleFactor_iff.2 ⟨j + k, ?_⟩
          rw [dA_add]
          refine (dA_mono j (hk.trans sA.zero.le)).trans (le_inf (dA_le j KA) ?_)
          exact (dA_mono j le_top).trans hj
        · rw [hhi _ (by omega), hhi _ (by omega), show 2 * i - 2 * b = 2 * (i - b) by omega,
            show 2 * i + 1 - 2 * b = 2 * (i - b) + 1 by omega]
          exact sA.sol _ (by omega)
    semisimple := fun i hi => by
      by_cases h1 : i < b
      · rw [hlo _ (by omega), hlo _ (by omega)]
        haveI := sB.normal (2 * i + 1)
        exact semisimpleFactor_inf KA (sB.semisimple i h1)
      · rw [hhi _ (by omega), hhi _ (by omega), show 2 * i + 1 - 2 * b = 2 * (i - b) + 1 by omega,
          show 2 * i + 2 - 2 * b = 2 * (i - b) + 2 by omega]
        exact sA.semisimple _ (by omega) }

end Factors

end CFSGOutside.KhukhroShumyatskyFactorizedLength
