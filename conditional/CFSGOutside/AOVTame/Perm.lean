import CFSGOutside.AOVTame.Factors
import CFSGOutside.AOVTame.Bmap

/-!
# AOV tameness: fusion-preserving automorphisms permute the minimal factors (AOV Prop. 3.5)

For `α ∈ Aut_typ^I(L^c_T(G))`, the induced `β ∈ Aut(T, F)` sends direct decompositions of `T` to
direct decompositions, hence minimal factors to minimal factors.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G}
  {α : LAut 2 (T : Subgroup G)} (hα : α ∈ autTypI 2 (T : Subgroup G))

attribute [local instance] Nat.fact_prime_two

lemma bmap_beta_inv {X : Subgroup G} (hXT : X ≤ T) :
    bmap (beta (inv_mem hα)) (bmap (beta hα) X) = X := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzT, rfl⟩ := (mem_bmap_beta (inv_mem hα)).1 hy
    obtain ⟨x, hx, hxT, rfl⟩ := (mem_bmap_beta hα).1 hz
    have := betaFun_inv_aut hα ⟨x, hxT⟩
    have e : betaG (inv_mem hα) (betaG hα x hxT) hzT = x := congrArg Subtype.val this
    rw [e]; exact hx
  · intro hy
    refine (mem_bmap_beta (inv_mem hα)).2 ⟨betaG hα y (hXT hy), (mem_bmap_beta hα).2
      ⟨y, hy, hXT hy, rfl⟩, betaG_mem _ _ _, ?_⟩
    have := betaFun_inv_aut hα ⟨y, hXT hy⟩
    exact (congrArg Subtype.val this).symm

variable [AlperinFusion]
include hα

/-- `β` maps decompositions to decompositions. -/
lemma Decomp.image {X Y : Subgroup G} (h : Decomp T X Y) :
    Decomp T (bmap (beta hα) X) (bmap (beta hα) Y) where
  leX := bmap_le _ X
  leY := bmap_le _ Y
  inf := by
    rw [← bmap_inf, h.inf, eq_bot_iff]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx1 : x = 1 := Subtype.ext hx
    rw [mem_bot]
    change ((beta hα) x : G) = 1
    rw [hx1, map_one]; rfl
  comm := by
    intro a ha b hb
    obtain ⟨x, hx, hxT, rfl⟩ := (mem_bmap_beta hα).1 ha
    obtain ⟨y, hy, hyT, rfl⟩ := (mem_bmap_beta hα).1 hb
    have e1 := betaFun_mul hα ⟨x, hxT⟩ ⟨y, hyT⟩
    have e2 := betaFun_mul hα ⟨y, hyT⟩ ⟨x, hxT⟩
    have hxy : (⟨x, hxT⟩ : (T : Subgroup G)) * ⟨y, hyT⟩ = ⟨y, hyT⟩ * ⟨x, hxT⟩ :=
      Subtype.ext (h.comm x hx y hy)
    have := congrArg Subtype.val (e1.symm.trans ((congrArg _ hxy).trans e2))
    exact this
  sup := by
    intro t ht
    set z := betaG (inv_mem hα) t ht
    obtain ⟨x, hx, y, hy, e⟩ := h.sup z (betaG_mem _ _ _)
    refine ⟨betaG hα x (h.leX hx), (mem_bmap_beta hα).2 ⟨x, hx, _, rfl⟩,
      betaG hα y (h.leY hy), (mem_bmap_beta hα).2 ⟨y, hy, _, rfl⟩, ?_⟩
    have e1 := betaFun_mul hα ⟨x, h.leX hx⟩ ⟨y, h.leY hy⟩
    have e2 : (⟨x, h.leX hx⟩ : (T : Subgroup G)) * ⟨y, h.leY hy⟩ = ⟨z, betaG_mem _ _ _⟩ :=
      Subtype.ext e.symm
    rw [e2] at e1
    have e3 : betaG hα z (betaG_mem _ _ _) = t := betaG_inv hα t ht
    rw [← e3]
    exact congrArg Subtype.val e1
  scX := beta_stronglyClosed hα h.leX h.scX
  scY := beta_stronglyClosed hα h.leY h.scY

lemma IsFactor.image {X : Subgroup G} (h : IsFactor T X) : IsFactor T (bmap (beta hα) X) :=
  let ⟨_, hY⟩ := h; ⟨_, hY.image hα⟩

lemma bmap_beta_inv' {X : Subgroup G} (hXT : X ≤ T) :
    bmap (beta hα) (bmap (beta (inv_mem hα)) X) = X := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzT, rfl⟩ := (mem_bmap_beta hα).1 hy
    obtain ⟨x, hx, hxT, rfl⟩ := (mem_bmap_beta (inv_mem hα)).1 hz
    rw [betaG_inv hα x hxT]; exact hx
  · intro hy
    exact (mem_bmap_beta hα).2 ⟨betaG (inv_mem hα) y (hXT hy), (mem_bmap_beta (inv_mem hα)).2
      ⟨y, hy, hXT hy, rfl⟩, betaG_mem _ _ _, (betaG_inv hα y (hXT hy)).symm⟩

lemma bmap_bot : bmap (beta hα) ⊥ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx1 : x = 1 := Subtype.ext hx
  rw [mem_bot]
  change ((beta hα) x : G) = 1
  rw [hx1, map_one]; rfl

/-- `β` maps minimal factors to minimal factors. -/
lemma IsMinFactor.image {X : Subgroup G} (h : IsMinFactor T X) :
    IsMinFactor T (bmap (beta hα) X) := by
  obtain ⟨hf, hne, hmin⟩ := h
  have hXT : X ≤ T := let ⟨_, hY⟩ := hf; hY.leX
  refine ⟨hf.image hα, fun he => hne ?_, fun X' hX' hle => ?_⟩
  · have := bmap_beta_inv hα hXT
    rw [he] at this
    rw [← this]; exact bmap_bot (inv_mem hα)
  · have hX'T : X' ≤ T := let ⟨_, hY⟩ := hX'; hY.leX
    have h1 := hX'.image (inv_mem hα)
    have h2 : bmap (beta (inv_mem hα)) X' ≤ X := by
      rw [← bmap_beta_inv hα hXT]; exact bmap_mono _ hle
    rcases hmin _ h1 h2 with h3 | h3
    · left
      rw [← bmap_beta_inv' hα hX'T, h3]; exact bmap_bot hα
    · right
      rw [← bmap_beta_inv' hα hX'T, h3]

end AndersenOliverVentura.Tame
