import CFSGOutside.AOVTame.AutI
import CFSGOutside.AOVTame.SatGroup
import CFSGOutside.Corpus.AlperinFusion
import CFSGOutside.Corpus.Defs.GoldschmidtOddCore

/-!
# AOV tameness: `β(α)` is fusion preserving (AOV Lemma 1.15, `β ∈ Aut(S, F)`)

For `α ∈ Aut_typ^I(L^c_T(G))`, the automorphism `β` of `T` is fusion preserving on all subgroups,
not only on centric ones. As in the paper this uses Alperin's fusion theorem (here the corpus
statement `CFSG.RankTwoShapes.alperin_centric_radical_fusion`, as the class `AlperinFusion`):
every conjugation in `T` is a product of conjugations in normalizers of centric subgroups.
Consequently `β` preserves strong closure.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

universe u

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}

/-- An Alperin subgroup is centric. -/
lemma isCentric_of_isAlperin {Q : Subgroup G} (hQ : IsAlperinSubgroup p (T : Subgroup G) Q) :
    IsCentric (T : Subgroup G) Q := by
  obtain ⟨hQT, hidx, hcen, -⟩ := hQ
  have hN : IsSylowIn p (normalizer (Q : Set G) ⊓ T) (normalizer (Q : Set G)) := by
    refine ⟨inf_le_left, T.isPGroup'.to_le inf_le_right, fun h => ?_⟩
    rw [inf_comm] at h
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).1 hidx h
  have hC := isSylowIn_centralizer_of_normalizer T hN
  refine ⟨hQT, fun g hg => le_antisymm ?_ ?_⟩
  · -- `C_T(gQg⁻¹) = Z(gQg⁻¹)` by counting
    have hZ : centralizer (Q : Set G) ⊓ T = Q ⊓ centralizer (Q : Set G) :=
      le_antisymm (le_inf hcen inf_le_left) (le_inf inf_le_right (inf_le_left.trans hQT))
    have h1 := card_centralizer_le_of_isSylowIn T hC g
    rw [hZ] at h1
    have h2 : conjSub g Q ⊓ centralizer (conjSub g Q : Set G) ≤
        centralizer (conjSub g Q : Set G) ⊓ T := le_inf inf_le_right (inf_le_left.trans hg)
    have h3 : Nat.card (conjSub g Q ⊓ centralizer (conjSub g Q : Set G) : Subgroup G) =
        Nat.card (Q ⊓ centralizer (Q : Set G) : Subgroup G) := by
      rw [← conjSub_centralizer, ← conjSub_inf, card_conjSub]
    have := Subgroup.eq_of_le_of_card_ge h2 (h1.trans h3.ge)
    rw [← this]
  · exact le_inf inf_le_right (inf_le_left.trans hg)

/-- `β` as a function on `T`. -/
noncomputable def betaG {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (x : G) (hx : x ∈ (T : Subgroup G)) : G :=
  (betaFun hα ⟨x, hx⟩ : G)

lemma betaG_mem {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (x : G) (hx : x ∈ (T : Subgroup G)) : betaG hα x hx ∈ (T : Subgroup G) := (betaFun hα _).2

section
variable {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))

/-- `β` commutes with conjugation in the normalizer of a centric subgroup. -/
lemma beta_conj_centric {Q : Subgroup G} (hQ : IsCentric (T : Subgroup G) Q) {n : G}
    (hn : n ∈ normalizer (Q : Set G)) :
    ∃ k : G, ∀ y (hy : y ∈ Q), betaG hα (n⁻¹ * y * n) (hQ.1 ((mem_normalizer_iff.1 (inv_mem hn) y).1 hy |>
      fun h => by simpa using h)) = k * betaG hα y (hQ.1 hy) * k⁻¹ := by
  have hni : n⁻¹ ∈ transporter Q Q := fun y hy => (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
  obtain ⟨h, hh, -, hrel⟩ := map_mk_conj hα (P := ⟨Q, hQ⟩) (Q := ⟨Q, hQ⟩) hni
  refine ⟨h, fun y hy => ?_⟩
  have := hrel y hy
  simp only [inv_inv] at this
  exact this.symm

/-- **`β` is fusion preserving.** -/
theorem beta_fusion [AlperinFusion] {P : Subgroup G} (hP : P ≤ T) {g : G}
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ T) :
    ∃ h : G, ∀ x (hx : x ∈ P) (hx' : g⁻¹ * x * g ∈ (T : Subgroup G)),
      betaG hα (g⁻¹ * x * g) hx' = h⁻¹ * betaG hα x (hP hx) * h := by
  obtain ⟨c, hc, hcg⟩ := AlperinFusion.alperin_centric_radical_fusion T hP hg
  suffices H : ∀ c : G, AlperinDecomposition p (T : Subgroup G) P c →
      ∃ h : G, ∀ x (hx : x ∈ P) (hx' : c⁻¹ * x * c ∈ (T : Subgroup G)),
        betaG hα (c⁻¹ * x * c) hx' = h⁻¹ * betaG hα x (hP hx) * h by
    obtain ⟨h, hh⟩ := H c hc
    refine ⟨h, fun x hx hx' => ?_⟩
    have e := hcg x hx
    have hx'' : c⁻¹ * x * c ∈ (T : Subgroup G) := by rw [e]; exact hx'
    have := hh x hx hx''
    simp only [betaG] at this ⊢
    rw [← this]
    congr 2
    exact Subtype.ext e.symm
  intro c hc
  induction hc with
  | one => exact ⟨1, fun x hx hx' => by simp [betaG]⟩
  | @step c n Q hc hQ hPQ hn ih =>
    obtain ⟨h, hh⟩ := ih
    have hQc := isCentric_of_isAlperin hQ
    obtain ⟨k, hk⟩ := beta_conj_centric hα hQc hn
    refine ⟨h * k⁻¹, fun x hx hx' => ?_⟩
    have hy : c⁻¹ * x * c ∈ Q := hPQ ⟨x, hx, by simp [mul_assoc]⟩
    have e1 : (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
    have := hk (c⁻¹ * x * c) hy
    have h2 := hh x hx (hQc.1 hy)
    simp only [betaG] at this h2 ⊢
    have e2 : (⟨(c * n)⁻¹ * x * (c * n), hx'⟩ : (T : Subgroup G)) =
        ⟨n⁻¹ * (c⁻¹ * x * c) * n, by rw [← e1]; exact hx'⟩ := Subtype.ext e1
    rw [e2, this, h2]
    group

lemma mem_bmap_beta {X : Subgroup G} {y : G} :
    y ∈ bmap (beta hα) X ↔ ∃ x ∈ X, ∃ hx : x ∈ (T : Subgroup G), y = betaG hα x hx := by
  constructor
  · rintro ⟨_, ⟨⟨x, hxT⟩, hxX, rfl⟩, rfl⟩
    exact ⟨x, hxX, hxT, rfl⟩
  · rintro ⟨x, hxX, hxT, rfl⟩
    exact ⟨_, ⟨⟨x, hxT⟩, hxX, rfl⟩, rfl⟩

lemma betaG_inv (x : G) (hx : x ∈ (T : Subgroup G)) :
    betaG hα (betaG (inv_mem hα) x hx) (betaG_mem _ x hx) = x := by
  have := betaFun_inv_aut' hα ⟨x, hx⟩
  exact congrArg Subtype.val this

/-- `β` preserves strong closure. -/
theorem beta_stronglyClosed [AlperinFusion] {X : Subgroup G} (hXT : X ≤ T)
    (hX : fusionStronglyClosed (X : Set G) T) :
    fusionStronglyClosed (bmap (beta hα) X : Set G) T := by
  intro y hy g hg
  obtain ⟨x, hxX, hxT, rfl⟩ := (mem_bmap_beta hα).1 hy
  set y := betaG hα x hxT with hy_def
  have hyT : y ∈ (T : Subgroup G) := betaG_mem hα x hxT
  have hP : zpowers y ≤ T := (zpowers_le).2 hyT
  have hPg : (zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have : (MulAut.conj g⁻¹) (y ^ k) = (g⁻¹ * y * g) ^ k := by
      have := map_zpow (MulAut.conj g⁻¹) y k
      simpa [MulAut.conj_apply] using this
    change (MulAut.conj g⁻¹) (y ^ k) ∈ (T : Subgroup G)
    rw [this]; exact zpow_mem hg k
  obtain ⟨h, hh⟩ := beta_fusion (inv_mem hα) hP hPg
  have e := hh y (mem_zpowers y) hg
  have hyx : betaG (inv_mem hα) y hyT = x := by
    have := betaFun_inv_aut hα ⟨x, hxT⟩
    exact congrArg Subtype.val this
  rw [hyx] at e
  have hz : betaG (inv_mem hα) (g⁻¹ * y * g) hg ∈ X := by
    rw [e]
    apply hX x hxX h
    rw [← e]; exact betaG_mem _ _ _
  exact (mem_bmap_beta hα).2 ⟨_, hz, betaG_mem _ _ _, (betaG_inv hα _ hg).symm⟩

end

end AndersenOliverVentura.Tame
