import CFSGOutside.Baddeley.Outer

/-!
# Baddeley, Lemmas 6.1 and 6.2: containments of special pairs

R. W. Baddeley, *Two-arc transitive graphs and twisted wreath products*, J. Algebraic Combin. **2** (1993),
215–237, DOI 10.1023/A:1022447514654.

**Lemma 6.2 (p. 232).** *If `(Γ, G)` is a special pair with a regular nonabelian minimal normal subgroup `M` and a
subgroup `H` such that `(Γ, H)` is also a special pair, then `M` is contained in `H` as a minimal normal subgroup of
`H`.* This is `lemma_6_2`. We prove the stronger `eq_of_isSpecialPair`: every regular nonabelian minimal normal
subgroup of `H` equals `M`. With `H = G` it gives **Lemma 6.1 (p. 229)**, `lemma_6_1`: a special pair has a unique
regular nonabelian minimal normal subgroup.

The graph is `Γ : SimpleGraph V` with `V` finite, and `G` and `H` are subgroups of `Equiv.Perm V` (see
`CFSGOutside.Baddeley.Definitions`).

**Proof.** We follow the paper's case split. Let `M'` be a regular nonabelian minimal normal subgroup of `H`, and
work inside `G`. Minimality of `M'` gives `M' ≤ M C_G(M)` or `M' ∩ M C_G(M) = 1`.
* In the first case, `|C_G(M)| < |M|` (`card_centralizer_lt`, from Glauberman's Z*-theorem; the paper uses its
  §5 and Praeger's results instead) forces `M' ∩ M ≠ 1`. So `M' ≤ M`, and `M' = M` as both are regular.
* The second case is impossible (`card_ne_of_inf_sup_centralizer_eq_bot`, from the Schreier conjecture and
  Feit–Thompson; the paper uses Teague's theorem and the Schreier conjecture).

**Corpus inputs.** These are hypotheses, and the clean build discharges them from the corpus:
* the Schreier conjecture for the catalogue, `[CFSGOutside.Corpus.Schreier]`
  (`CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`), with `hCFSG`, the classification, placing every
  finite simple group in the catalogue;
* the Odd Order Theorem, `[CFSGOutside.Corpus.OddOrder]` (`CFSG.FeitThompson.isSolvable_of_odd_natCard`);
* Glauberman's Z*-theorem, `[CFSGOutside.Corpus.GlaubermanZStar]` (`CFSG.ZStar.glauberman_zStar`).

The paper notes that its proof depends on the classification, through the Schreier conjecture and Teague's result.
-/

namespace CFSGOutside.Baddeley

open Subgroup CFSGOutside.Corpus

section Transfer

variable {P V : Type*} [Group P] [MulAction P V] {G : Subgroup P}

theorem isMinimalNormalIn_subgroupOf {N K : Subgroup P} (h : IsMinimalNormalIn N K) (hKG : K ≤ G) :
    IsMinimalNormalIn (N.subgroupOf G) (K.subgroupOf G) := by
  obtain ⟨hNK, hKn, hN1, hmin⟩ := h
  have hNG := hNK.trans hKG
  refine ⟨fun x hx => hNK hx, fun g hg => ?_, ?_, fun L hL hKL => ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    exact mem_normalizer_iff.1 (hKn hg) x
  · intro h0
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNG hx⟩ : G) ∈ N.subgroupOf G := hx
    rw [h0, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · have hLN : L.map G.subtype ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hL hy
    have hKL' : K ≤ normalizer ((L.map G.subtype : Subgroup P) : Set P) := by
      intro k hk
      have hk' : (⟨k, hKG hk⟩ : G) ∈ K.subgroupOf G := hk
      rw [mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, (mem_normalizer_iff.1 (hKL hk') y).1 hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hzx' : (z : P) = k * x * k⁻¹ := hzx
        have hxG : x ∈ G := by
          have : x = k⁻¹ * (z : P) * k := by rw [hzx']; group
          rw [this]
          exact mul_mem (mul_mem (inv_mem (hKG hk)) z.2) (hKG hk)
        refine ⟨⟨x, hxG⟩, (mem_normalizer_iff.1 (hKL hk') ⟨x, hxG⟩).2 ?_, rfl⟩
        have : (⟨k, hKG hk⟩ : G) * ⟨x, hxG⟩ * (⟨k, hKG hk⟩ : G)⁻¹ = z := Subtype.ext hzx'.symm
        rw [this]
        exact hz
    rcases hmin _ hLN hKL' with h | h
    · left
      exact (map_eq_bot_iff_of_injective _ G.subtype_injective).1 h
    · right
      rw [← h]
      exact (comap_map_eq_self_of_injective G.subtype_injective L).symm

theorem isRegular_subgroupOf {N : Subgroup P} (h : IsRegular V N) (hNG : N ≤ G) :
    IsRegular V (N.subgroupOf G) :=
  ⟨fun v w => by
    obtain ⟨m, hm, hmv⟩ := h.1 v w
    exact ⟨⟨m, hNG hm⟩, hm, hmv⟩,
   fun m hm v hv => Subtype.ext (h.2 m hm v hv)⟩

theorem isNonabelian_subgroupOf {N : Subgroup P} (h : IsNonabelian N) (hNG : N ≤ G) :
    IsNonabelian (N.subgroupOf G) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨⟨a, hNG ha⟩, ha, ⟨b, hNG hb⟩, hb, fun h => hab (congrArg Subtype.val h)⟩

variable {Γ : SimpleGraph V}

theorem isAutGroup_top (h : IsAutGroup Γ G) : IsAutGroup Γ (⊤ : Subgroup G) :=
  fun g _ => h g g.2

theorem isTwoArcTransitive_top (h : IsTwoArcTransitive Γ G) :
    IsTwoArcTransitive Γ (⊤ : Subgroup G) := by
  intro a₀ a₁ a₂ b₀ b₁ b₂ h1 h2 h3 h4 h5 h6
  obtain ⟨g, hg, e0, e1, e2⟩ := h a₀ a₁ a₂ b₀ b₁ b₂ h1 h2 h3 h4 h5 h6
  exact ⟨⟨g, hg⟩, trivial, e0, e1, e2⟩

end Transfer

variable {V : Type} [Finite V] {Γ : SimpleGraph V}

/-- **Lemma 6.2, strong form.** If `(Γ, G)` is a special pair with a regular nonabelian minimal normal subgroup `M`
and `H ≤ G`, then every regular nonabelian minimal normal subgroup of `H` equals `M`. -/
theorem eq_of_isSpecialPair [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G H M M' : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M)
    (hMreg : IsRegular V M) (hHG : H ≤ G) (hM' : IsMinimalNormalIn M' H) (hM'na : IsNonabelian M')
    (hM'reg : IsRegular V M') : M' = M := by
  obtain ⟨⟨hAut, hconn, h2⟩, -⟩ := hG
  have hMG := hM.1
  have hM'G := hM'.1.trans hHG
  have hM₀ : IsMinimalNormalIn (M.subgroupOf G) ⊤ := by
    have := isMinimalNormalIn_subgroupOf hM le_rfl
    rwa [subgroupOf_self] at this
  have hM₀na := isNonabelian_subgroupOf hMna hMG
  have hM₀reg := isRegular_subgroupOf hMreg hMG
  have hM'₀ := isMinimalNormalIn_subgroupOf hM' hHG
  have hM'₀na := isNonabelian_subgroupOf hM'na hM'G
  have hM'₀reg := isRegular_subgroupOf hM'reg hM'G
  obtain ⟨v₀⟩ := hconn.nonempty
  have hcard : Nat.card (M'.subgroupOf G) = Nat.card (M.subgroupOf G) := by
    rw [card_eq_card_of_isRegular hM'₀reg v₀, card_eq_card_of_isRegular hM₀reg v₀]
  have hClt := card_centralizer_lt (isAutGroup_top hAut) hconn (isTwoArcTransitive_top h2) hM₀ hM₀na
    hM₀reg
  haveI hM₀n : (M.subgroupOf G).Normal := normal_of_top_le hM₀.2.1
  set M₀ := M.subgroupOf G
  set M'₀ := M'.subgroupOf G
  set C₀ := centralizer (M₀ : Set G)
  have hM'₀M₀ : M'₀ = M₀ := by
    rcases hM'₀.2.2.2 (M'₀ ⊓ (M₀ ⊔ C₀)) inf_le_left (le_normalizer_inf hM'₀.2.1 inferInstance)
      with h | h
    · exact absurd hcard (card_ne_of_inf_sup_centralizer_eq_bot hCFSG hM₀ hM₀na hM'₀ hM'₀na h)
    · have hle : M'₀ ≤ M₀ ⊔ C₀ := by rw [← h]; exact inf_le_right
      rcases hM'₀.2.2.2 (M'₀ ⊓ M₀) inf_le_left (le_normalizer_inf hM'₀.2.1 hM₀n) with h' | h'
      · exfalso
        have e1 := relIndex_mul_card M₀ M'₀
        rw [inf_comm, h', card_bot, mul_one] at e1
        have e2 := relIndex_mul_card M₀ C₀
        have e3 : M₀.relIndex (C₀ ⊔ M₀) = M₀.relIndex C₀ := relIndex_sup_right C₀ M₀
        have hpos : 0 < Nat.card (M₀ ⊓ C₀ : Subgroup G) := Nat.card_pos
        have hC0 : 0 < Nat.card C₀ := Nat.card_pos
        have e4 : M₀.relIndex C₀ ≤ Nat.card C₀ := by
          rw [← e2]
          exact Nat.le_mul_of_pos_right _ hpos
        have e5 : M₀.relIndex M'₀ ≤ M₀.relIndex (C₀ ⊔ M₀) := by
          refine relIndex_le_of_le_right (by rwa [sup_comm]) ?_
          rw [e3]
          intro h0
          rw [h0, zero_mul] at e2
          omega
        omega
      · have hle' : M'₀ ≤ M₀ := by rw [← h']; exact inf_le_right
        exact eq_of_le_of_card_ge hle' hcard.ge
  have := subgroupOf_inj.1 hM'₀M₀
  rwa [inf_eq_left.2 hM'G, inf_eq_left.2 hMG] at this

/-- **2-arc-transitive graphs.** Let Γ be a finite simple graph, and call a group G of automorphisms of Γ special if Γ
is connected, G is transitive on 2-arcs, and G has a nonabelian minimal normal subgroup that is regular on the
vertices. If G is special, it has exactly one such subgroup M, and if H ≤ G is also special then M ≤ H and M is a
minimal normal subgroup of H.

Source: R. W. Baddeley, Two-arc transitive graphs and twisted wreath products, J. Algebraic Combin. 2 (1993),
215–237, Lemmas 6.1 and 6.2. https://doi.org/10.1023/A:1022447514654

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem lemma_6_2 [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G H M : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M)
    (hMreg : IsRegular V M) (hHG : H ≤ G) (hH : IsSpecialPair Γ H) :
    M ≤ H ∧ IsMinimalNormalIn M H := by
  obtain ⟨-, M', hM', hM'na, hM'reg⟩ := hH
  obtain rfl := eq_of_isSpecialPair hCFSG hG hM hMna hMreg hHG hM' hM'na hM'reg
  exact ⟨hM'.1, hM'⟩

/-- **Lemma 6.1** (Baddeley 1993, p. 229). If `(Γ, G)` is a special pair, then `G` has a unique regular, nonabelian,
minimal normal subgroup. -/
theorem lemma_6_1 [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) :
    ∃! M : Subgroup (Equiv.Perm V), IsMinimalNormalIn M G ∧ IsNonabelian M ∧ IsRegular V M := by
  obtain ⟨M, hM, hMna, hMreg⟩ := hG.2
  exact ⟨M, ⟨hM, hMna, hMreg⟩, fun M' ⟨hM', hM'na, hM'reg⟩ =>
    eq_of_isSpecialPair hCFSG hG hM hMna hMreg le_rfl hM' hM'na hM'reg⟩

end CFSGOutside.Baddeley
