
import CFSGOutside.Corpus.Schreier
import CFSGOutside.Robinson.Definitions
import CFSGOutside.Robinson.OuterAction

/-!
# Robinson: finite groups with simple (non-abelian) chief factors

**Paper.** D. J. S. Robinson, *The structure of finite groups in which permutability is a
transitive relation*, J. Austral. Math. Soc. **70** (2001), 143–159,
DOI 10.1017/S1446788700002573.

**Definitions (§2).** A group is an *SC-group* if all its chief factors are simple, and an
*SNAC-group* if its non-abelian chief factors are simple.

**Proposition 2.3.** A group `G` is SNAC if and only if it has normal subgroups `S` and `D` such
that `S` and `G/D` are soluble while `D/S` is a direct product of `G`-invariant simple groups.

**Proposition 2.4.** A group `G` is an SC-group if and only if there is a perfect normal subgroup
`D` such that `G/D` is supersoluble, `D/Z(D)` is a direct product of `G`-invariant simple groups,
and `Z(D)` is supersolubly embedded in `G` (that is, there is a `G`-admissible series in `Z(D)` with
cyclic factors).

**Lemma 2.6(i).** Let `G` be an SC-group, `D = G^(∞)` and `R = D/Z(D)`. Then `C_G(D) = C_G(R)` is
the soluble radical of `G` (`lemma_2_6_i`).  **(ii)** `DS/D` is the kernel of the coupling
`χ : G/D → Out(D)` (`lemma_2_6_ii`, with `coupling`, `ker_coupling`).

**Corollary 2.5.** An SC-group is an extension of a perfect T-group by a supersoluble group:
`G^(∞)` is a perfect T-group and `G/G^(∞)` is supersoluble (`corollary_2_5`; `IsTGroup`).

The "⇒" directions of 2.3 and 2.4 are also stated with the paper's witness `D = G^(∞)`
(`proposition_2_3_derivedLimit`, `proposition_2_4_derivedLimit`).

All groups are finite.  The only input from the classification is the Schreier conjecture
(`Out(T)` is soluble for every non-abelian finite simple `T`), taken from the corpus
(`CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds`, assumed as the class
`CFSGOutside.Corpus.Schreier`) under the hypothesis `hCFSG : TauCeti.ClassificationStatement.{0}`,
and used through `CFSGOutside.Robinson.perfect_action_inner`: a perfect group acting on such a `T`
acts by inner automorphisms.  It enters only the direction "SNAC ⇒ structure" of Proposition 2.3 and the
direction "SC ⇒ structure" of Proposition 2.4, exactly as in the paper.

**Conventions.**
* A chief factor is a pair `K < H` of normal subgroups of `G` with no normal subgroup of `G`
  strictly between them (`IsChiefFactor H K`).  The factor group `H/K` is realised as the subgroup
  `factor H K = H.map (mk' K)` of `G ⧸ K` (canonically isomorphic to `H ⧸ K.subgroupOf H`,
  `factorEquiv`).
* "`D/S` is a direct product of `G`-invariant simple groups" (`IsDirectProductOfInvariantSimple`)
  means: the subgroup `D/S = D.map (mk' S)` of `G ⧸ S` is the supremum of a finite family of
  normal subgroups of `G ⧸ S` (i.e. `G`-invariant), each a simple group, which is independent
  (`sSupIndep`); such a family is an internal direct product (`mulEquivPi`).
* A cyclic factor `H/K` (with `K ≤ H`) is expressed as `H = K ⊔ ⟨g⟩` (`CyclicFactor`, see
  `cyclicFactor_iff_isCyclic`).  `A` is supersolubly embedded in `G` if there is a series
  `1 = A₀ ≤ A₁ ≤ ⋯ ≤ Aₙ = A` of normal subgroups of `G` with cyclic factors, and `G` is
  supersoluble if `⊤` is supersolubly embedded in `G`.
* `Z(D)` is `centerIn D = D ⊓ centralizer D`, the centre of `D` as a subgroup of `G`
  (`centerIn_eq_map_center`).
-/

section

namespace CFSGOutside.Robinson

open Subgroup QuotientGroup

section Basic

variable {G : Type*} [Group G]

lemma centerIn_eq_map_center (D : Subgroup G) : centerIn D = (center D).map D.subtype := by
  ext x
  rw [mem_centerIn]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2)
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hy
    exact ⟨y.2, fun z hz => congrArg Subtype.val (hy ⟨z, hz⟩)⟩

lemma centerIn_le (D : Subgroup G) : centerIn D ≤ D := inf_le_left

lemma factorEquiv_aux (H K : Subgroup G) [K.Normal] :
    ((QuotientGroup.mk' K).comp H.subtype).range = factor H K := by
  rw [MonoidHom.range_comp, range_subtype]

/-- The subgroup `factor H K` of `G ⧸ K` is the factor group `H ⧸ K`. -/
noncomputable def factorEquiv (H K : Subgroup G) [K.Normal] :
    (H ⧸ K.subgroupOf H) ≃* factor H K := by
  have hker : ((QuotientGroup.mk' K).comp H.subtype).ker = K.subgroupOf H := by
    ext x
    simp [mem_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr (factorEquiv_aux H K)))

lemma mem_factor {H K : Subgroup G} [K.Normal] {y : G ⧸ K} :
    y ∈ factor H K ↔ ∃ h ∈ H, (h : G ⧸ K) = y := by
  simp [factor]

lemma comap_factor {H K : Subgroup G} [K.Normal] (hKH : K ≤ H) :
    (factor H K).comap (QuotientGroup.mk' K) = H := by
  rw [factor, comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr hKH

lemma mem_of_mk_mem_factor {H K : Subgroup G} [K.Normal] (hKH : K ≤ H) {g : G}
    (hg : (g : G ⧸ K) ∈ factor H K) : g ∈ H := by
  rw [← comap_factor hKH]
  exact hg

lemma factor_normal {H K : Subgroup G} [K.Normal] [hH : H.Normal] : (factor H K).Normal :=
  hH.map _ (QuotientGroup.mk'_surjective K)

lemma nonabelian_iff {H K : Subgroup G} [K.Normal] :
    (∃ a b : factor H K, a * b ≠ b * a) ↔ ¬ ⁅H, H⁆ ≤ K := by
  constructor
  · rintro ⟨a, b, hab⟩ hle
    apply hab
    obtain ⟨x, hx, hxa⟩ := mem_factor.mp a.2
    obtain ⟨y, hy, hyb⟩ := mem_factor.mp b.2
    have hc : x * y * x⁻¹ * y⁻¹ ∈ K := hle (commutator_mem_commutator hx hy)
    apply Subtype.ext
    rw [coe_mul, coe_mul, ← hxa, ← hyb]
    have h1 : ((x * y * x⁻¹ * y⁻¹ : G) : G ⧸ K) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    calc (x : G ⧸ K) * y = ((x : G ⧸ K) * y * (x : G ⧸ K)⁻¹ * (y : G ⧸ K)⁻¹) * y * x := by group
      _ = y * x := by rw [h1, one_mul]
  · intro h
    by_contra hc
    push Not at hc
    apply h
    rw [commutator_le]
    intro x hx y hy
    have := hc ⟨(x : G ⧸ K), mem_factor.mpr ⟨x, hx, rfl⟩⟩ ⟨(y : G ⧸ K), mem_factor.mpr ⟨y, hy, rfl⟩⟩
    have h' : (x : G ⧸ K) * (y : G ⧸ K) = (y : G ⧸ K) * (x : G ⧸ K) :=
      congrArg Subtype.val this
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h']
    group

lemma commutator_eq_bot_of_comm {A : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ⁅A, A⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact h b hb a ha

/-- A perfect soluble subgroup is trivial. -/
lemma eq_bot_of_perfect_of_solvable {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hs : Group.IsSolvable P) :
    P = ⊥ := by
  have htop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = (⊤ : Subgroup P) := by
    apply map_injective P.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hP]
  have hd : ∀ n, derivedSeries P n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, htop]
  obtain ⟨n, hn⟩ := (isSolvable_def P).mp hs
  rw [hd n] at hn
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : P) ∈ derivedSeries P n := by rw [hd n]; exact mem_top _
  rw [hd n, hn] at this
  simpa using congrArg Subtype.val (mem_bot.mp this)

lemma isPerfect_of_commutator_eq {D : Subgroup G} (hD : ⁅D, D⁆ = D) : Group.IsPerfect D := by
  rw [Group.isPerfect_def]
  apply map_injective D.subtype_injective
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hD]

lemma isSolvable_of_le {A B : Subgroup G} (h : A ≤ B) [Group.IsSolvable B] : Group.IsSolvable A :=
  solvable_of_solvable_injective (inclusion_injective h)

lemma isSolvable_map {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) [Group.IsSolvable A] :
    Group.IsSolvable (A.map f) :=
  solvable_of_surjective (f.subgroupMap_surjective A)

lemma isSolvable_comap {S : Subgroup G} [S.Normal] (hS : Group.IsSolvable S) (A : Subgroup (G ⧸ S))
    (hA : Group.IsSolvable A) : Group.IsSolvable (A.comap (QuotientGroup.mk' S)) := by
  have hSA : S ≤ A.comap (QuotientGroup.mk' S) := by
    intro s hs
    simp [(QuotientGroup.eq_one_iff s).mpr hs]
  let g : A.comap (QuotientGroup.mk' S) →* A :=
    ((QuotientGroup.mk' S).comp (A.comap (QuotientGroup.mk' S)).subtype).codRestrict A
      (fun x => x.2)
  refine solvable_of_ker_le_range (inclusion hSA) g ?_
  intro x hx
  have hx' : (x : G) ∈ S := by
    have : g x = 1 := hx
    have h2 := congrArg Subtype.val this
    exact (QuotientGroup.eq_one_iff _).mp h2
  exact ⟨⟨x, hx'⟩, rfl⟩

/-- Normal subgroups between `K` and `H`, for a chief factor: dichotomy. -/
lemma IsChiefFactor.eq_or_eq {H K : Subgroup G} (hc : IsChiefFactor H K) {L : Subgroup G}
    (hL : L.Normal) (hKL : K ≤ L) (hLH : L ≤ H) : L = K ∨ L = H := hc.2.2.2 L hL hKL hLH

lemma IsChiefFactor.factor_ne_bot {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K) :
    factor H K ≠ ⊥ := by
  intro h
  apply hc.2.2.1.not_ge
  intro x hx
  have : (x : G ⧸ K) ∈ factor H K := mem_factor.mpr ⟨x, hx, rfl⟩
  rw [h, mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp this

/-- A soluble chief factor is abelian. -/
lemma commutator_le_of_solvable_factor {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K)
    (hF : Group.IsSolvable (factor H K)) : ⁅H, H⁆ ≤ K := by
  haveI := hc.1
  have hP : (⁅H, H⁆ ⊔ K).Normal := inferInstance
  rcases hc.eq_or_eq hP le_sup_right (sup_le (commutator_le_left H H) hc.2.2.1.le) with h | h
  · exact h ▸ le_sup_left
  · exfalso
    apply hc.factor_ne_bot
    apply eq_bot_of_perfect_of_solvable _ hF
    conv_rhs => rw [factor, ← h]
    rw [Subgroup.map_sup, map_commutator]
    have : K.map (QuotientGroup.mk' K) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, sup_bot_eq]

/-- The chief factor correspondence for quotients. -/
lemma IsChiefFactor.comap {N : Subgroup G} [N.Normal] {H K : Subgroup (G ⧸ N)}
    (hc : IsChiefFactor H K) :
    IsChiefFactor (H.comap (QuotientGroup.mk' N)) (K.comap (QuotientGroup.mk' N)) := by
  have hsurj := QuotientGroup.mk'_surjective N
  refine ⟨hc.1.comap _, hc.2.1.comap _, ?_, ?_⟩
  · refine lt_of_le_of_ne (comap_mono hc.2.2.1.le) fun h => hc.2.2.1.ne ?_
    rw [← map_comap_eq_self_of_surjective hsurj K, h, map_comap_eq_self_of_surjective hsurj]
  · intro L hL hKL hLH
    have hNL : N ≤ L := by
      intro n hn
      apply hKL
      simp [(QuotientGroup.eq_one_iff n).mpr hn]
    have hL' : L = (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
      rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNL]
    have h1 : K ≤ L.map (QuotientGroup.mk' N) := by
      rw [← map_comap_eq_self_of_surjective hsurj K]
      exact Subgroup.map_mono hKL
    have h2 : L.map (QuotientGroup.mk' N) ≤ H := by
      rw [← map_comap_eq_self_of_surjective hsurj H]
      exact Subgroup.map_mono hLH
    rcases hc.eq_or_eq (hL.map _ hsurj) h1 h2 with h | h
    · left; rw [hL', h]
    · right; rw [hL', h]

lemma comap_mk_bot (S : Subgroup G) [S.Normal] :
    (⊥ : Subgroup (G ⧸ S)).comap (QuotientGroup.mk' S) = S := by
  ext x
  simp [QuotientGroup.eq_one_iff]

lemma isChiefFactor_bot_comap {S : Subgroup G} [S.Normal] {N : Subgroup (G ⧸ S)}
    (hN : IsChiefFactor N ⊥) : IsChiefFactor (N.comap (QuotientGroup.mk' S)) S := by
  have := hN.comap (N := S)
  rwa [comap_mk_bot] at this

lemma factor_comap {S : Subgroup G} [S.Normal] (N : Subgroup (G ⧸ S)) :
    factor (N.comap (QuotientGroup.mk' S)) S = N :=
  map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S) N

/-- In an SNAC group, a non-abelian minimal normal subgroup of a quotient is simple. -/
lemma simple_of_minimal_normal {S : Subgroup G} [S.Normal] (hG : IsSNAC G)
    {N : Subgroup (G ⧸ S)} (hN : IsChiefFactor N ⊥) (hnab : ∃ a b : N, a * b ≠ b * a) :
    IsSimpleGroup N := by
  have hc := isChiefFactor_bot_comap hN
  have := hG _ _ hc (by rw [factor_comap]; exact hnab)
  rwa [factor_comap] at this

/-- A Q-normal subgroup of a simple normal subgroup `T` is `⊥` or `T`. -/
lemma eq_bot_or_eq_of_le_simple {T M : Subgroup G} [IsSimpleGroup T] (hM : M.Normal)
    (hMT : M ≤ T) : M = ⊥ ∨ M = T := by
  have hn : (M.subgroupOf T).Normal := hM.subgroupOf T
  rcases (haveI := hn; IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf T)) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hMT hx⟩ : T) ∈ M.subgroupOf T := hx
    rw [h] at this
    simpa using congrArg Subtype.val (mem_bot.mp this)
  · right
    refine le_antisymm hMT fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ M.subgroupOf T := h ▸ mem_top _
    exact this

lemma not_comm_of_simple_normal {T : Subgroup G} (hnab : ∃ a b : T, a * b ≠ b * a) :
    ¬ T ≤ centralizer (T : Set G) := by
  intro h
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (h a.2)) b b.2 |>.symm

lemma mem_sup_normal_left {A N : Subgroup G} [N.Normal] {x : G} :
    x ∈ N ⊔ A ↔ ∃ n ∈ N, ∃ a ∈ A, n * a = x := mem_sup_of_normal_left

end Basic

section Independence

variable {Q : Type*} [Group Q]

lemma insert_diff_singleton_self {s : Set (Subgroup Q)} {a : Subgroup Q} (ha : a ∉ s) :
    insert a s \ {a} = s := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxa⟩
    · exact absurd hx hxa
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, fun h => ha (h ▸ hx)⟩

lemma sSupIndep_insert_normal {𝒯 : Set (Subgroup Q)} {N : Subgroup Q} [N.Normal]
    (h𝒯 : sSupIndep 𝒯) (hN : N ∉ 𝒯) (hdisj : Disjoint N (sSup 𝒯)) :
    sSupIndep (insert N 𝒯) := by
  intro a ha
  rcases ha with rfl | ha
  · rwa [insert_diff_singleton_self hN]
  · have hne : a ≠ N := fun h => hN (h ▸ ha)
    have hset : insert N 𝒯 \ {a} = insert N (𝒯 \ {a}) := by
      ext x
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx | hx, hxa⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hx, hxa⟩
      · rintro (hx | ⟨hx, hxa⟩)
        · exact ⟨Or.inl hx, fun h => hne (h.symm.trans hx)⟩
        · exact ⟨Or.inr hx, hxa⟩
    rw [hset, sSup_insert, disjoint_def]
    intro g hga hg
    obtain ⟨n, hn, y, hy, rfl⟩ := mem_sup_normal_left.mp hg
    have hsub : sSup (𝒯 \ {a}) ≤ sSup 𝒯 := sSup_le_sSup Set.diff_subset
    have hy' : y ∈ sSup 𝒯 := hsub hy
    have hga' : n * y ∈ sSup 𝒯 := le_sSup ha hga
    have hn1 : n = 1 := disjoint_def.mp hdisj hn (by simpa using mul_mem hga' (inv_mem hy'))
    subst hn1
    rw [one_mul] at hga ⊢
    exact disjoint_def.mp (h𝒯 ha) hga hy

/-- An independent family of normal subgroups pairwise commutes. -/
lemma commute_of_sSupIndep {𝒯 : Set (Subgroup Q)} (h𝒯n : ∀ T ∈ 𝒯, T.Normal)
    (hind : sSupIndep 𝒯) {T T' : Subgroup Q} (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯) (hne : T ≠ T')
    {x y : Q} (hx : x ∈ T) (hy : y ∈ T') : Commute x y := by
  haveI := h𝒯n T hT
  haveI := h𝒯n T' hT'
  have hd : Disjoint T T' :=
    (hind hT).mono_right
      (le_sSup (show T' ∈ 𝒯 \ {T} from ⟨hT', fun h => hne (Set.mem_singleton_iff.mp h).symm⟩))
  exact commute_of_normal_of_disjoint _ _ inferInstance inferInstance hd x y hx hy

/-- A family as in `IsDirectProductOfInvariantSimple` is an internal direct product. -/
noncomputable def mulEquivPi [Finite Q] {D : Subgroup Q} (𝒯 : Finset (Subgroup Q))
    (h𝒯n : ∀ T ∈ 𝒯, T.Normal) (hind : sSupIndep (𝒯 : Set (Subgroup Q)))
    (hsup : sSup (𝒯 : Set (Subgroup Q)) = D) :
    (∀ T : 𝒯, (T : Subgroup Q)) ≃* D := by
  classical
  let f : 𝒯 → Subgroup Q := fun T => T
  have hcomm : Pairwise fun T T' : 𝒯 => ∀ x y : Q, x ∈ f T → y ∈ f T' → Commute x y := by
    intro T T' hne x y hx hy
    exact commute_of_sSupIndep h𝒯n hind T.2 T'.2 (fun h => hne (Subtype.ext h)) hx hy
  have hind' : iSupIndep f := by
    intro T
    have h := hind T.2
    refine h.mono_right ?_
    apply iSup_le
    intro T'
    apply iSup_le
    intro hne
    apply le_sSup
    exact ⟨T'.2, fun h' => hne (Subtype.ext (Set.mem_singleton_iff.mp h'))⟩
  let φ := noncommPiCoprod hcomm
  have hinj : Function.Injective φ := injective_noncommPiCoprod_of_iSupIndep hind'
  have hrange : φ.range = D := by
    rw [noncommPiCoprod_range, ← hsup, sSup_eq_iSup']
    rfl
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

end Independence

section Schreier

variable {Q : Type} [Group Q] [Finite Q]

/-- **The Schreier step** (the only place the classification is used).  A perfect subgroup `D`
of `Q` normalizing a non-abelian simple normal subgroup `N ≤ D` acts on it by inner
automorphisms, hence `D = N · C_D(N)`. -/
lemma le_sup_centralizer [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {D N : Subgroup Q}
    [hN : N.Normal] [IsSimpleGroup N] (hnab : ∃ a b : N, a * b ≠ b * a) (hperf : ⁅D, D⁆ = D)
    (hND : N ≤ D) : D ≤ N ⊔ (D ⊓ centralizer (N : Set Q)) := by
  have hout : Group.IsSolvable (CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.Outer N) :=
    CFSGOutside.Corpus.Schreier.schreierFor_inCatalog_holds N hnab
      (TauCeti.classificationStatement_iff.1 hCFSG N)
  haveI : Group.IsPerfect D := isPerfect_of_commutator_eq hperf
  intro d hd
  obtain ⟨n, hn⟩ := CFSGOutside.Robinson.perfect_action_inner
    ((MulAut.conjNormal (H := N)).comp D.subtype) ⟨d, hd⟩
  have key : ∀ x ∈ N, d * x * d⁻¹ = (n : Q) * x * (n : Q)⁻¹ := by
    intro x hx
    have := congrArg (fun σ : MulAut N => ((σ ⟨x, hx⟩ : N) : Q)) hn
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
  have hc : (n : Q)⁻¹ * d ∈ D ⊓ centralizer (N : Set Q) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hND n.2)) hd, ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    have := key h hh
    calc h * ((n : Q)⁻¹ * d) = (n : Q)⁻¹ * ((n : Q) * h * (n : Q)⁻¹) * d := by group
      _ = (n : Q)⁻¹ * (d * h * d⁻¹) * d := by rw [this]
      _ = (n : Q)⁻¹ * d * h := by group
  have : d = (n : Q) * ((n : Q)⁻¹ * d) := by group
  rw [this]
  exact mul_mem (mem_sup_left n.2) (mem_sup_right hc)

/-- **Decomposition** (proof of Proposition 2.3, "⇒").  A perfect normal subgroup `D` of `Q`
which contains no non-trivial soluble normal subgroup of `Q`, and all of whose minimal normal
subgroups of `Q` are simple, is a direct product of `Q`-invariant simple groups. -/
theorem isDirectProduct_of_perfect [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) :
    ∀ D : Subgroup Q, D.Normal → ⁅D, D⁆ = D →
      (∀ A : Subgroup Q, A.Normal → A ≤ D → Group.IsSolvable A → A = ⊥) →
      (∀ N : Subgroup Q, IsChiefFactor N ⊥ → N ≤ D → IsSimpleGroup N) →
      IsDirectProductOfInvariantSimple D := by
  intro D
  induction D using WellFoundedLT.induction with
  | _ D ih =>
  intro hDn hperf hsol hmin
  by_cases hD : D = ⊥
  · refine ⟨∅, by simp, ?_, by simp [hD]⟩
    simp [sSupIndep]
  obtain ⟨N, hND, hNmin⟩ := Finite.exists_le_minimal
    (p := fun N : Subgroup Q => N.Normal ∧ N ≠ ⊥) (a := D) ⟨hDn, hD⟩
  haveI hNn : N.Normal := hNmin.1.1
  have hchief : IsChiefFactor N ⊥ := by
    refine ⟨hNn, normal_bot, bot_lt_iff_ne_bot.mpr hNmin.1.2, ?_⟩
    intro L hL _ hLN
    by_cases hL0 : L = ⊥
    · exact Or.inl hL0
    · exact Or.inr (le_antisymm hLN (hNmin.2 ⟨hL, hL0⟩ hLN))
  haveI : IsSimpleGroup N := hmin N hchief hND
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : Group.IsSolvable N := isSolvable_of_comm hc
    exact hNmin.1.2 (hsol N hNn hND inferInstance)
  set C := D ⊓ centralizer (N : Set Q) with hCdef
  haveI hCn : C.Normal := by
    haveI := hDn
    exact normal_inf_normal _ _
  have hDC : D = N ⊔ C := le_antisymm (le_sup_centralizer hCFSG hnab hperf hND)
    (sup_le hND inf_le_left)
  have hNC : N ⊓ C = ⊥ := by
    by_contra hne
    have hle : N ≤ N ⊓ C := hNmin.2 ⟨normal_inf_normal _ _, hne⟩ inf_le_left
    exact not_comm_of_simple_normal hnab (hle.trans (inf_le_right.trans inf_le_right))
  have hCD : C < D := by
    refine lt_of_le_of_ne inf_le_left fun h => hNmin.1.2 ?_
    rw [← inf_eq_left.mpr (hND.trans h.ge), hNC]
  have hCperf : ⁅C, C⁆ = C := by
    refine le_antisymm (commutator_le_left C C) fun c hc => ?_
    have hmapC : C.map (QuotientGroup.mk' N) = D.map (QuotientGroup.mk' N) := by
      rw [hDC, Subgroup.map_sup]
      have : N.map (QuotientGroup.mk' N) = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [this, bot_sup_eq]
    have hmap : (⁅C, C⁆).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
      rw [map_commutator, hmapC, ← map_commutator, hperf]
    have hcm : QuotientGroup.mk' N c ∈ (⁅C, C⁆).map (QuotientGroup.mk' N) :=
      hmap ▸ mem_map_of_mem _ hc
    obtain ⟨x, hx, hxc⟩ := hcm
    have hxN : x⁻¹ * c ∈ N := by
      rw [← QuotientGroup.eq]
      exact hxc
    have hxC : x⁻¹ * c ∈ C := mul_mem (inv_mem (commutator_le_left C C hx)) hc
    have h1 : x⁻¹ * c = 1 := by
      have : x⁻¹ * c ∈ N ⊓ C := ⟨hxN, hxC⟩
      rw [hNC] at this
      exact mem_bot.mp this
    have : c = x := by
      calc c = x * (x⁻¹ * c) := by group
        _ = x := by rw [h1, mul_one]
    exact this ▸ hx
  obtain ⟨𝒯, h𝒯, hind, hsup⟩ := ih C hCD hCn hCperf
    (fun A hA hAC hAs => hsol A hA (hAC.trans hCD.le) hAs)
    (fun M hM hMC => hmin M hM (hMC.trans hCD.le))
  have hN𝒯 : N ∉ 𝒯 := by
    intro hmem
    have : N ≤ C := hsup ▸ le_sSup (Finset.mem_coe.mpr hmem)
    apply hNmin.1.2
    rw [← inf_eq_left.mpr this, hNC]
  classical
  refine ⟨insert N 𝒯, ?_, ?_, ?_⟩
  · intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact ⟨hNn, inferInstance⟩
    · exact h𝒯 T hT
  · rw [Finset.coe_insert]
    refine sSupIndep_insert_normal hind (by simpa using hN𝒯) ?_
    rw [hsup, disjoint_iff]
    exact hNC
  · rw [Finset.coe_insert, sSup_insert, hsup, ← hDC]

end Schreier

section Structure

variable {G : Type*} [Group G]

/-- Simplicity of a factor from the lattice of subgroups between `K` and `H`. -/
lemma isSimpleGroup_factor_of_lattice {H K : Subgroup G} [K.Normal] (hKH : K < H)
    (hlat : ∀ L : Subgroup G, K ≤ L → L ≤ H → (∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) →
      L = K ∨ L = H) :
    IsSimpleGroup (factor H K) := by
  obtain ⟨h₀, hh₀, hk₀⟩ := SetLike.exists_of_lt hKH
  have hnt : Nontrivial (factor H K) := ⟨⟨⟨(h₀ : G ⧸ K), mem_factor.mpr ⟨h₀, hh₀, rfl⟩⟩, 1,
    fun h => hk₀ ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h))⟩⟩
  refine @IsSimpleGroup.mk _ _ hnt ?_
  intro N hN
  set L := (N.map (factor H K).subtype).comap (QuotientGroup.mk' K) with hLdef
  have hKL : K ≤ L := by
    intro k hk
    refine ⟨1, one_mem _, ?_⟩
    simp [(QuotientGroup.eq_one_iff k).mpr hk]
  have hLH : L ≤ H := by
    intro l hl
    obtain ⟨y, -, hy⟩ := hl
    apply mem_of_mk_mem_factor hKH.le
    have : ((l : G) : G ⧸ K) = y := hy.symm
    rw [this]
    exact y.2
  have hnorm : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := by
    intro h hh l hl
    obtain ⟨y, hy, hyl⟩ := hl
    let hf : factor H K := ⟨(h : G ⧸ K), mem_factor.mpr ⟨h, hh, rfl⟩⟩
    refine ⟨hf * y * hf⁻¹, hN.conj_mem y hy hf, ?_⟩
    simp only [coe_subtype, coe_mul, coe_inv] at hyl ⊢
    rw [hyl]
    rfl
  rcases hlat L hKL hLH hnorm with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, hg, hgy⟩ := mem_factor.mp y.2
    have hgL : g ∈ L := ⟨y, hy, hgy.symm⟩
    rw [h] at hgL
    rw [mem_bot]
    apply Subtype.ext
    rw [← hgy]
    exact (QuotientGroup.eq_one_iff _).mpr hgL
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, hg, hgy⟩ := mem_factor.mp y.2
    have hgL : g ∈ L := h ▸ hg
    obtain ⟨z, hz, hzg⟩ := hgL
    have : z = y := Subtype.ext (hzg.trans hgy)
    exact this ▸ hz

/-- The converse: a simple factor `U/S` has no subgroups strictly between `S` and `U` normalized
by `U`. -/
lemma eq_or_eq_of_isSimpleGroup {U S : Subgroup G} [S.Normal]
    (hT : IsSimpleGroup (U.map (QuotientGroup.mk' S))) {L : Subgroup G} (hSL : S ≤ L)
    (hLU : L ≤ U) (hnorm : ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ ∈ L) : L = S ∨ L = U := by
  set T := U.map (QuotientGroup.mk' S)
  set N := (L.map (QuotientGroup.mk' S)).subgroupOf T
  have hN : N.Normal := by
    constructor
    intro n hn t
    obtain ⟨l, hl, hln⟩ := hn
    obtain ⟨u, hu, hut⟩ := t.2
    rw [mem_subgroupOf]
    refine ⟨u * l * u⁻¹, hnorm u hu l hl, ?_⟩
    simp only [coe_mul, coe_inv, map_mul, map_inv]
    rw [hln, hut]
    rfl
  rcases (haveI := hN; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with h | h
  · left
    refine le_antisymm (fun l hl => ?_) hSL
    have hmem : (⟨QuotientGroup.mk' S l, mem_map_of_mem _ (hLU hl)⟩ : T) ∈ N :=
      mem_map_of_mem _ hl
    rw [h, mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hmem)
  · right
    refine le_antisymm hLU fun u hu => ?_
    have hmem : (⟨QuotientGroup.mk' S u, mem_map_of_mem _ hu⟩ : T) ∈ N := h ▸ mem_top _
    have hu' : u ∈ (L.map (QuotientGroup.mk' S)).comap (QuotientGroup.mk' S) := hmem
    rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hSL] at hu'

/-- For a non-abelian chief factor `H/K` and a normal `X` with `G/X` soluble, `H ≤ KX`. -/
lemma le_sup_of_solvable_quotient {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K)
    (hnab : ¬ ⁅H, H⁆ ≤ K) (X : Subgroup G) [X.Normal] (hX : Group.IsSolvable (G ⧸ X)) :
    H ≤ K ⊔ X := by
  haveI := hc.1
  rcases hc.eq_or_eq (normal_inf_normal H (K ⊔ X)) (le_inf hc.2.2.1.le le_sup_left)
    inf_le_left with h | h
  · exfalso
    apply hnab
    apply commutator_le_of_solvable_factor hc
    obtain ⟨n, hn⟩ := (isSolvable_def _).mp hX
    have hGX : derivedSeries G n ≤ X := by
      rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective X), Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk'] at hn
      exact hn
    rw [isSolvable_def]
    refine ⟨n, eq_bot_iff.mpr fun y hy => ?_⟩
    have hy1 : (y : G ⧸ K) ∈ derivedSeries (G ⧸ K) n :=
      map_derivedSeries_le_derivedSeries (factor H K).subtype n (mem_map_of_mem _ hy)
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective K)] at hy1
    obtain ⟨g, hg, hgy⟩ := hy1
    obtain ⟨k, hk, hky⟩ := mem_factor.mp y.2
    have hkg : g⁻¹ * k ∈ K := by
      rw [← QuotientGroup.eq]
      exact hgy.trans hky.symm
    have hkX : k ∈ K ⊔ X := by
      have : k = g * (g⁻¹ * k) := by group
      rw [this, sup_comm]
      exact mul_mem (mem_sup_left (hGX hg)) (mem_sup_right hkg)
    have hkK : k ∈ K := h ▸ (⟨hk, hkX⟩ : k ∈ H ⊓ (K ⊔ X))
    rw [mem_bot]
    apply Subtype.ext
    rw [← hky]
    exact (QuotientGroup.eq_one_iff _).mpr hkK
  · rw [← h]; exact inf_le_right

/-- **Proposition 2.3, "⇐"** (and the non-abelian case of Proposition 2.4, "⇐").  If `S ≤ D`
are normal, `S` and `G/D` are soluble and `D/S` is a direct product of `G`-invariant simple
groups, then every non-abelian chief factor of `G` is simple. -/
theorem simple_of_structure {S D : Subgroup G} [S.Normal] [D.Normal] (hSD : S ≤ D)
    (hS : Group.IsSolvable S) (hD : Group.IsSolvable (G ⧸ D))
    (hT : IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' S)))
    {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K)
    (hnab : ∃ a b : factor H K, a * b ≠ b * a) : IsSimpleGroup (factor H K) := by
  haveI := hc.1
  have hKH := hc.2.2.1
  have hnab' := nonabelian_iff.mp hnab
  have hHD := le_sup_of_solvable_quotient hc hnab' D hD
  -- `H ∩ S ≤ K`
  have hHS : H ⊓ S ≤ K := by
    haveI : (H ⊓ S).Normal := normal_inf_normal H S
    rcases hc.eq_or_eq inferInstance
      (le_sup_right : K ≤ (H ⊓ S) ⊔ K) (sup_le inf_le_left hKH.le) with h | h
    · exact h ▸ le_sup_left
    · exfalso
      apply hnab'
      apply commutator_le_of_solvable_factor hc
      have hle : factor H K ≤ S.map (QuotientGroup.mk' K) := by
        rw [factor, ← h, Subgroup.map_sup]
        have : K.map (QuotientGroup.mk' K) = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [this, sup_bot_eq]
        exact Subgroup.map_mono inf_le_right
      haveI := isSolvable_map (QuotientGroup.mk' K) S
      exact isSolvable_of_le hle
  obtain ⟨𝒯, h𝒯, hind, hsup⟩ := hT
  -- the subgroup of elements centralizing `H/K`
  set M := (centralizer (factor H K : Set (G ⧸ K))).comap (QuotientGroup.mk' K) with hMdef
  have hM : ∀ X : Subgroup G, ⁅H, X⁆ ≤ K → X ≤ M := by
    intro X hX x hx
    show (x : G ⧸ K) ∈ centralizer _
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_factor.mp hy
    have hc' : h * x * h⁻¹ * x⁻¹ ∈ K := hX (commutator_mem_commutator hh hx)
    have : ((h * x * h⁻¹ * x⁻¹ : G) : G ⧸ K) = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    calc (h : G ⧸ K) * x = ((h : G ⧸ K) * x * (h : G ⧸ K)⁻¹ * (x : G ⧸ K)⁻¹) * x * h := by group
      _ = x * h := by rw [this, one_mul]
  have hM' : ¬ H ≤ M := by
    intro hle
    apply hnab'
    rw [commutator_le]
    intro x hx y hy
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    have h' : (x : G ⧸ K) * (y : G ⧸ K) = (y : G ⧸ K) * (x : G ⧸ K) :=
      mem_centralizer_iff.mp (hle hy) (x : G ⧸ K) (mem_factor.mpr ⟨x, hx, rfl⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h']
    group
  have hSM : S ≤ M := hM S ((commutator_le_inf H S).trans hHS)
  have hKM : K ≤ M := hM K (commutator_le_right H K)
  -- some simple factor `T = U/S` with `[H, U] ≰ K`
  have hex : ∃ T ∈ 𝒯, ¬ ⁅H, T.comap (QuotientGroup.mk' S)⁆ ≤ K := by
    by_contra hne
    push Not at hne
    apply hM'
    have hDM : D ≤ M := by
      have h1 : D.map (QuotientGroup.mk' S) ≤ M.map (QuotientGroup.mk' S) := by
        rw [← hsup]
        apply sSup_le
        intro T hT
        have := Subgroup.map_mono (f := QuotientGroup.mk' S) (hM _ (hne T hT))
        rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)] at this
      have h2 := comap_mono (f := QuotientGroup.mk' S) h1
      rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hSD,
        sup_eq_left.mpr hSM] at h2
      exact h2
    exact hHD.trans (sup_le hKM hDM)
  obtain ⟨T, hT𝒯, hHU⟩ := hex
  obtain ⟨hTn, hTs⟩ := h𝒯 T hT𝒯
  set U := T.comap (QuotientGroup.mk' S) with hUdef
  haveI hUn : U.Normal := hTn.comap _
  have hSU : S ≤ U := by
    intro s hs
    show (s : G ⧸ S) ∈ T
    rw [(QuotientGroup.eq_one_iff s).mpr hs]
    exact one_mem _
  have hUmap : U.map (QuotientGroup.mk' S) = T :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S) T
  have hTs' : IsSimpleGroup (U.map (QuotientGroup.mk' S)) := hUmap ▸ hTs
  set V := H ⊓ U with hVdef
  haveI hVn : V.Normal := normal_inf_normal H U
  have hcomm : ⁅H, U⁆ ≤ V := le_inf (commutator_le_left H U) (commutator_le_right H U)
  have hVK : V ⊔ K = H := by
    rcases hc.eq_or_eq (L := V ⊔ K) inferInstance le_sup_right (sup_le inf_le_left hKH.le)
      with h | h
    · exact absurd ((hcomm.trans le_sup_left).trans h.le) hHU
    · exact h
  have hVS : V ⊔ S = U := by
    rcases eq_or_eq_of_isSimpleGroup hTs' le_sup_right (sup_le inf_le_right hSU)
      (fun u _ l hl => (inferInstance : (V ⊔ S).Normal).conj_mem l hl u) with h | h
    · exfalso
      apply hHU
      refine hcomm.trans ?_
      intro v hv
      exact hHS ⟨hv.1, h ▸ (mem_sup_left hv : v ∈ V ⊔ S)⟩
    · exact h
  have hVSK : V ⊓ S ≤ K := (inf_le_inf_right S inf_le_left).trans hHS
  -- the lattice criterion
  apply isSimpleGroup_factor_of_lattice hKH
  intro L hKL hLH hLn
  set L₀ := (L ⊓ V) ⊔ S
  have hL₀U : L₀ ≤ U := sup_le (inf_le_right.trans inf_le_right) hSU
  have hL₀n : ∀ u ∈ U, ∀ l ∈ L₀, u * l * u⁻¹ ∈ L₀ := by
    intro u hu l hl
    obtain ⟨a, ha, s, hs, rfl⟩ := mem_sup_normal_right.mp hl
    rw [← hVS] at hu
    obtain ⟨v, hv, s', hs', rfl⟩ := mem_sup_normal_right.mp hu
    have hconj : v * s' * a * (v * s')⁻¹ ∈ L ⊓ V := by
      -- `s' a s'⁻¹ = (s' a s'⁻¹ a⁻¹) a` with the commutator in `S ∩ V ≤ K ≤ L`
      have hcS : s' * a * s'⁻¹ * a⁻¹ ∈ S := by
        have := (inferInstance : S.Normal).conj_mem _ (inv_mem hs') a
        simpa [mul_assoc] using mul_mem hs' this
      have hcV : s' * a * s'⁻¹ * a⁻¹ ∈ V := by
        have := (inferInstance : V.Normal).conj_mem a ha.2 s'
        exact mul_mem this (inv_mem ha.2)
      have hcL : s' * a * s'⁻¹ * a⁻¹ ∈ L := hKL (hVSK ⟨hcV, hcS⟩)
      have h1 : s' * a * s'⁻¹ ∈ L := by
        have := mul_mem hcL ha.1
        simpa [mul_assoc] using this
      have h2 : s' * a * s'⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem a ha.2 s'
      have h3 : v * (s' * a * s'⁻¹) * v⁻¹ ∈ L := hLn v hv.1 _ h1
      have h4 : v * (s' * a * s'⁻¹) * v⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem _ h2 v
      have : v * s' * a * (v * s')⁻¹ = v * (s' * a * s'⁻¹) * v⁻¹ := by group
      rw [this]
      exact ⟨h3, h4⟩
    have : v * s' * (a * s) * (v * s')⁻¹ =
        (v * s' * a * (v * s')⁻¹) * ((v * s') * s * (v * s')⁻¹) := by group
    rw [this]
    exact mul_mem (mem_sup_left hconj)
      (mem_sup_right ((inferInstance : S.Normal).conj_mem s hs _))
  rcases eq_or_eq_of_isSimpleGroup hTs' le_sup_right hL₀U hL₀n with h | h
  · left
    refine le_antisymm (fun l hl => ?_) hKL
    rw [← hVK] at hLH
    obtain ⟨v, hv, k, hk, rfl⟩ := mem_sup_normal_right.mp (hLH hl)
    have hvL : v ∈ L := by
      have := mul_mem hl (inv_mem (hKL hk))
      simpa using this
    have hvS : v ∈ S := h ▸ (mem_sup_left ⟨hvL, hv⟩ : v ∈ L₀)
    exact mul_mem (hVSK ⟨hv, hvS⟩) hk
  · right
    refine le_antisymm hLH ?_
    rw [← hVK]
    refine sup_le (fun v hv => ?_) hKL
    have hv' : v ∈ L₀ := by
      show v ∈ L ⊓ V ⊔ S
      rw [h, ← hVS]
      exact mem_sup_left hv
    obtain ⟨a, ha, s, hs, has⟩ := mem_sup_normal_right.mp hv'
    have hsV : s ∈ V := by
      have : s = a⁻¹ * v := by rw [← has]; group
      rw [this]
      exact mul_mem (inv_mem ha.2) hv
    rw [← has]
    exact mul_mem ha.1 (hKL (hVSK ⟨hsV, hs⟩))

end Structure

section Cyclic

variable {G : Type*} [Group G]

lemma CyclicFactor.map {G' : Type*} [Group G'] {f : G →* G'} {H K : Subgroup G}
    (h : CyclicFactor H K) : CyclicFactor (H.map f) (K.map f) := by
  obtain ⟨g, hg, hH⟩ := h
  refine ⟨f g, mem_map_of_mem f hg, ?_⟩
  rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers]

lemma CyclicFactor.comap {N : Subgroup G} [N.Normal] {H K : Subgroup (G ⧸ N)}
    (h : CyclicFactor H K) :
    CyclicFactor (H.comap (QuotientGroup.mk' N)) (K.comap (QuotientGroup.mk' N)) := by
  obtain ⟨y, hy, hH⟩ := h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  refine ⟨g, hy, ?_⟩
  have hNK : N ≤ K.comap (QuotientGroup.mk' N) := by
    intro n hn
    show QuotientGroup.mk' N n ∈ K
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hmap : (K.comap (QuotientGroup.mk' N) ⊔ zpowers g).map (QuotientGroup.mk' N) =
      K ⊔ zpowers (QuotientGroup.mk' N g) := by
    rw [Subgroup.map_sup, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N),
      MonoidHom.map_zpowers]
  rw [hH, ← hmap, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr (hNK.trans le_sup_left)]

lemma isCyclic_factor {H K : Subgroup G} [K.Normal] (h : CyclicFactor H K) :
    IsCyclic (factor H K) := by
  obtain ⟨g, hg, hH⟩ := h
  refine ⟨⟨⟨(g : G ⧸ K), mem_factor.mpr ⟨g, hg, rfl⟩⟩, fun y => ?_⟩⟩
  obtain ⟨h, hh, hy⟩ := mem_factor.mp y.2
  rw [hH] at hh
  obtain ⟨k, hk, z, hz, rfl⟩ := mem_sup_normal_left.mp hh
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hz
  refine ⟨m, Subtype.ext ?_⟩
  rw [← hy]
  simp [(QuotientGroup.eq_one_iff k).mpr hk]

/-- `CyclicFactor H K` says exactly that the factor group `H/K` is cyclic. -/
lemma cyclicFactor_iff_isCyclic {H K : Subgroup G} [K.Normal] (hKH : K ≤ H) :
    CyclicFactor H K ↔ IsCyclic (factor H K) := by
  refine ⟨isCyclic_factor, fun h => ?_⟩
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := factor H K)
  obtain ⟨g, hg, hgy⟩ := mem_factor.mp y.2
  refine ⟨g, hg, le_antisymm (fun x hx => ?_) (sup_le hKH (zpowers_le.mpr hg))⟩
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hy ⟨(x : G ⧸ K), mem_factor.mpr ⟨x, hx, rfl⟩⟩)
  have hq : ((g ^ m : G) : G ⧸ K) = (x : G ⧸ K) := by
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_zpow] at this
    rw [← hgy] at this
    simpa using this
  rw [QuotientGroup.eq] at hq
  have : x = g ^ m * ((g ^ m)⁻¹ * x) := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers g) m)) (mem_sup_right hq)

lemma mulAut_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (σ τ : MulAut C) :
    σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic τ.toMonoidHom
  ext x
  simp only [MulAut.mul_apply]
  have h1 := hm (τ x)
  have h2 := hk x
  have h3 := hk (σ x)
  have h4 := hm x
  simp only [MulEquiv.coe_toMonoidHom] at h1 h2 h3 h4
  rw [h1, h2, h3, h4, ← zpow_mul, ← zpow_mul, mul_comm]

lemma commutator_le_of_cyclicFactor {H K : Subgroup G} [K.Normal] (h : CyclicFactor H K) :
    ⁅H, H⁆ ≤ K := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := nonabelian_iff.mpr hne
  haveI := isCyclic_factor h
  letI := IsCyclic.commGroup (α := factor H K)
  exact hab (mul_comm a b)

/-- A cyclic chief factor is simple. -/
lemma simple_of_cyclicFactor {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K)
    (hcyc : CyclicFactor H K) : IsSimpleGroup (factor H K) := by
  haveI := hc.1
  haveI : IsCyclic (factor H K) := isCyclic_factor hcyc
  haveI : (factor H K).Normal := factor_normal
  apply isSimpleGroup_factor_of_lattice hc.2.2.1
  intro L hKL hLH _
  apply hc.eq_or_eq _ hKL hLH
  constructor
  intro l hl x
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic
    (MulAut.conjNormal (H := factor H K) (x : G ⧸ K)).toMonoidHom
  have := congrArg Subtype.val (hm ⟨(l : G ⧸ K), mem_factor.mpr ⟨l, hLH hl, rfl⟩⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, SubgroupClass.coe_zpow] at this
  have hq : ((l ^ m : G) : G ⧸ K) = ((x * l * x⁻¹ : G) : G ⧸ K) := by
    simpa using this.symm
  rw [QuotientGroup.eq] at hq
  have : x * l * x⁻¹ = l ^ m * ((l ^ m)⁻¹ * (x * l * x⁻¹)) := by group
  rw [this]
  exact mul_mem (zpow_mem hl m) (hKL hq)

/-- A simple abelian chief factor is cyclic. -/
lemma cyclicFactor_of_simple_abelian {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K)
    (hs : IsSimpleGroup (factor H K)) (hab : ⁅H, H⁆ ≤ K) : CyclicFactor H K := by
  have hcomm : ∀ a b : factor H K, a * b = b * a := by
    by_contra h
    push Not at h
    exact (nonabelian_iff.mp h) hab
  obtain ⟨f, hf⟩ := exists_ne (1 : factor H K)
  obtain ⟨g, hg, hgf⟩ := mem_factor.mp f.2
  have hZ : (zpowers f).Normal := by
    constructor
    intro n hn x
    rw [hcomm x n, mul_inv_cancel_right]
    exact hn
  rcases (haveI := hZ; IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers f)) with h | h
  · exact absurd (mem_bot.mp (h ▸ mem_zpowers f)) hf
  refine ⟨g, hg, le_antisymm (fun x hx => ?_) (sup_le hc.2.2.1.le (zpowers_le.mpr hg))⟩
  have hxm : (⟨(x : G ⧸ K), mem_factor.mpr ⟨x, hx, rfl⟩⟩ : factor H K) ∈ zpowers f :=
    h ▸ mem_top _
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hxm
  have hq : ((g ^ m : G) : G ⧸ K) = (x : G ⧸ K) := by
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_zpow] at this
    rw [← hgf] at this
    simpa using this
  rw [QuotientGroup.eq] at hq
  have : x = g ^ m * ((g ^ m)⁻¹ * x) := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers g) m)) (mem_sup_right hq)

lemma exists_eq_zpowers_of_le {Q : Type*} [Group Q] {A : Subgroup Q} {c : Q}
    (h : A ≤ zpowers c) : ∃ y ∈ A, A = zpowers y := by
  haveI : IsCyclic (A.subgroupOf (zpowers c)) := Subgroup.isCyclic _
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := A.subgroupOf (zpowers c))
  have hyA : (y : zpowers c).1 ∈ A := y.2
  refine ⟨(y : zpowers c).1, hyA, le_antisymm (fun a ha => ?_) (zpowers_le.mpr hyA)⟩
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hy ⟨⟨a, h ha⟩, ha⟩)
  exact mem_zpowers_iff.mpr ⟨m, by
    simpa using congrArg (fun z : A.subgroupOf (zpowers c) => ((z : zpowers c) : Q)) hm⟩

/-- A chief factor lying between two consecutive terms of a normal series with cyclic factors
(after joining with `K`) is cyclic. -/
lemma cyclicFactor_of_chain {H K : Subgroup G} [K.Normal] (hc : IsChiefFactor H K) (n : ℕ)
    (A : ℕ → Subgroup G) (hAn : ∀ i, (A i).Normal) (hcyc : ∀ i < n, CyclicFactor (A (i + 1)) (A i))
    (htop : H ≤ K ⊔ A n) (hbot : H ⊓ (K ⊔ A 0) = K) : CyclicFactor H K := by
  classical
  haveI := hc.1
  have hex : ∃ j, H ≤ K ⊔ A j := ⟨n, htop⟩
  have hjH : H ≤ K ⊔ A (Nat.find hex) := Nat.find_spec hex
  have hjn : Nat.find hex ≤ n := Nat.find_min' hex htop
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hjH
    apply hc.2.2.1.ne'
    rw [← hbot]
    exact (inf_eq_left.mpr hjH).symm
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hin : i < n := by omega
  have hnot : ¬ H ≤ K ⊔ A i := Nat.find_min hex (by omega)
  haveI := hAn i
  have hHM : H ⊓ (K ⊔ A i) = K := by
    rcases hc.eq_or_eq (normal_inf_normal H (K ⊔ A i)) (le_inf hc.2.2.1.le le_sup_left)
      inf_le_left with h | h
    · exact h
    · exact absurd (h.symm.le.trans inf_le_right) hnot
  obtain ⟨a, -, ha⟩ := hcyc i hin
  have hHa : H ≤ (K ⊔ A i) ⊔ zpowers a := by
    have := hjH
    rwa [hi, ha, ← sup_assoc] at this
  set M := K ⊔ A i with hMdef
  have hle : H.map (QuotientGroup.mk' M) ≤ zpowers (QuotientGroup.mk' M a) := by
    rw [← MonoidHom.map_zpowers]
    calc H.map _ ≤ (M ⊔ zpowers a).map (QuotientGroup.mk' M) := Subgroup.map_mono hHa
      _ = (zpowers a).map _ := by
        rw [Subgroup.map_sup]
        have : M.map (QuotientGroup.mk' M) = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [this, bot_sup_eq]
  obtain ⟨y, hy, hHy⟩ := exists_eq_zpowers_of_le hle
  obtain ⟨h, hh, rfl⟩ := hy
  refine ⟨h, hh, le_antisymm (fun x hx => ?_) (sup_le hc.2.2.1.le (zpowers_le.mpr hh))⟩
  have hxm : QuotientGroup.mk' M x ∈ zpowers (QuotientGroup.mk' M h) :=
    hHy ▸ mem_map_of_mem _ hx
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hxm
  have hq : ((h ^ m : G) : G ⧸ M) = (x : G ⧸ M) := by simpa using hm
  rw [QuotientGroup.eq] at hq
  have hK : (h ^ m)⁻¹ * x ∈ K := by
    rw [← hHM]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (zpow_mem hh m)) hx, hq⟩
  have : x = h ^ m * ((h ^ m)⁻¹ * x) := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers h) m)) (mem_sup_right hK)

/-- Building a normal series with cyclic factors through chief factors. -/
lemma exists_normalCyclicSeries [Finite G] {A B₀ : Subgroup G} [A.Normal]
    (hcyc : ∀ H K : Subgroup G, IsChiefFactor H K → A ≤ K → H ≤ B₀ → CyclicFactor H K) :
    ∀ B : Subgroup G, B.Normal → A ≤ B → B ≤ B₀ → NormalCyclicSeries A B := by
  intro B
  induction B using WellFoundedLT.induction with
  | _ B ih =>
  intro hBn hAB hBB₀
  by_cases hAB' : A = B
  · subst hAB'
    exact ⟨0, fun _ => A, rfl, rfl, fun _ => inferInstance,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨K, hAK, hKmax⟩ := Finite.exists_le_maximal
    (p := fun K : Subgroup G => K.Normal ∧ A ≤ K ∧ K < B) (a := A)
    ⟨inferInstance, le_rfl, lt_of_le_of_ne hAB hAB'⟩
  obtain ⟨hKn, -, hKB⟩ := hKmax.1
  have hchief : IsChiefFactor B K := by
    refine ⟨hBn, hKn, hKB, fun L hL hKL hLB => ?_⟩
    by_cases hLB' : L = B
    · exact Or.inr hLB'
    · exact Or.inl (le_antisymm (hKmax.2 ⟨hL, hAK.trans hKL, lt_of_le_of_ne hLB hLB'⟩ hKL) hKL)
  obtain ⟨n, f, hf0, hfn, hfnorm, hfcyc⟩ := ih K hKB hKn hAK (hKB.le.trans hBB₀)
  classical
  refine ⟨n + 1, fun i => if i ≤ n then f i else B, by simp [hf0], by simp, fun i => ?_,
    fun i hi => ?_⟩
  · dsimp only
    split_ifs
    exacts [hfnorm i, hBn]
  · by_cases hin : i < n
    · simp only [show i ≤ n from hin.le, show i + 1 ≤ n from hin, if_true]
      exact hfcyc i hin
    · have : i = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
      rw [hfn]
      haveI := hKn
      exact hcyc B K hchief hAK hBB₀

lemma isSolvable_of_normalCyclicSeries {Q : Type*} [Group Q]
    (h : NormalCyclicSeries (⊥ : Subgroup Q) ⊤) : Group.IsSolvable Q := by
  obtain ⟨n, f, hf0, hfn, hfnorm, hfcyc⟩ := h
  have key : ∀ j ≤ n, derivedSeries Q j ≤ f (n - j) := by
    intro j
    induction j with
    | zero => intro _; simp [hfn]
    | succ j ih =>
      intro hj
      rw [derivedSeries_succ]
      have h1 := ih (by omega)
      haveI := hfnorm (n - (j + 1))
      have h2 := commutator_le_of_cyclicFactor (hfcyc (n - (j + 1)) (by omega))
      have e : n - (j + 1) + 1 = n - j := by omega
      rw [e] at h2
      exact (commutator_mono h1 h1).trans h2
  rw [isSolvable_def]
  exact ⟨n, eq_bot_iff.mpr ((key n le_rfl).trans (by simp [hf0]))⟩

/-- A perfect normal subgroup acts trivially on a cyclic normal factor. -/
lemma commutator_le_of_cyclicFactor_perfect {A B D : Subgroup G} [B.Normal] [A.Normal]
    (hcyc : CyclicFactor A B) (hperf : ⁅D, D⁆ = D) : ⁅A, D⁆ ≤ B := by
  haveI : IsCyclic (factor A B) := isCyclic_factor hcyc
  haveI : (factor A B).Normal := factor_normal
  set D' := D.map (QuotientGroup.mk' B)
  have hD' : ⁅D', D'⁆ = D' := by rw [← map_commutator, hperf]
  haveI : Group.IsPerfect D' := isPerfect_of_commutator_eq hD'
  haveI : Group.IsSolvable (MulAut (factor A B)) :=
    isSolvable_of_comm (fun σ τ => mulAut_comm_of_isCyclic σ τ)
  have h1 := CFSGOutside.Robinson.hom_eq_one
    ((MulAut.conjNormal (H := factor A B)).comp D'.subtype)
  rw [commutator_le]
  intro a ha d hd
  have h2 := congrArg (fun φ : D' →* MulAut (factor A B) =>
    ((φ ⟨(d : G ⧸ B), mem_map_of_mem _ hd⟩ ⟨(a : G ⧸ B), mem_factor.mpr ⟨a, ha, rfl⟩⟩ :
      factor A B) : G ⧸ B)) h1
  simp only [MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply, MonoidHom.one_apply,
    MulAut.one_apply] at h2
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  calc (a : G ⧸ B) * d * (a : G ⧸ B)⁻¹ * (d : G ⧸ B)⁻¹
      = a * ((d : G ⧸ B) * a * (d : G ⧸ B)⁻¹)⁻¹ := by group
    _ = 1 := by rw [h2]; group

/-- In an SC-group, soluble normal subgroups centralize every perfect subgroup (Grün's lemma
argument through the three subgroups lemma). -/
lemma commutator_eq_bot_of_solvable [Finite G] (hG : IsSC G) {D : Subgroup G}
    (hperf : ⁅D, D⁆ = D) : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → ⁅A, D⁆ = ⊥ := by
  intro A
  induction A using WellFoundedLT.induction with
  | _ A ih =>
  intro hAn hAs
  by_cases hA : A = ⊥
  · rw [hA, commutator_bot_left]
  obtain ⟨B, -, hBmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => B.Normal ∧ B < A) (a := ⊥)
    ⟨normal_bot, bot_lt_iff_ne_bot.mpr hA⟩
  obtain ⟨hBn, hBA⟩ := hBmax.1
  have hchief : IsChiefFactor A B := by
    refine ⟨hAn, hBn, hBA, fun L hL hBL hLA => ?_⟩
    by_cases hLA' : L = A
    · exact Or.inr hLA'
    · exact Or.inl (le_antisymm (hBmax.2 ⟨hL, lt_of_le_of_ne hLA hLA'⟩ hBL) hBL)
  haveI := hBn
  haveI := hAn
  haveI := hAs
  haveI : Group.IsSolvable B := isSolvable_of_le hBA.le
  have hBD := ih B hBA hBn inferInstance
  haveI := isSolvable_map (QuotientGroup.mk' B) A
  have hab := commutator_le_of_solvable_factor hchief inferInstance
  have hcyc := cyclicFactor_of_simple_abelian hchief (hG A B hchief) hab
  have hAD := commutator_le_of_cyclicFactor_perfect (D := D) hcyc hperf
  have h3 : ⁅⁅A, D⁆, D⁆ = ⊥ := eq_bot_iff.mpr ((commutator_mono hAD le_rfl).trans hBD.le)
  have h4 : ⁅⁅D, A⁆, D⁆ = ⊥ := by rw [commutator_comm D A]; exact h3
  have h5 := commutator_commutator_eq_bot_of_rotate h4 h3
  rw [hperf] at h5
  rw [commutator_comm]
  exact h5

end Cyclic

section Product

variable {Q : Type*} [Group Q]

/-- In a direct product of `Q`-invariant non-abelian simple groups, an abelian section `X/Y`
between `Q`-normal subgroups is trivial. -/
lemma le_of_commutator_le_of_product (𝒯 : Finset (Subgroup Q))
    (h𝒯 : ∀ T ∈ 𝒯, T.Normal ∧ IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a)
    (hind : sSupIndep (𝒯 : Set (Subgroup Q))) :
    ∀ X Y : Subgroup Q, X.Normal → Y.Normal → Y ≤ X → X ≤ sSup (𝒯 : Set (Subgroup Q)) →
      ⁅X, X⁆ ≤ Y → X ≤ Y := by
  classical
  induction 𝒯 using Finset.induction_on with
  | empty =>
    intro X Y _ _ _ hX _
    simp only [Finset.coe_empty, sSup_empty, le_bot_iff] at hX
    rw [hX]
    exact bot_le
  | insert T 𝒯' hT ih =>
    intro X Y hXn hYn hYX hX hXY
    have h𝒯' : ∀ T' ∈ 𝒯', T'.Normal ∧ IsSimpleGroup T' ∧ ∃ a b : T', a * b ≠ b * a :=
      fun T' h => h𝒯 T' (Finset.mem_insert_of_mem h)
    have hind' : sSupIndep (𝒯' : Set (Subgroup Q)) :=
      hind.mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    obtain ⟨hTn, hTs, hTnab⟩ := h𝒯 T (Finset.mem_insert_self T 𝒯')
    haveI : (sSup (𝒯' : Set (Subgroup Q))).Normal :=
      sSup_normal _ (fun T' h => (h𝒯' T' h).1)
    haveI := hTn
    haveI := hXn
    haveI := hYn
    have hdisj : Disjoint T (sSup (𝒯' : Set (Subgroup Q))) := by
      have := hind (Finset.mem_coe.mpr (Finset.mem_insert_self T 𝒯'))
      rwa [Finset.coe_insert, insert_diff_singleton_self (by simpa using hT)] at this
    have hX' : X ≤ T ⊔ sSup (𝒯' : Set (Subgroup Q)) := by
      rwa [Finset.coe_insert, sSup_insert] at hX
    have hTD' : ∀ s ∈ T, ∀ d ∈ sSup (𝒯' : Set (Subgroup Q)), s * d = d * s :=
      fun s hs d hd => (commute_of_normal_of_disjoint _ _ inferInstance inferInstance hdisj s d hs hd).eq
    by_cases hTY : T ≤ Y
    · have key := ih h𝒯' hind' (X ⊓ sSup (𝒯' : Set (Subgroup Q)))
        (Y ⊓ sSup (𝒯' : Set (Subgroup Q))) (normal_inf_normal _ _) (normal_inf_normal _ _)
        (inf_le_inf_right _ hYX) inf_le_right
        (le_inf ((commutator_mono inf_le_left inf_le_left).trans hXY)
          ((commutator_le_left _ _).trans inf_le_right))
      intro x hx
      obtain ⟨t, ht, d, hd, rfl⟩ := mem_sup_normal_left.mp (hX' hx)
      have hdX : d ∈ X := by
        have := mul_mem (inv_mem (hYX (hTY ht))) hx
        simpa using this
      exact mul_mem (hTY ht) (key ⟨hdX, hd⟩).1
    · have hTY' : T ⊓ Y = ⊥ := by
        rcases eq_bot_or_eq_of_le_simple (normal_inf_normal T Y) inf_le_left with h | h
        · exact h
        · exact absurd (h.symm.le.trans inf_le_right) hTY
      have hTX : T ⊓ X = ⊥ := by
        rcases eq_bot_or_eq_of_le_simple (normal_inf_normal T X) inf_le_left with h | h
        · exact h
        · exfalso
          have hTX' : T ≤ X := h.symm.le.trans inf_le_right
          apply not_comm_of_simple_normal hTnab
          rw [← commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hTY']
          exact le_inf (commutator_le_left T T) ((commutator_mono hTX' hTX').trans hXY)
      have hXT : ∀ x ∈ X, ∀ s ∈ T, x * s = s * x := by
        intro x hx s hs
        exact (commute_of_normal_of_disjoint X T inferInstance inferInstance
          (by rw [disjoint_iff, inf_comm, hTX]) x s hx hs).eq
      have hXD : X ≤ sSup (𝒯' : Set (Subgroup Q)) := by
        intro x hx
        obtain ⟨t, ht, d, hd, rfl⟩ := mem_sup_normal_left.mp (hX' hx)
        have hcen : t ∈ T ⊓ centralizer (T : Set Q) := by
          refine ⟨ht, mem_centralizer_iff.mpr fun s hs => ?_⟩
          have e1 := hXT (t * d) hx s hs
          have e2 := hTD' s hs d hd
          calc s * t = s * (t * d) * d⁻¹ := by group
            _ = t * d * s * d⁻¹ := by rw [← e1]
            _ = t * (d * s) * d⁻¹ := by group
            _ = t * (s * d) * d⁻¹ := by rw [e2]
            _ = t * s := by group
        have ht1 : t = 1 := by
          rcases eq_bot_or_eq_of_le_simple (normal_inf_normal T (centralizer (T : Set Q)))
            inf_le_left with h | h
          · rw [h] at hcen
            exact mem_bot.mp hcen
          · exact absurd (h.symm.le.trans inf_le_right) (not_comm_of_simple_normal hTnab)
        rw [ht1, one_mul]
        exact hd
      exact ih h𝒯' hind' X Y hXn hYn hYX hXD hXY

/-- The simple factors of a perfect direct product are non-abelian. -/
lemma nonabelian_of_perfect {D : Subgroup Q} (hperf : ⁅D, D⁆ = D) (𝒯 : Finset (Subgroup Q))
    (h𝒯 : ∀ T ∈ 𝒯, T.Normal ∧ IsSimpleGroup T) (hind : sSupIndep (𝒯 : Set (Subgroup Q)))
    (hsup : sSup (𝒯 : Set (Subgroup Q)) = D) : ∀ T ∈ 𝒯, ∃ a b : T, a * b ≠ b * a := by
  classical
  intro T hT
  by_contra hc
  push Not at hc
  obtain ⟨hTn, hTs⟩ := h𝒯 T hT
  haveI : (sSup ((𝒯 : Set (Subgroup Q)) \ {T})).Normal :=
    sSup_normal _ (fun T' h => (h𝒯 T' h.1).1)
  haveI := hTn
  set W := sSup ((𝒯 : Set (Subgroup Q)) \ {T})
  have hdisj : Disjoint T W := hind (Finset.mem_coe.mpr hT)
  have hDTW : D = T ⊔ W := by
    rw [← hsup, ← sSup_insert, Set.insert_diff_singleton,
      Set.insert_eq_of_mem (Finset.mem_coe.mpr hT)]
  have hTT : ⁅T, T⁆ = ⊥ :=
    commutator_eq_bot_of_comm (fun a ha b hb => congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩))
  have hDW : D ≤ W := by
    have h1 : D.map (QuotientGroup.mk' W) = T.map (QuotientGroup.mk' W) := by
      rw [hDTW, Subgroup.map_sup]
      have : W.map (QuotientGroup.mk' W) = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [this, sup_bot_eq]
    have h2 : D.map (QuotientGroup.mk' W) = ⊥ := by
      rw [← hperf, map_commutator, h1, ← map_commutator, hTT, Subgroup.map_bot]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
    exact h2
  have hTD : T ≤ D := by rw [← hsup]; exact le_sSup (Finset.mem_coe.mpr hT)
  have hT0 : T = ⊥ := by
    rw [eq_bot_iff, ← disjoint_iff.mp hdisj]
    exact le_inf le_rfl (hTD.trans hDW)
  obtain ⟨x, hx⟩ := exists_ne (1 : T)
  exact hx (Subtype.ext (mem_bot.mp (hT0.le x.2)))

end Product

section Main

variable {G : Type} [Group G] [Finite G]

lemma exists_derivedSeries_perfect (G : Type*) [Group G] [Finite G] :
    ∃ n, ⁅derivedSeries G n, derivedSeries G n⁆ = derivedSeries G n := by
  obtain ⟨m, k, hmk, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => derivedSeries G n)
  wlog h : m < k generalizing m k
  · exact this k m hmk.symm heq.symm (lt_of_le_of_ne (not_lt.mp h) hmk.symm)
  refine ⟨m, ?_⟩
  rw [← derivedSeries_succ]
  apply le_antisymm (derivedSeries_antitone G (Nat.le_succ m))
  rw [heq]
  exact derivedSeries_antitone G (by omega)

lemma isSolvable_quotient_derivedSeries (G : Type*) [Group G] (n : ℕ) :
    Group.IsSolvable (G ⧸ derivedSeries G n) := by
  rw [isSolvable_def]
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _), Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

/-- The decomposition of `D/S`, for an SNAC-group (proof of Propositions 2.3 and 2.4, "⇒"). -/
theorem isDirectProduct_quotient [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (hG : IsSNAC G)
    {S D : Subgroup G} [S.Normal] [D.Normal] (hS : Group.IsSolvable S) (hSD : S ≤ D)
    (hperf : ⁅D, D⁆ = D)
    (hmax : ∀ A : Subgroup G, A.Normal → S ≤ A → A ≤ D → Group.IsSolvable A → A ≤ S) :
    IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' S)) := by
  have hsurj := QuotientGroup.mk'_surjective S
  have hsol : ∀ A : Subgroup (G ⧸ S), A.Normal → A ≤ D.map (QuotientGroup.mk' S) →
      Group.IsSolvable A → A = ⊥ := by
    intro A hA hAD hAs
    have h1 : A.comap (QuotientGroup.mk' S) ≤ S := by
      refine hmax _ (hA.comap _) ?_ ?_ (isSolvable_comap hS A hAs)
      · intro s hs
        show QuotientGroup.mk' S s ∈ A
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff s).mpr hs]
        exact one_mem _
      · have := comap_mono (f := QuotientGroup.mk' S) hAD
        rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hSD] at this
    rw [← map_comap_eq_self_of_surjective hsurj A, eq_bot_iff]
    calc _ ≤ S.map (QuotientGroup.mk' S) := Subgroup.map_mono h1
      _ = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  apply isDirectProduct_of_perfect hCFSG _ ((inferInstance : D.Normal).map _ hsurj)
  · rw [← map_commutator, hperf]
  · exact hsol
  · intro N hN hND
    apply simple_of_minimal_normal hG hN
    by_contra hc
    push Not at hc
    haveI : Group.IsSolvable N := isSolvable_of_comm hc
    exact (bot_lt_iff_ne_bot.mp hN.2.2.1) (hsol N hN.1 hND inferInstance)

/-- **Groups with simple chief factors.** A finite group G has all its nonabelian chief factors simple if and only if it
has normal subgroups S ≤ D with S and G/D soluble and D/S a direct product of G-invariant simple groups. G has all
its chief factors simple if and only if some perfect normal subgroup D has G/D supersoluble, D/Z(D) a direct product
of G-invariant simple groups, and Z(D) supersolubly embedded in G. In both cases D can be taken to be the last term
G^(∞) of the derived series. If every chief factor of G is simple, then G^(∞) is a perfect group in which normality
is transitive, G/G^(∞) is supersoluble, the centralizer of G^(∞) is the soluble radical S of G, and the kernel of
the coupling G/G^(∞) → Out(G^(∞)) is G^(∞)S/G^(∞).

Source: D. J. S. Robinson, The structure of finite groups in which permutability is a transitive relation, J.
Austral. Math. Soc. 70 (2001), 143–159, Propositions 2.3 and 2.4, Corollary 2.5 and Lemma 2.6.
https://doi.org/10.1017/S1446788700002573

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem proposition_2_3 [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] :
    IsSNAC G ↔ ∃ (S D : Subgroup G) (_ : S.Normal) (_ : D.Normal), S ≤ D ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ D) ∧ IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' S)) := by
  constructor
  · intro hG
    obtain ⟨n, hn⟩ := exists_derivedSeries_perfect G
    obtain ⟨S, -, hSmax⟩ := Finite.exists_le_maximal
      (p := fun A : Subgroup G => A.Normal ∧ Group.IsSolvable A ∧ A ≤ derivedSeries G n) (a := ⊥)
      ⟨normal_bot, inferInstance, bot_le⟩
    obtain ⟨hSn, hSs, hSD⟩ := hSmax.1
    refine ⟨S, derivedSeries G n, hSn, inferInstance, hSD, hSs,
      isSolvable_quotient_derivedSeries G n, ?_⟩
    exact isDirectProduct_quotient hCFSG hG hSs hSD hn
      (fun A hA hSA hAD hAs => hSmax.2 ⟨hA, hAs, hAD⟩ hSA)
  · rintro ⟨S, D, hSn, hDn, hSD, hS, hD, hT⟩ H K _ hc hnab
    exact simple_of_structure hSD hS hD hT hc hnab

lemma centerIn_comm (D : Subgroup G) : ∀ a b : centerIn D, a * b = b * a := by
  intro a b
  apply Subtype.ext
  exact ((mem_centerIn.mp a.2).2 b (mem_centerIn.mp b.2).1).symm

/-- The structure of an SC-group relative to any perfect normal `D` with `G/D` soluble (in particular
`D = G^(∞)`): proof of Proposition 2.4, "⇒". -/
theorem sc_structure_of [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (hG : IsSC G)
    {D : Subgroup G} [D.Normal] (hn : ⁅D, D⁆ = D) (hsolq : Group.IsSolvable (G ⧸ D)) :
    IsSupersoluble (G ⧸ D) ∧
      IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' (centerIn D))) ∧
      IsSupersolublyEmbedded (centerIn D) := by
  have hSNAC : IsSNAC G := fun H K _ hc _ => hG H K hc
  haveI hZs : Group.IsSolvable (centerIn D) := isSolvable_of_comm (centerIn_comm _)
  refine ⟨?_, ?_, ?_⟩
  · haveI := hsolq
    refine exists_normalCyclicSeries (A := ⊥) (B₀ := ⊤) ?_ ⊤ normal_top bot_le le_rfl
    intro H K hc _ _
    haveI := hc.2.1
    have hc' := hc.comap (N := D)
    have hab : ⁅H, H⁆ ≤ K :=
      commutator_le_of_solvable_factor hc (solvable_of_solvable_injective
        (factor H K).subtype_injective)
    have hab' : ⁅H.comap (QuotientGroup.mk' (D)),
        H.comap (QuotientGroup.mk' (D))⁆ ≤
          K.comap (QuotientGroup.mk' (D)) := by
      rw [← map_le_iff_le_comap, map_commutator,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      exact hab
    haveI := hc'.2.1
    have hcyc := cyclicFactor_of_simple_abelian hc' (hG _ _ hc') hab'
    have := hcyc.map (f := QuotientGroup.mk' (D))
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at this
  · apply isDirectProduct_quotient hCFSG hSNAC hZs (centerIn_le _) hn
    intro A hA _ hAD hAs
    have := commutator_eq_bot_of_solvable hG hn A hA hAs
    rw [commutator_eq_bot_iff_le_centralizer] at this
    exact le_inf hAD this
  · refine exists_normalCyclicSeries (A := ⊥) (B₀ := centerIn (D)) ?_ _
      inferInstance bot_le le_rfl
    intro H K hc _ hHZ
    haveI := hc.2.1
    have hab : ⁅H, H⁆ ≤ K := by
      have : ⁅H, H⁆ = ⊥ := commutator_eq_bot_of_comm (fun a ha b hb =>
        ((mem_centerIn.mp (hHZ ha)).2 b (mem_centerIn.mp (hHZ hb)).1).symm)
      rw [this]
      exact bot_le
    exact cyclicFactor_of_simple_abelian hc (hG H K hc) hab

/-- **Robinson 2001, Proposition 2.4.** A finite group `G` is an SC-group if and only if there
is a perfect normal subgroup `D` such that `G/D` is supersoluble, `D/Z(D)` is a direct product of
`G`-invariant simple groups, and `Z(D)` is supersolubly embedded in `G`. -/
theorem proposition_2_4 [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] :
    IsSC G ↔ ∃ (D : Subgroup G) (_ : D.Normal), ⁅D, D⁆ = D ∧ IsSupersoluble (G ⧸ D) ∧
      IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' (centerIn D))) ∧
      IsSupersolublyEmbedded (centerIn D) := by
  constructor
  · intro hG
    obtain ⟨n, hn⟩ := exists_derivedSeries_perfect G
    exact ⟨derivedSeries G n, inferInstance, hn,
      sc_structure_of hCFSG hG hn (isSolvable_quotient_derivedSeries G n)⟩
  · rintro ⟨D, hDn, hperf, hsup, hT, hZ⟩ H K _ hc
    haveI : Group.IsSolvable (centerIn D) := isSolvable_of_comm (centerIn_comm _)
    have hDsol : Group.IsSolvable (G ⧸ D) := isSolvable_of_normalCyclicSeries hsup
    haveI := hc.1
    have hKH := hc.2.2.1
    by_cases hab : ⁅H, H⁆ ≤ K
    swap
    · exact simple_of_structure (centerIn_le D) inferInstance hDsol hT hc (nonabelian_iff.mpr hab)
    apply simple_of_cyclicFactor hc
    rcases hc.eq_or_eq (normal_inf_normal H (K ⊔ D)) (le_inf hKH.le le_sup_left) inf_le_left
      with h | h
    · -- the factor lies above `D`: use the supersoluble series of `G/D`
      obtain ⟨n, f, hf0, hfn, hfnorm, hfcyc⟩ := hsup
      refine cyclicFactor_of_chain hc n (fun i => (f i).comap (QuotientGroup.mk' D))
        (fun i => (hfnorm i).comap _) (fun i hi => (hfcyc i hi).comap) ?_ ?_
      · show H ≤ K ⊔ (f n).comap (QuotientGroup.mk' D)
        rw [hfn, comap_top]
        exact le_top.trans le_sup_right
      · show H ⊓ (K ⊔ (f 0).comap (QuotientGroup.mk' D)) = K
        rw [hf0, MonoidHom.comap_bot, QuotientGroup.ker_mk']
        exact h
    · have hHKD : H ≤ K ⊔ D := h.symm.le.trans inf_le_right
      rcases hc.eq_or_eq (normal_inf_normal H (K ⊔ centerIn D)) (le_inf hKH.le le_sup_left)
        inf_le_left with h' | h'
      · -- the factor would lie in `D/Z(D)`, a product of non-abelian simple groups: impossible
        exfalso
        obtain ⟨𝒯, h𝒯, hind, hsupT⟩ := hT
        have hsurj := QuotientGroup.mk'_surjective (centerIn D)
        have hnab := nonabelian_of_perfect (D := D.map (QuotientGroup.mk' (centerIn D)))
          (by rw [← map_commutator, hperf]) 𝒯 h𝒯 hind hsupT
        have key := le_of_commutator_le_of_product 𝒯
          (fun T hT => ⟨(h𝒯 T hT).1, (h𝒯 T hT).2, hnab T hT⟩) hind
          ((H ⊓ D).map (QuotientGroup.mk' (centerIn D)))
          ((K ⊓ D).map (QuotientGroup.mk' (centerIn D)))
          ((normal_inf_normal H D).map _ hsurj) ((normal_inf_normal K D).map _ hsurj)
          (Subgroup.map_mono (inf_le_inf_right D hKH.le)) (by rw [hsupT]; exact Subgroup.map_mono inf_le_right)
          (by
            rw [← map_commutator]
            exact Subgroup.map_mono (le_inf ((commutator_mono inf_le_left inf_le_left).trans hab)
              ((commutator_le_left _ _).trans inf_le_right)))
        have h1 := map_le_iff_le_comap.mp key
        rw [comap_map_eq, QuotientGroup.ker_mk'] at h1
        have h2 : H ≤ K ⊔ centerIn D := by
          intro x hx
          obtain ⟨k, hk, d, hd, rfl⟩ := mem_sup_normal_right.mp (hHKD hx)
          have hdH : d ∈ H := by
            have := mul_mem (inv_mem (hKH.le hk)) hx
            simpa using this
          have hd' := h1 ⟨hdH, hd⟩
          exact mul_mem (mem_sup_left hk) ((sup_le_sup_right (inf_le_left : K ⊓ D ≤ K) (centerIn D)) hd')
        have : H ≤ K := (le_inf le_rfl h2).trans h'.le
        exact lt_irrefl _ (lt_of_lt_of_le hKH this)
      · -- the factor lies in `Z(D)`: use the series of `Z(D)`
        obtain ⟨n, f, hf0, hfn, hfnorm, hfcyc⟩ := hZ
        refine cyclicFactor_of_chain hc n f hfnorm hfcyc ?_ ?_
        · rw [hfn]
          exact h'.symm.le.trans inf_le_right
        · rw [hf0, sup_bot_eq]
          exact inf_eq_right.mpr hKH.le


lemma derivedLimit_eq (G : Type*) [Group G] [Finite G] :
    ∃ n, derivedLimit G = derivedSeries G n ∧
      ⁅derivedSeries G n, derivedSeries G n⁆ = derivedSeries G n := by
  obtain ⟨n, hn⟩ := exists_derivedSeries_perfect G
  have hconst : ∀ k, derivedSeries G (n + k) = derivedSeries G n := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, derivedSeries_succ, ih, hn]
  refine ⟨n, le_antisymm (iInf_le _ n) (le_iInf fun m => ?_), hn⟩
  rcases le_total m n with h | h
  · exact derivedSeries_antitone G h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [hconst k]

/-- **Robinson 2001, Lemma 2.6(i).** Let `G` be an SC-group, `D = G^(∞)` and `R = D/Z(D)`. Then
`C_G(D) = C_G(R)`, and this is the soluble radical of `G` (a soluble normal subgroup containing
every soluble normal subgroup).  Here `C_G(R)` is the set of `g` acting trivially on `D/Z(D)`,
i.e. the preimage of the centralizer of `D/Z(D)` in `G/Z(D)`. -/
theorem lemma_2_6_i [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    centralizer (derivedLimit G : Set G) =
        (centralizer ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G))) :
          Set (G ⧸ centerIn (derivedLimit G)))).comap
          (QuotientGroup.mk' (centerIn (derivedLimit G))) ∧
      (centralizer (derivedLimit G : Set G)).Normal ∧
      Group.IsSolvable (centralizer (derivedLimit G : Set G)) ∧
      ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ centralizer (derivedLimit G : Set G) := by
  obtain ⟨n, hDn, hn⟩ := derivedLimit_eq G
  set D := derivedLimit G
  have hn' : ⁅D, D⁆ = D := by rw [hDn]; exact hn
  have hsolD : Group.IsSolvable (G ⧸ D) := by
    rw [isSolvable_def]
    refine ⟨n, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective D), ← hDn, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  set Z := centerIn D
  have hsurj := QuotientGroup.mk'_surjective Z
  have hSNAC : IsSNAC G := fun H K _ hc _ => hG H K hc
  haveI hZs : Group.IsSolvable Z := isSolvable_of_comm (centerIn_comm _)
  have hrad : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ centralizer (D : Set G) :=
    fun A hA hAs => commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_solvable hG hn' A hA hAs)
  set CR := (centralizer (D.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
    (QuotientGroup.mk' Z) with hCRdef
  haveI : (D.map (QuotientGroup.mk' Z)).Normal := (inferInstance : D.Normal).map _ hsurj
  haveI hCRn : CR.Normal := (normal_centralizer).comap _
  have hCCR : centralizer (D : Set G) ≤ CR := by
    intro g hg
    show (g : G ⧸ Z) ∈ centralizer _
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨d, hd, rfl⟩ := hy
    have := mem_centralizer_iff.mp hg d hd
    show ((d * g : G) : G ⧸ Z) = ((g * d : G) : G ⧸ Z)
    rw [this]
  -- `CR ∩ D ≤ Z(D)`, since `D/Z(D)` is a product of non-abelian simple groups
  have hCRD : CR ⊓ D ≤ Z := by
    obtain ⟨𝒯, h𝒯, hind, hsupT⟩ := isDirectProduct_quotient hCFSG hSNAC hZs (centerIn_le _) hn'
      (fun A hA _ hAD hAs => le_inf hAD (hrad A hA hAs))
    have hnab := nonabelian_of_perfect (D := D.map (QuotientGroup.mk' Z))
      (by rw [← map_commutator, hn']) 𝒯 h𝒯 hind hsupT
    have hXD : (CR ⊓ D).map (QuotientGroup.mk' Z) ≤ D.map (QuotientGroup.mk' Z) :=
      Subgroup.map_mono inf_le_right
    have hXC : (CR ⊓ D).map (QuotientGroup.mk' Z) ≤
        centralizer (D.map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) := by
      rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_left
    have key := le_of_commutator_le_of_product 𝒯
      (fun T hT => ⟨(h𝒯 T hT).1, (h𝒯 T hT).2, hnab T hT⟩) hind
      ((CR ⊓ D).map (QuotientGroup.mk' Z)) ⊥ ((normal_inf_normal CR D).map _ hsurj) normal_bot
      bot_le (by rw [hsupT]; exact hXD)
      (by
        rw [commutator_eq_bot_iff_le_centralizer.mpr ?_]
        intro x hx
        exact centralizer_le (hXD) (hXC hx))
    rw [le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at key
    exact key
  have hCRs : Group.IsSolvable CR := by
    haveI := hsolD
    haveI : Group.IsSolvable (CR ⊓ D : Subgroup G) := isSolvable_of_le hCRD
    let g : CR →* G ⧸ D := (QuotientGroup.mk' D).comp CR.subtype
    refine solvable_of_ker_le_range (inclusion (inf_le_left : CR ⊓ D ≤ CR)) g ?_
    intro x hx
    have hxD : (x : G) ∈ D := (QuotientGroup.eq_one_iff _).mp hx
    exact ⟨⟨x, Subgroup.mem_inf.mpr ⟨x.2, hxD⟩⟩, rfl⟩
  have hCRC : CR ≤ centralizer (D : Set G) := hrad CR hCRn hCRs
  have heq : centralizer (D : Set G) = CR := le_antisymm hCCR hCRC
  refine ⟨heq, heq ▸ hCRn, heq ▸ hCRs, hrad⟩

end Main

section Followup

variable {G : Type} [Group G] [Finite G]

lemma derivedLimit_perfect (G : Type*) [Group G] [Finite G] :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G := by
  obtain ⟨n, hDn, hn⟩ := derivedLimit_eq G
  rw [hDn]
  exact hn

lemma isSolvable_quotient_derivedLimit (G : Type*) [Group G] [Finite G] :
    Group.IsSolvable (G ⧸ derivedLimit G) := by
  obtain ⟨n, hDn, -⟩ := derivedLimit_eq G
  rw [isSolvable_def]
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedLimit G)), ← hDn,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- **Proposition 2.3, "⇒", with `D = G^(∞)`** (as in Robinson's proof). -/
theorem proposition_2_3_derivedLimit [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type)
    [Group G] [Finite G] (hG : IsSNAC G) :
    ∃ (S : Subgroup G) (_ : S.Normal), S ≤ derivedLimit G ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple ((derivedLimit G).map (QuotientGroup.mk' S)) := by
  obtain ⟨S, -, hSmax⟩ := Finite.exists_le_maximal
    (p := fun A : Subgroup G => A.Normal ∧ Group.IsSolvable A ∧ A ≤ derivedLimit G) (a := ⊥)
    ⟨normal_bot, inferInstance, bot_le⟩
  obtain ⟨hSn, hSs, hSD⟩ := hSmax.1
  refine ⟨S, hSn, hSD, hSs, isSolvable_quotient_derivedLimit G, ?_⟩
  exact isDirectProduct_quotient hCFSG hG hSs hSD (derivedLimit_perfect G)
    (fun A hA hSA hAD hAs => hSmax.2 ⟨hA, hAs, hAD⟩ hSA)

/-- **Proposition 2.4, "⇒", with `D = G^(∞)`** (as in Robinson's proof). -/
theorem proposition_2_4_derivedLimit [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type)
    [Group G] [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsSupersoluble (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple
        ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G)))) ∧
      IsSupersolublyEmbedded (centerIn (derivedLimit G)) :=
  ⟨derivedLimit_perfect G,
    sc_structure_of hCFSG hG (derivedLimit_perfect G) (isSolvable_quotient_derivedLimit G)⟩

/-! ### Lemma 2.6(ii): the coupling `G/D → Out(D)` -/

/-- The kernel of the coupling is `D C_G(D) / D`. -/
lemma ker_coupling (D : Subgroup G) [D.Normal] :
    (coupling D).ker = (D ⊔ centralizer (D : Set G)).map (QuotientGroup.mk' D) := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D y
  rw [MonoidHom.mem_ker, coupling, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
    conjOuter_eq_one_iff]
  constructor
  · intro hg
    exact mem_map_of_mem _ hg
  · rintro ⟨g', hg', hgg'⟩
    have hq : g'⁻¹ * g ∈ D := by
      rw [← QuotientGroup.eq]
      exact hgg'
    have : g = g' * (g'⁻¹ * g) := by group
    rw [this]
    exact mul_mem hg' (mem_sup_left hq)

/-- **Robinson 2001, Lemma 2.6(ii).** Let `G` be an SC-group, `D = G^(∞)` and `S` the soluble
radical of `G`. Then `DS/D` is the kernel of the coupling `χ : G/D → Out(D)`. -/
theorem lemma_2_6_ii [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] (hG : IsSC G) (S : Subgroup G) (hSn : S.Normal) (hSs : Group.IsSolvable S)
    (hSmax : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ S) :
    (coupling (derivedLimit G)).ker =
      (derivedLimit G ⊔ S).map (QuotientGroup.mk' (derivedLimit G)) := by
  obtain ⟨-, hCn, hCs, hrad⟩ := lemma_2_6_i hCFSG G hG
  have hS : S = centralizer (derivedLimit G : Set G) :=
    le_antisymm (hrad S hSn hSs) (hSmax _ hCn hCs)
  rw [ker_coupling, hS]

/-! ### Corollary 2.5: `G^(∞)` is a T-group -/

section Product2

variable {Q : Type*} [Group Q]

lemma eq_bot_or_eq_of_le_simple' {T M : Subgroup Q} [IsSimpleGroup T]
    (hM : ∀ t ∈ T, ∀ m ∈ M, t * m * t⁻¹ ∈ M) (hMT : M ≤ T) : M = ⊥ ∨ M = T := by
  have hn : (M.subgroupOf T).Normal := by
    constructor
    intro n hn t
    rw [mem_subgroupOf] at hn ⊢
    simpa using hM t t.2 n hn
  rcases (haveI := hn; IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf T)) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hMT hx⟩ : T) ∈ M.subgroupOf T := hx
    rw [h] at this
    simpa using congrArg Subtype.val (mem_bot.mp this)
  · right
    refine le_antisymm hMT fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ M.subgroupOf T := h ▸ mem_top _
    exact this

/-- In a direct product of non-abelian simple normal subgroups, every subgroup normalized by the
product is a sub-product. -/
lemma exists_subfamily_of_normalized (𝒯 : Finset (Subgroup Q))
    (h𝒯 : ∀ T ∈ 𝒯, T.Normal ∧ IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a)
    (hind : sSupIndep (𝒯 : Set (Subgroup Q))) :
    ∀ M : Subgroup Q, M ≤ sSup (𝒯 : Set (Subgroup Q)) →
      (∀ d ∈ sSup (𝒯 : Set (Subgroup Q)), ∀ m ∈ M, d * m * d⁻¹ ∈ M) →
      ∃ J : Finset (Subgroup Q), J ⊆ 𝒯 ∧ M = sSup (J : Set (Subgroup Q)) := by
  classical
  induction 𝒯 using Finset.induction_on with
  | empty =>
    intro M hM _
    refine ⟨∅, subset_rfl, ?_⟩
    simp only [Finset.coe_empty, sSup_empty, le_bot_iff] at hM ⊢
    exact hM
  | insert T 𝒯' hT ih =>
    intro M hM hMn
    have h𝒯' : ∀ T' ∈ 𝒯', T'.Normal ∧ IsSimpleGroup T' ∧ ∃ a b : T', a * b ≠ b * a :=
      fun T' h => h𝒯 T' (Finset.mem_insert_of_mem h)
    have hind' : sSupIndep (𝒯' : Set (Subgroup Q)) :=
      hind.mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    obtain ⟨hTn, hTs, hTnab⟩ := h𝒯 T (Finset.mem_insert_self T 𝒯')
    haveI hD'n : (sSup (𝒯' : Set (Subgroup Q))).Normal :=
      sSup_normal _ (fun T' h => (h𝒯' T' h).1)
    haveI := hTn
    have hsup : sSup ((insert T 𝒯' : Finset (Subgroup Q)) : Set (Subgroup Q)) =
        T ⊔ sSup (𝒯' : Set (Subgroup Q)) := by rw [Finset.coe_insert, sSup_insert]
    have hdisj : Disjoint T (sSup (𝒯' : Set (Subgroup Q))) := by
      have := hind (Finset.mem_coe.mpr (Finset.mem_insert_self T 𝒯'))
      rwa [Finset.coe_insert, insert_diff_singleton_self (by simpa using hT)] at this
    have hTD' : ∀ s ∈ T, ∀ d ∈ sSup (𝒯' : Set (Subgroup Q)), s * d = d * s :=
      fun s hs d hd => (commute_of_normal_of_disjoint _ _ inferInstance inferInstance hdisj s d
        hs hd).eq
    have hM' : M ≤ T ⊔ sSup (𝒯' : Set (Subgroup Q)) := hsup ▸ hM
    have hD'le : sSup (𝒯' : Set (Subgroup Q)) ≤
        sSup ((insert T 𝒯' : Finset (Subgroup Q)) : Set (Subgroup Q)) := by
      rw [hsup]; exact le_sup_right
    have hTle : T ≤ sSup ((insert T 𝒯' : Finset (Subgroup Q)) : Set (Subgroup Q)) := by
      rw [hsup]; exact le_sup_left
    by_cases hTM : T ≤ M
    · obtain ⟨J, hJ, hJeq⟩ := ih h𝒯' hind' (M ⊓ sSup (𝒯' : Set (Subgroup Q))) inf_le_right
        (fun d hd m hm => Subgroup.mem_inf.mpr ⟨hMn d (hD'le hd) m hm.1,
          hD'n.conj_mem m hm.2 d⟩)
      refine ⟨insert T J, Finset.insert_subset_insert T hJ, ?_⟩
      rw [Finset.coe_insert, sSup_insert, ← hJeq]
      refine le_antisymm (fun x hx => ?_) (sup_le hTM inf_le_left)
      obtain ⟨t, ht, d, hd, rfl⟩ := mem_sup_normal_left.mp (hM' hx)
      have hdM : d ∈ M := by
        have := mul_mem (inv_mem (hTM ht)) hx
        simpa using this
      exact mul_mem (mem_sup_left ht) (mem_sup_right (Subgroup.mem_inf.mpr ⟨hdM, hd⟩))
    · have hMT : M ⊓ T = ⊥ := by
        rcases eq_bot_or_eq_of_le_simple' (T := T) (M := M ⊓ T)
          (fun t ht m hm => Subgroup.mem_inf.mpr ⟨hMn t (hTle ht) m hm.1, hTn.conj_mem m hm.2 t⟩)
          inf_le_right with h | h
        · exact h
        · exact absurd (h.symm.le.trans inf_le_left) hTM
      have hMcomm : ∀ m ∈ M, ∀ s ∈ T, m * s = s * m := by
        intro m hm s hs
        have h1 : m * (s * m⁻¹ * s⁻¹) ∈ M := mul_mem hm (hMn s (hTle hs) _ (inv_mem hm))
        have h2 : (m * s * m⁻¹) * s⁻¹ ∈ T := mul_mem (hTn.conj_mem s hs m) (inv_mem hs)
        have h3 : m * s * m⁻¹ * s⁻¹ = 1 := by
          have : m * s * m⁻¹ * s⁻¹ ∈ M ⊓ T := Subgroup.mem_inf.mpr ⟨by simpa [mul_assoc] using h1, h2⟩
          rw [hMT] at this
          exact mem_bot.mp this
        calc m * s = (m * s * m⁻¹ * s⁻¹) * s * m := by group
          _ = s * m := by rw [h3, one_mul]
      have hMD' : M ≤ sSup (𝒯' : Set (Subgroup Q)) := by
        intro x hx
        obtain ⟨t, ht, d, hd, rfl⟩ := mem_sup_normal_left.mp (hM' hx)
        have hcen : t ∈ T ⊓ centralizer (T : Set Q) := by
          refine Subgroup.mem_inf.mpr ⟨ht, mem_centralizer_iff.mpr fun s hs => ?_⟩
          have e1 := hMcomm (t * d) hx s hs
          have e2 := hTD' s hs d hd
          calc s * t = s * (t * d) * d⁻¹ := by group
            _ = t * d * s * d⁻¹ := by rw [← e1]
            _ = t * (d * s) * d⁻¹ := by group
            _ = t * (s * d) * d⁻¹ := by rw [e2]
            _ = t * s := by group
        have ht1 : t = 1 := by
          rcases eq_bot_or_eq_of_le_simple (normal_inf_normal T (centralizer (T : Set Q)))
            inf_le_left with h | h
          · rw [h] at hcen
            exact mem_bot.mp hcen
          · exact absurd (h.symm.le.trans inf_le_right) (not_comm_of_simple_normal hTnab)
        rw [ht1, one_mul]
        exact hd
      obtain ⟨J, hJ, hJeq⟩ := ih h𝒯' hind' M hMD' (fun d hd m hm => hMn d (hD'le hd) m hm)
      exact ⟨J, hJ.trans (Finset.subset_insert T 𝒯'), hJeq⟩

/-- A supremum of non-abelian simple normal subgroups is perfect. -/
lemma sSup_perfect (J : Set (Subgroup Q))
    (hJ : ∀ T ∈ J, T.Normal ∧ IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a) :
    ⁅sSup J, sSup J⁆ = sSup J := by
  haveI : (sSup J).Normal := sSup_normal _ (fun T h => (hJ T h).1)
  refine le_antisymm (commutator_le_left _ _) (sSup_le fun T hT => ?_)
  obtain ⟨hTn, hTs, hTnab⟩ := hJ T hT
  haveI := hTn
  have hTT : ⁅T, T⁆ = T := by
    rcases eq_bot_or_eq_of_le_simple (inferInstance : (⁅T, T⁆).Normal) (commutator_le_left T T)
      with h | h
    · exact absurd (commutator_eq_bot_iff_le_centralizer.mp h) (not_comm_of_simple_normal hTnab)
    · exact h
  rw [← hTT]
  exact commutator_mono (le_sSup hT) (le_sSup hT)

end Product2

/-- The T-group argument inside `G`: for `D` perfect normal with `D/Z(D)` a product of non-abelian
simple `G/Z(D)`-normal groups, normality inside `D` is transitive. -/
lemma normalized_of_normalized {D : Subgroup G} [D.Normal]
    (𝒯 : Finset (Subgroup (G ⧸ centerIn D)))
    (h𝒯 : ∀ T ∈ 𝒯, T.Normal ∧ IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a)
    (hind : sSupIndep (𝒯 : Set (Subgroup (G ⧸ centerIn D))))
    (hsup : sSup (𝒯 : Set (Subgroup (G ⧸ centerIn D))) = D.map (QuotientGroup.mk' (centerIn D)))
    {H K : Subgroup G} (hHK : H ≤ K) (hKD : K ≤ D) (hK : ∀ d ∈ D, ∀ k ∈ K, d * k * d⁻¹ ∈ K)
    (hH : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H := by
  classical
  set Z := centerIn D
  set π := QuotientGroup.mk' Z
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  -- `K Z / Z` is a sub-product
  obtain ⟨J, hJ, hJeq⟩ := exists_subfamily_of_normalized 𝒯 h𝒯 hind (K.map π)
    (by rw [hsup]; exact Subgroup.map_mono hKD)
    (by
      rw [hsup]
      rintro _ ⟨d, hd, rfl⟩ _ ⟨k, hk, rfl⟩
      exact ⟨d * k * d⁻¹, hK d hd k hk, by simp [π]⟩)
  have hJ' : ∀ T ∈ J, T.Normal ∧ IsSimpleGroup T ∧ ∃ a b : T, a * b ≠ b * a :=
    fun T hT => h𝒯 T (hJ hT)
  have hindJ : sSupIndep (J : Set (Subgroup (G ⧸ Z))) := hind.mono (by exact_mod_cast hJ)
  -- `H Z / Z` is a sub-product, hence normal and perfect
  obtain ⟨J', hJ'J, hJ'eq⟩ := exists_subfamily_of_normalized J hJ' hindJ (H.map π)
    (by rw [← hJeq]; exact Subgroup.map_mono hHK)
    (by
      rw [← hJeq]
      rintro _ ⟨k, hk, rfl⟩ _ ⟨h, hh, rfl⟩
      exact ⟨k * h * k⁻¹, hH k hk h hh, by simp [π]⟩)
  have hJ'' : ∀ T ∈ (J' : Set (Subgroup (G ⧸ Z))), T.Normal ∧ IsSimpleGroup T ∧
      ∃ a b : T, a * b ≠ b * a := fun T hT => hJ' T (hJ'J hT)
  haveI hHn : (H.map π).Normal := by
    rw [hJ'eq]; exact sSup_normal _ (fun T h => (hJ'' T h).1)
  have hHperf : ⁅H.map π, H.map π⁆ = H.map π := by rw [hJ'eq]; exact sSup_perfect _ hJ''
  set W := (H.map π).comap π with hWdef
  haveI hWn : W.Normal := hHn.comap π
  have hW : W = H ⊔ Z := by rw [hWdef, comap_map_eq, QuotientGroup.ker_mk']
  have hWWZ : W ≤ ⁅W, W⁆ ⊔ Z := by
    have h1 : (⁅W, W⁆).map π = H.map π := by
      rw [map_commutator, hWdef, map_comap_eq_self_of_surjective hsurj, hHperf]
    have := comap_mono (f := π) h1.ge
    rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at this
    calc W = H ⊔ Z := hW
      _ ≤ ⁅W, W⁆ ⊔ Z := this
  have hHD : H ≤ D := hHK.trans hKD
  have hWW : ⁅W, W⁆ ≤ H := by
    rw [commutator_le]
    intro x hx y hy
    rw [hW] at hx hy
    obtain ⟨h, hh, z, hz, rfl⟩ := mem_sup_normal_right.mp hx
    obtain ⟨h', hh', z', hz', rfl⟩ := mem_sup_normal_right.mp hy
    have hzD := (mem_centerIn.mp hz)
    have hz'D := (mem_centerIn.mp hz')
    have e1 : z * (h' * z') * z⁻¹ = h' * z' :=
      by rw [← hzD.2 _ (mul_mem (hHD hh') hz'D.1), mul_inv_cancel_right]
    have e2 : z' * h⁻¹ = h⁻¹ * z' := (hz'D.2 _ (inv_mem (hHD hh))).symm
    rw [commutatorElement_def]
    have e : h * z * (h' * z') * (h * z)⁻¹ * (h' * z')⁻¹ = h * h' * h⁻¹ * h'⁻¹ :=
      calc h * z * (h' * z') * (h * z)⁻¹ * (h' * z')⁻¹
          = h * (z * (h' * z') * z⁻¹) * h⁻¹ * (h' * z')⁻¹ := by group
        _ = h * h' * (z' * h⁻¹) * z'⁻¹ * h'⁻¹ := by rw [e1]; group
        _ = h * h' * (h⁻¹ * z') * z'⁻¹ * h'⁻¹ := by rw [e2]
        _ = h * h' * h⁻¹ * h'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hh hh') (inv_mem hh)) (inv_mem hh')
  haveI : (⁅W, W⁆).Normal := inferInstance
  intro d hd h hh
  have hhW : h ∈ W := by rw [hW]; exact mem_sup_left hh
  obtain ⟨c, hc, z, hz, rfl⟩ := mem_sup_normal_right.mp (hWWZ hhW)
  have hzH : z ∈ H := by
    have := mul_mem (inv_mem (hWW hc)) hh
    simpa using this
  have hdz : d * z * d⁻¹ = z := by
    rw [(mem_centerIn.mp hz).2 d hd, mul_inv_cancel_right]
  have : d * (c * z) * d⁻¹ = (d * c * d⁻¹) * (d * z * d⁻¹) := by group
  rw [this, hdz]
  exact mul_mem (hWW ((inferInstance : (⁅W, W⁆).Normal).conj_mem c hc d)) hzH

/-- With `D` as in Proposition 2.4, `D` is a T-group. -/
lemma isTGroup_of_structure {D : Subgroup G} [D.Normal] (hperf : ⁅D, D⁆ = D)
    (hT : IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' (centerIn D)))) :
    IsTGroup D := by
  obtain ⟨𝒯, h𝒯, hind, hsup⟩ := hT
  have hnab := nonabelian_of_perfect (D := D.map (QuotientGroup.mk' (centerIn D)))
    (by rw [← map_commutator, hperf]) 𝒯 h𝒯 hind hsup
  intro H K hHK hHKn hKn
  have key := normalized_of_normalized 𝒯 (fun T hT => ⟨(h𝒯 T hT).1, (h𝒯 T hT).2, hnab T hT⟩)
    hind hsup (H := H.map D.subtype) (K := K.map D.subtype) (Subgroup.map_mono hHK)
    (by rintro _ ⟨y, -, rfl⟩; exact y.2) ?_ ?_
  · constructor
    intro h hh d
    obtain ⟨y, hy, hyeq⟩ := key d d.2 h ⟨h, hh, rfl⟩
    have : y = d * h * d⁻¹ := Subtype.ext (by simpa using hyeq)
    exact this ▸ hy
  · rintro d hd _ ⟨k, hk, rfl⟩
    exact ⟨⟨d, hd⟩ * k * ⟨d, hd⟩⁻¹, hKn.conj_mem k hk ⟨d, hd⟩, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨h, hh, rfl⟩
    have h1 : (⟨h, hHK hh⟩ : K) ∈ H.subgroupOf K := hh
    have h2 := hHKn.conj_mem _ h1 ⟨k, hk⟩
    exact ⟨k * h * k⁻¹, h2, rfl⟩

/-- **Robinson 2001, Corollary 2.5.** An SC-group `G` is an extension of a perfect T-group by a
supersoluble group; namely `D = G^(∞)` is a perfect T-group and `G/D` is supersoluble. -/
theorem corollary_2_5 [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsTGroup (derivedLimit G) ∧
      IsSupersoluble (G ⧸ derivedLimit G) := by
  obtain ⟨hperf, hsup, hT, -⟩ := proposition_2_4_derivedLimit hCFSG G hG
  exact ⟨hperf, isTGroup_of_structure hperf hT, hsup⟩

end Followup

end CFSGOutside.Robinson
