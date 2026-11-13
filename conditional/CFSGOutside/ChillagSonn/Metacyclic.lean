import CFSGOutside.ChillagSonn.Defs

/-!
# Chillag–Sonn: basic facts on metacyclic groups

Closure properties of metacyclic and Sylow-metacyclic groups (Chillag–Sonn, Lemmas 1.1(a) and 1.3): both are
inherited by subgroups and homomorphic images, and a metacyclic group of exponent dividing `e` has order dividing
`e²`. In particular a Sylow-metacyclic group has no elementary abelian subgroup of order `p³`.
-/

namespace CFSGOutside.ChillagSonn

/-- Homomorphic images of metacyclic groups are metacyclic. -/
theorem IsMetacyclic.of_surjective {P Q : Type*} [Group P] [Group Q] (f : P →* Q) (hf : Function.Surjective f)
    (h : IsMetacyclic P) : IsMetacyclic Q := by
  obtain ⟨N, hN, hNc, hPN⟩ := h
  have hM : (N.map f).Normal := hN.map f hf
  refine ⟨N.map f, hM, isCyclic_of_surjective _ (f.subgroupMap_surjective N), ?_⟩
  refine isCyclic_of_surjective (QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N))
    (QuotientGroup.map_surjective_of_surjective _ _ _ ?_ _)
  exact (QuotientGroup.mk'_surjective _).comp hf

/-- Metacyclicity is invariant under isomorphism. -/
theorem IsMetacyclic.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (h : IsMetacyclic P) :
    IsMetacyclic Q :=
  h.of_surjective e.toMonoidHom e.surjective

/-- A group embedding into a metacyclic group is metacyclic. -/
theorem IsMetacyclic.of_injective {P Q : Type*} [Group P] [Group Q] (f : P →* Q) (hf : Function.Injective f)
    (h : IsMetacyclic Q) : IsMetacyclic P := by
  obtain ⟨N, hN, hNc, hQN⟩ := h
  have hM : (N.comap f).Normal := hN.comap f
  have : IsCyclic ((N.comap f).map f) := Subgroup.isCyclic_of_le (Subgroup.map_comap_le f N)
  refine ⟨N.comap f, hM,
    isCyclic_of_surjective _ ((N.comap f).equivMapOfInjective f hf).symm.surjective, ?_⟩
  refine isCyclic_of_injective (QuotientGroup.map (N.comap f) N f le_rfl) ?_
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- Subgroups of metacyclic groups are metacyclic. -/
theorem IsMetacyclic.subgroup {P : Type*} [Group P] (h : IsMetacyclic P) (H : Subgroup P) : IsMetacyclic H :=
  h.of_injective H.subtype H.subtype_injective

/-- A finite cyclic group of exponent dividing `e` has order dividing `e`. -/
private theorem card_dvd_of_isCyclic {C : Type*} [Group C] [IsCyclic C] {e : ℕ} (he : ∀ x : C, x ^ e = 1) :
    Nat.card C ∣ e :=
  IsCyclic.exponent_eq_card (α := C) ▸ Monoid.exponent_dvd_of_forall_pow_eq_one he

/-- A metacyclic group of exponent dividing `e` has order dividing `e²`. -/
theorem IsMetacyclic.card_dvd_sq {P : Type*} [Group P] [Finite P] (h : IsMetacyclic P) {e : ℕ}
    (he : ∀ x : P, x ^ e = 1) : Nat.card P ∣ e ^ 2 := by
  obtain ⟨N, hN, hNc, hPN⟩ := h
  rw [N.card_eq_card_quotient_mul_card_subgroup, sq]
  refine mul_dvd_mul (card_dvd_of_isCyclic fun x ↦ ?_) (card_dvd_of_isCyclic fun x ↦ Subtype.ext (he x))
  induction x using QuotientGroup.induction_on with
  | H x => rw [← QuotientGroup.mk_pow, he, QuotientGroup.mk_one]

/-- Lemma 1.3 for homomorphic images. -/
theorem SylowMetacyclic.of_surjective {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (hG : SylowMetacyclic G) : SylowMetacyclic H := by
  intro p _ P
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  exact (hG p Q).of_surjective (f.subgroupMap Q) (f.subgroupMap_surjective Q)

/-- Sylow-metacyclicity is invariant under isomorphism. -/
theorem SylowMetacyclic.of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] (e : G ≃* H)
    (hG : SylowMetacyclic G) : SylowMetacyclic H :=
  hG.of_surjective e.toMonoidHom e.surjective

/-- Quotients of Sylow-metacyclic groups are Sylow-metacyclic. -/
theorem SylowMetacyclic.quotient {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G) (N : Subgroup G)
    [N.Normal] : SylowMetacyclic (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Every `p`-subgroup of a Sylow-metacyclic group is metacyclic. -/
theorem SylowMetacyclic.isMetacyclic_of_isPGroup {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G)
    {p : ℕ} [Fact p.Prime] (Q : Subgroup G) (hQ : IsPGroup p Q) : IsMetacyclic Q := by
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  exact (hG p S).of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)

/-- Lemma 1.3 for subgroups. -/
theorem SylowMetacyclic.subgroup {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G) (H : Subgroup G) :
    SylowMetacyclic H := by
  intro p _ P
  have := hG.isMetacyclic_of_isPGroup (P.1.map H.subtype) (P.2.map H.subtype)
  exact this.of_mulEquiv (P.1.equivMapOfInjective H.subtype H.subtype_injective).symm

/-- A `p`-subgroup of exponent dividing `e` of a Sylow-metacyclic group has order dividing `e²`. -/
theorem SylowMetacyclic.card_dvd_sq {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G) {p : ℕ}
    [Fact p.Prime] (Q : Subgroup G) (hQ : IsPGroup p Q) {e : ℕ} (he : ∀ x ∈ Q, x ^ e = 1) :
    Nat.card Q ∣ e ^ 2 :=
  (hG.isMetacyclic_of_isPGroup Q hQ).card_dvd_sq fun x ↦ Subtype.ext (by simpa using he x x.2)

/-- A Sylow-metacyclic group has no elementary abelian subgroup of order `p³`: an abelian subgroup of exponent `p`
has order at most `p²`. -/
theorem SylowMetacyclic.card_le_of_elem {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G) {p : ℕ}
    [Fact p.Prime] (E : Subgroup G) (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  have hpE : IsPGroup p E := fun x ↦ ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
  exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos 2) (hG.card_dvd_sq E hpE hE)

/-- The 2-rank form used repeatedly: commuting involutions generate a subgroup of order at most 4. -/
theorem SylowMetacyclic.card_le_four {G : Type*} [Group G] [Finite G] (hG : SylowMetacyclic G)
    (E : Subgroup G) (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hG.card_le_of_elem E hE

end CFSGOutside.ChillagSonn
