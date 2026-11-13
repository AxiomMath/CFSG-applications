import CFSGOutside.Gagola.T45Defs
import CFSGOutside.Gagola.PerfectAux

namespace CFSGOutside.Gagola

open Classical

theorem sylowAb_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : SylowAb Y) : SylowAb X := by
  intro p hp hdvd P
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  have := h p hp (hc ▸ hdvd) (P.mapSurjective (f := (e : X →* Y)) e.surjective)
  have h2 : IsMulCommutative (P.map (e : X →* Y)) := this
  have h3 := isMulCommutative_map (e.symm : Y →* X) (P.map (e : X →* Y))
  have : (P : Subgroup X) = (P.map (e : X →* Y)).map (e.symm : Y →* X) := by
    rw [Subgroup.map_map]
    have : (e.symm : Y →* X).comp (e : X →* Y) = MonoidHom.id X := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [this]; exact h3

theorem solvable_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) [Group.IsSolvable Y] :
    Group.IsSolvable X :=
  solvable_of_solvable_injective (f := (e : X →* Y)) e.injective

section
variable {H : Type} [Group H] [Fintype H] (Z K : Subgroup H) [Z.Normal] [K.Normal]

/-- natural map `K/Z → H/Z`. -/
def subIota (hZK : Z ≤ K) : K ⧸ Z.subgroupOf K →* H ⧸ Z :=
  QuotientGroup.map (Z.subgroupOf K) Z K.subtype (fun x hx => hx)

theorem subIota_injective (hZK : Z ≤ K) : Function.Injective (subIota Z K hZK) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H k =>
    change ((k : H) : H ⧸ Z) = 1 at hx
    rw [QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff]
    exact hx

theorem sylowAb_sub (hS : SylowAb (H ⧸ Z)) (hZK : Z ≤ K) :
    SylowAb (K ⧸ Z.subgroupOf K) := by
  intro p hp hdvd P'
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := subIota_injective Z K hZK
  have hd : p ^ 6 ∣ Nat.card (H ⧸ Z) := by
    refine hdvd.trans ?_
    have h1 := Subgroup.card_subgroup_dvd_card (subIota Z K hZK).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h1
  have hpg : IsPGroup p (P'.map (subIota Z K hZK)) :=
    P'.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hpg
  have hQc := hS p hp hd Q
  haveI : IsMulCommutative (P'.map (subIota Z K hZK)) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hQc.is_comm.comm ⟨a.1, hQ a.2⟩ ⟨b.1, hQ b.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  refine ⟨⟨fun a b => ?_⟩⟩
  have := (inferInstance : IsMulCommutative (P'.map (subIota Z K hZK))).is_comm.comm
    ⟨subIota Z K hZK a.1, Subgroup.mem_map_of_mem _ a.2⟩
    ⟨subIota Z K hZK b.1, Subgroup.mem_map_of_mem _ b.2⟩
  apply Subtype.ext
  apply hinj
  have := congrArg Subtype.val this
  simpa using this

theorem card_sub_lt (hZK : Z ≤ K) (hKne : K ≠ ⊤) :
    Nat.card (K ⧸ Z.subgroupOf K) < Nat.card (H ⧸ Z) := by
  have hinj := subIota_injective Z K hZK
  have hns : ¬ Function.Surjective (subIota Z K hZK) := by
    intro hs
    apply hKne
    rw [eq_top_iff]
    intro h _
    obtain ⟨y, hy⟩ := hs (h : H ⧸ Z)
    induction y using QuotientGroup.induction_on with
    | H k =>
      change ((k : H) : H ⧸ Z) = (h : H ⧸ Z) at hy
      rw [QuotientGroup.eq] at hy
      have := K.mul_mem k.2 (hZK hy)
      simpa using this
  refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ hinj) fun heq => hns ?_
  exact (hinj.bijective_of_nat_card_le heq.ge).2

theorem solvable_of_sub_and_quot {p : ℕ} [Fact p.Prime] (hZK : Z ≤ K)
    (hK : Group.IsSolvable (K ⧸ Z.subgroupOf K)) (hp : IsPGroup p (H ⧸ K)) :
    Group.IsSolvable (H ⧸ Z) := by
  haveI : Group.IsSolvable (H ⧸ K) := by
    haveI := hp.isNilpotent
    infer_instance
  refine solvable_of_ker_le_range (subIota Z K hZK) (quotMap Z K hZK) ?_
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H h =>
    have hx' : (h : H ⧸ K) = 1 := hx
    rw [QuotientGroup.eq_one_iff] at hx'
    exact ⟨((⟨h, hx'⟩ : K) : K ⧸ Z.subgroupOf K), rfl⟩

end
end CFSGOutside.Gagola
