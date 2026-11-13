import Certificates.Certificate3085
import Certificates.Kernel.Ly3085.Squeeze
import Certificates.Kernel.SporSch.Ly.SevA
import CFSGOutside.Corpus.HallPaige.Ly

/-!
The definitions copied into `CFSGOutside.Corpus.HallPaige.Ly` agree with the corpus definitions.

Most copies are definitionally equal to their originals. The exceptions are the structures
`LySeed`, `LyOperator` and `BConsts`, which are new types, and the packed matrices `AF`, `AI`,
which were recomputed rather than copied. For those this file proves agreement: the seed class
is built from the corpus seed, the corpus suborbit theorem is transported along the equivariant
bijection between the two operator types, and the packed matrices and constants are checked
against the corpus values in the kernel.
-/

namespace CFSGOutsideClean.Corpus.Ly

open MulAction

theorem decode_eq :
    @CFSGOutside.Corpus.Ly.decode = @CFSG.Blueprint.NativeSporadic.decode := by
  with_unfolding_all rfl

theorem LySeed1_eq :
    CFSGOutside.Corpus.Ly.LySeed1 = CFSG.Blueprint.NativeSporadic.LySeed1 := by
  with_unfolding_all rfl

theorem LySeed2_eq :
    CFSGOutside.Corpus.Ly.LySeed2 = CFSG.Blueprint.NativeSporadic.LySeed2 := by
  with_unfolding_all rfl

theorem lyF_eq : CFSGOutside.Corpus.Ly.lyF = CFSG.Sporadic.LySchreier.lyF := by
  with_unfolding_all rfl

theorem lyE_eq : CFSGOutside.Corpus.Ly.lyE = CFSG.Sporadic.LySchreier.lyE := by
  with_unfolding_all rfl

/-- The copied seed class holds because the corpus seed class does. -/
theorem lySeed : CFSGOutside.Corpus.Ly.LySeed :=
  ⟨CFSG.Sporadic.Ly.LySeed.mA_sq, CFSG.Sporadic.Ly.LySeed.mB_pow,
    CFSG.Sporadic.Ly.LySeed.mX_pow, CFSG.Sporadic.Ly.LySeed.form_A,
    CFSG.Sporadic.Ly.LySeed.form_B⟩

theorem AF_eq : CFSGOutside.Corpus.Ly.AF = CertificateChecks.KernelSporSch.LySv.AF := by
  with_unfolding_all rfl

theorem AI_eq : CFSGOutside.Corpus.Ly.AI = CertificateChecks.KernelSporSch.LySv.AI := by
  with_unfolding_all rfl

theorem BC_ONEF_eq : CFSGOutside.Corpus.Ly.BC.ONEF = CFSG.KD.LyOm.BC.ONEF := by
  decide +kernel

theorem fMul_eq (X Y : ℕ) :
    CFSGOutside.Corpus.Ly.fMul CFSGOutside.Corpus.Ly.BC X Y =
      CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC X Y := by
  with_unfolding_all rfl

section Transport

variable {G α β : Type*} [Group G] [instα : MulAction G α] [instβ : MulAction G β]

theorem stabilizer_eq_of_equiv (e : α ≃ β) (he : ∀ (g : G) (x : α), e (g • x) = g • e x)
    (x : α) : stabilizer G x = stabilizer G (e x) := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← he, e.injective.eq_iff]

theorem orbit_eq_preimage_of_equiv (e : α ≃ β) (he : ∀ (g : G) (x : α), e (g • x) = g • e x)
    (x : α) : orbit G x = e ⁻¹' orbit G (e x) := by
  ext y
  simp only [Set.mem_preimage, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (he g x).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, e.injective (by rw [he, hg])⟩

theorem card_orbit_eq_of_equiv (e : α ≃ β) (he : ∀ (g : G) (x : α), e (g • x) = g • e x)
    (x : α) : Nat.card (orbit G x) = Nat.card (orbit G (e x)) := by
  rw [orbit_eq_preimage_of_equiv e he x]
  exact Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)


end Transport

abbrev GLM : Type := GL (Fin 111) (ZMod 5)

abbrev Mat : Type := Matrix (Fin 111) (Fin 111) (ZMod 5)

/-! The suborbit statement, abstracted over the data both copies of `F1_all` are built from. -/

/-- The strong generators `aStar j` of `lyH`, as words in `a` and `b`. -/
def gAStar (J : Subgroup GLM) (a b : J) (sw : ℕ → List ℤ) (j : ℕ) : J :=
  (CFSGOutside.Corpus.Ly.extendByWords [a, b] ((List.range 5).map fun j => sw (j + 2))).getD j 1

def gLyH (J : Subgroup GLM) (a b : J) (sw : ℕ → List ℤ) : Subgroup J :=
  Subgroup.closure (gAStar J a b sw '' Set.Icc 2 6)

def gRepG (J : Subgroup GLM) (a b : J) (wg : List (List ℕ)) (c : ℕ) : J :=
  ((wg.getD (c - 1) []).map fun l => [a, b, a⁻¹, b⁻¹].getD l 1).prod

/-- The conjugation action of `J` on an operator type wrapping matrices. -/
@[reducible] def gAct (J : Subgroup GLM) {Op : Type} (mk : Mat → Op) (val : Op → Mat)
    (hv : ∀ M, val (mk M) = M) (hmk : ∀ x, mk (val x) = x) : MulAction J Op where
  smul g E := mk (((g : GLM) : Mat) * val E * (((g⁻¹ : J) : GLM) : Mat))
  one_smul E := by
    change mk _ = E
    simp [hmk]
  mul_smul g h E := by
    change mk _ = mk (_ * val (mk _) * _)
    rw [hv]
    simp only [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

open Classical in
/-- The statement of the corpus `F1_all`, as a function of its data. -/
def gStmt (J : Subgroup GLM) (a b : J) {Op : Type} (mk : Mat → Op) (val : Op → Mat)
    (hv : ∀ M, val (mk M) = M) (hmk : ∀ x, mk (val x) = x) [Finite Op]
    (sw : ℕ → List ℤ) (wg : List (List ℕ)) (E : Mat) : Prop :=
  letI := gAct J mk val hv hmk
  (stabilizer J (mk E) = gLyH J a b sw ∧ Nat.card (gLyH J a b sw) = 5859000000 ∧
      Nat.card (orbit J (mk E)) = 8835156) ∧
    ((Finset.univ.biUnion (fun i : Fin 5 =>
        (Set.toFinite (orbit (gLyH J a b sw)
          (if i.val = 0 then mk E else gRepG J a b wg i.val • mk E))).toFinset) : Finset Op) :
        Set Op) = orbit J (mk E) ∧
    (Pairwise fun i j : Fin 5 =>
      Disjoint
        (Set.toFinite (orbit (gLyH J a b sw)
          (if i.val = 0 then mk E else gRepG J a b wg i.val • mk E))).toFinset
        (Set.toFinite (orbit (gLyH J a b sw)
          (if j.val = 0 then mk E else gRepG J a b wg j.val • mk E))).toFinset) ∧
    Nat.card (orbit (gLyH J a b sw) (mk E)) = 1 ∧
    Nat.card (orbit (gLyH J a b sw) (gRepG J a b wg 1 • mk E)) = 19530 ∧
    Nat.card (orbit (gLyH J a b sw) (gRepG J a b wg 2 • mk E)) = 968750 ∧
    Nat.card (orbit (gLyH J a b sw) (gRepG J a b wg 3 • mk E)) = 2034375 ∧
    Nat.card (orbit (gLyH J a b sw) (gRepG J a b wg 4 • mk E)) = 5812500

/-- Equal data give equivalent statements. -/
theorem gStmt_congr {J₁ J₂ : Subgroup GLM} (hJ : J₁ = J₂) {a₁ b₁ : J₁} {a₂ b₂ : J₂}
    (ha : (a₁ : GLM) = a₂) (hb : (b₁ : GLM) = b₂) {Op : Type} (mk : Mat → Op) (val : Op → Mat)
    (hv : ∀ M, val (mk M) = M) (hmk : ∀ x, mk (val x) = x) [Finite Op]
    {sw₁ sw₂ : ℕ → List ℤ} (hsw : sw₁ = sw₂) {wg₁ wg₂ : List (List ℕ)} (hwg : wg₁ = wg₂)
    {E₁ E₂ : Mat} (hE : E₁ = E₂) :
    gStmt J₁ a₁ b₁ mk val hv hmk sw₁ wg₁ E₁ ↔ gStmt J₂ a₂ b₂ mk val hv hmk sw₂ wg₂ E₂ := by
  subst hJ hsw hwg hE
  obtain rfl : a₁ = a₂ := Subtype.ext ha
  obtain rfl : b₁ = b₂ := Subtype.ext hb
  rfl

/-- The statement transfers between two operator types wrapping the same matrices. -/
theorem gStmt_transport (J : Subgroup GLM) (a b : J) {Op₁ Op₂ : Type}
    (mk₁ : Mat → Op₁) (val₁ : Op₁ → Mat) (hv₁ : ∀ M, val₁ (mk₁ M) = M)
    (hmk₁ : ∀ x, mk₁ (val₁ x) = x) [Finite Op₁]
    (mk₂ : Mat → Op₂) (val₂ : Op₂ → Mat) (hv₂ : ∀ M, val₂ (mk₂ M) = M)
    (hmk₂ : ∀ x, mk₂ (val₂ x) = x) [Finite Op₂]
    (sw : ℕ → List ℤ) (wg : List (List ℕ)) (E : Mat)
    (h : gStmt J a b mk₂ val₂ hv₂ hmk₂ sw wg E) : gStmt J a b mk₁ val₁ hv₁ hmk₁ sw wg E := by
  classical
  letI i₁ := gAct J mk₁ val₁ hv₁ hmk₁
  letI i₂ := gAct J mk₂ val₂ hv₂ hmk₂
  let e : Op₁ ≃ Op₂ :=
    ⟨fun x => mk₂ (val₁ x), fun y => mk₁ (val₂ y), fun x => by simp [hv₂, hmk₁],
      fun y => by simp [hv₁, hmk₂]⟩
  have he : ∀ (g : J) (x : Op₁), e (g • x) = g • e x := by
    intro g x
    change mk₂ (val₁ (mk₁ (((g : GLM) : Mat) * val₁ x * (((g⁻¹ : J) : GLM) : Mat)))) =
      mk₂ (((g : GLM) : Mat) * val₂ (mk₂ (val₁ x)) * (((g⁻¹ : J) : GLM) : Mat))
    rw [hv₁, hv₂]
  have heH : ∀ (g : gLyH J a b sw) (x : Op₁), e (g • x) = g • e x := fun g x => he g x
  have hE : e (mk₁ E) = mk₂ E := by
    change mk₂ (val₁ (mk₁ E)) = mk₂ E
    rw [hv₁]
  have hgE (c : ℕ) : e (gRepG J a b wg c • mk₁ E) = gRepG J a b wg c • mk₂ E := by
    rw [he, hE]
  have hrep (c : ℕ) :
      e (if c = 0 then mk₁ E else gRepG J a b wg c • mk₁ E) =
        if c = 0 then mk₂ E else gRepG J a b wg c • mk₂ E := by
    split_ifs
    · exact hE
    · exact hgE c
  have hsub (c : ℕ) :
      ((Set.toFinite (orbit (gLyH J a b sw)
          (if c = 0 then mk₁ E else gRepG J a b wg c • mk₁ E))).toFinset : Set Op₁) =
        e ⁻¹' ((Set.toFinite (orbit (gLyH J a b sw)
          (if c = 0 then mk₂ E else gRepG J a b wg c • mk₂ E))).toFinset : Set Op₂) := by
    simp only [Set.Finite.coe_toFinset]
    rw [← hrep]
    exact orbit_eq_preimage_of_equiv e heH _
  have hcardH (x : Op₁) (y : Op₂) (hxy : e x = y) {n : ℕ}
      (hn : Nat.card (orbit (gLyH J a b sw) y) = n) :
      Nat.card (orbit (gLyH J a b sw) x) = n := by
    rw [card_orbit_eq_of_equiv e heH, hxy, hn]
  obtain ⟨⟨hstab, hH, hJ⟩, hcover, hdisj, h0, h1, h2, h3, h4⟩ := h
  refine ⟨⟨?_, hH, ?_⟩, ?_, ?_, hcardH _ _ hE h0, hcardH _ _ (hgE 1) h1,
    hcardH _ _ (hgE 2) h2, hcardH _ _ (hgE 3) h3, hcardH _ _ (hgE 4) h4⟩
  · rw [stabilizer_eq_of_equiv e he, hE]
    exact hstab
  · rw [card_orbit_eq_of_equiv e he, hE]
    exact hJ
  · rw [orbit_eq_preimage_of_equiv e he, hE, ← hcover, Finset.coe_biUnion, Finset.coe_biUnion,
      Set.preimage_iUnion₂]
    simp only [hsub]
  · intro i j hij
    rw [← Finset.disjoint_coe, hsub, hsub]
    exact (Finset.disjoint_coe.2 (hdisj hij)).preimage e

theorem strongWord_eq :
    CFSGOutside.Corpus.Ly.strongWord = CFSG.Sporadic.LySchreier.strongWord := by
  with_unfolding_all rfl

theorem WG_eq : [CFSGOutside.Corpus.Ly.WG1, CFSGOutside.Corpus.Ly.WG2,
    CFSGOutside.Corpus.Ly.WG3, CFSGOutside.Corpus.Ly.WG4] =
      [CFSG.KD.LyOm.WG1, CFSG.KD.LyOm.WG2, CFSG.KD.LyOm.WG3, CFSG.KD.LyOm.WG4] := by
  decide +kernel

section Seed

variable [CFSGOutside.Corpus.Ly.LySeed]

theorem J_eq : (CFSGOutside.Corpus.Ly.J : Subgroup GLM) = CFSG.Sporadic.Ly.J :=
  rfl

theorem a_eq : ((CFSGOutside.Corpus.Ly.a : CFSGOutside.Corpus.Ly.J) : GLM) =
    ((CFSG.Sporadic.Ly.a : CFSG.Sporadic.Ly.J) : GLM) :=
  rfl

theorem b_eq : ((CFSGOutside.Corpus.Ly.b : CFSGOutside.Corpus.Ly.J) : GLM) =
    ((CFSG.Sporadic.Ly.b : CFSG.Sporadic.Ly.J) : GLM) :=
  rfl

/-- The corpus `F1_all`, as an instance of the abstract statement. -/
theorem corpus_gStmt :
    gStmt CFSG.Sporadic.Ly.J CFSG.Sporadic.Ly.a CFSG.Sporadic.Ly.b
      CFSG.Sporadic.LySchreier.LyOperator.mk CFSG.Sporadic.LySchreier.LyOperator.val
      (fun _ => rfl) (fun _ => rfl) CFSG.Sporadic.LySchreier.strongWord
      [CFSG.KD.LyOm.WG1, CFSG.KD.LyOm.WG2, CFSG.KD.LyOm.WG3, CFSG.KD.LyOm.WG4]
      CFSG.Sporadic.LySchreier.lyE :=
  CertificateChecks.KernelLy.Omega.F1_all

/-- The abstract statement over the copied data, obtained by rewriting along the equalities. -/
theorem copied_gStmt :
    gStmt CFSGOutside.Corpus.Ly.J CFSGOutside.Corpus.Ly.a CFSGOutside.Corpus.Ly.b
      CFSGOutside.Corpus.Ly.LyOperator.mk CFSGOutside.Corpus.Ly.LyOperator.val
      (fun _ => rfl) (fun _ => rfl) CFSGOutside.Corpus.Ly.strongWord
      [CFSGOutside.Corpus.Ly.WG1, CFSGOutside.Corpus.Ly.WG2, CFSGOutside.Corpus.Ly.WG3,
        CFSGOutside.Corpus.Ly.WG4]
      CFSGOutside.Corpus.Ly.lyE := by
  refine gStmt_transport _ _ _ _ _ _ _ CFSG.Sporadic.LySchreier.LyOperator.mk
    CFSG.Sporadic.LySchreier.LyOperator.val (fun _ => rfl) (fun _ => rfl) _ _ _ ?_
  exact (gStmt_congr J_eq a_eq b_eq _ _ _ _ strongWord_eq WG_eq lyE_eq).2 corpus_gStmt

end Seed

open Classical in
/-- The corpus suborbit theorem `F1_all`, transported to the copied definitions. -/
theorem F1_all [CFSGOutside.Corpus.Ly.LySeed] :
    (stabilizer CFSGOutside.Corpus.Ly.J CFSGOutside.Corpus.Ly.opE = CFSGOutside.Corpus.Ly.lyH ∧
        Nat.card CFSGOutside.Corpus.Ly.lyH = 5859000000 ∧
        Nat.card (orbit CFSGOutside.Corpus.Ly.J CFSGOutside.Corpus.Ly.opE) = 8835156) ∧
      ((Finset.univ.biUnion CFSGOutside.Corpus.Ly.subO :
          Finset CFSGOutside.Corpus.Ly.LyOperator) : Set CFSGOutside.Corpus.Ly.LyOperator) =
        orbit CFSGOutside.Corpus.Ly.J CFSGOutside.Corpus.Ly.opE ∧
      (Pairwise fun i j =>
        Disjoint (CFSGOutside.Corpus.Ly.subO i) (CFSGOutside.Corpus.Ly.subO j)) ∧
      Nat.card (orbit CFSGOutside.Corpus.Ly.lyH CFSGOutside.Corpus.Ly.opE) = 1 ∧
      Nat.card (orbit CFSGOutside.Corpus.Ly.lyH
        (CFSGOutside.Corpus.Ly.gRep 1 • CFSGOutside.Corpus.Ly.opE)) = 19530 ∧
      Nat.card (orbit CFSGOutside.Corpus.Ly.lyH
        (CFSGOutside.Corpus.Ly.gRep 2 • CFSGOutside.Corpus.Ly.opE)) = 968750 ∧
      Nat.card (orbit CFSGOutside.Corpus.Ly.lyH
        (CFSGOutside.Corpus.Ly.gRep 3 • CFSGOutside.Corpus.Ly.opE)) = 2034375 ∧
      Nat.card (orbit CFSGOutside.Corpus.Ly.lyH
        (CFSGOutside.Corpus.Ly.gRep 4 • CFSGOutside.Corpus.Ly.opE)) = 5812500 :=
  copied_gStmt

end CFSGOutsideClean.Corpus.Ly
