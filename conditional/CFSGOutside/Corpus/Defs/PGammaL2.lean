import CFSGOutside.Corpus.Defs.DGroup

/-!
# Copied corpus definitions: the projective semilinear group `PΓL(2,K)`

Copied at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus.GorensteinWalter`, from the vendored Qiuzhen-CFSG files
`CFSG/ThirdParty/QiuzhenCFSG/GorensteinWalter/LinearRingEquiv.lean` (`gl2RingEquiv` line 92, private in the corpus,
and `pgl2RingEquiv` line 110 with `pgl2RingEquiv_one`/`pgl2RingEquiv_mul`),
`ProjectiveSemilinear.lean` (`pgl2FieldAut`, line 52) and `PGammaL2.lean` (`PGammaL2`, line 64).
The short proofs inside the definitions are the corpus ones.
-/

noncomputable section

namespace CFSGOutside.Corpus.GorensteinWalter

universe u v

/-- Copy of the corpus (private) `CFSG.GorensteinWalter.gl2RingEquiv`. -/
def gl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.GeneralLinearGroup (Fin 2) R ≃*
      Matrix.GeneralLinearGroup (Fin 2) S := by
  let f : Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 2) S :=
    Matrix.GeneralLinearGroup.map e.toRingHom
  let g : Matrix.GeneralLinearGroup (Fin 2) S →*
      Matrix.GeneralLinearGroup (Fin 2) R :=
    Matrix.GeneralLinearGroup.map e.symm.toRingHom
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · ext x i j
    simp [f, g]
  · ext x i j
    simp [f, g]

/-- `PGL₂` is invariant under equivalence of its coefficient rings. Copy of
`CFSG.GorensteinWalter.pgl2RingEquiv`. -/
def pgl2RingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : PGL2 R ≃* PGL2 S := by
  let eGL : Matrix.GeneralLinearGroup (Fin 2) R ≃*
      Matrix.GeneralLinearGroup (Fin 2) S := gl2RingEquiv e
  apply QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) eGL
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    obtain ⟨w, rfl⟩ := eGL.surjective z
    simpa using congrArg eGL (hy w)
  · intro hx
    refine ⟨eGL.symm x, ?_, eGL.apply_symm_apply x⟩
    intro z
    apply eGL.injective
    simpa using hx (eGL z)

/-- Copy of `CFSG.GorensteinWalter.pgl2RingEquiv_one`. -/
theorem pgl2RingEquiv_one
    (R : Type u) [CommRing R] :
    pgl2RingEquiv (1 : R ≃+* R) = 1 := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

/-- Copy of `CFSG.GorensteinWalter.pgl2RingEquiv_mul`. -/
theorem pgl2RingEquiv_mul
    {R : Type u} [CommRing R] (e f : R ≃+* R) :
    pgl2RingEquiv (e * f) = pgl2RingEquiv e * pgl2RingEquiv f := by
  apply MulEquiv.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  rfl

/-- The coefficient automorphism action on `PGL₂(K)`. Copy of `CFSG.GorensteinWalter.pgl2FieldAut`. -/
def pgl2FieldAut (K : Type u) [CommRing K] :
    (K ≃+* K) →* MulAut (PGL2 K) where
  toFun := pgl2RingEquiv
  map_one' := pgl2RingEquiv_one K
  map_mul' := pgl2RingEquiv_mul

/-- The dimension-two projective semilinear group `PΓL₂(K) = PGL₂(K) ⋊ Aut(K)`. Copy of
`CFSG.GorensteinWalter.PGammaL2`. -/
abbrev PGammaL2 (K : Type u) [CommRing K] :=
  PGL2 K ⋊[pgl2FieldAut K] (K ≃+* K)

end CFSGOutside.Corpus.GorensteinWalter
