import CFSGOutside.Corpus.Defs.LieModel

/-!
# Corpus input: the Borel–Tits theorem for all models of simple groups of Lie type

Statement of `CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models`
(`CFSG/Milestones/CL_LIT_Borel_Tits_local_parabolic.lean`, line 29, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). In the corpus the tag type is written
`Assembly.LowTwoRank.StatedLieTag`, an `export` alias of `Open.StatedLieTag`, and the definitions `LieModel` and
`pCoreOf` are the copies in `CFSGOutside.Corpus.Defs`.

If `X` is a finite simple group of Lie type in characteristic `r` and `U` is a nontrivial `r`-subgroup, then the
normalizer of `U` lies in a proper parabolic subgroup (a proper subgroup containing the normalizer of a Sylow
`r`-subgroup, except for the Tits group, where it contains the Sylow `r`-subgroup itself).
-/

namespace CFSGOutside.Corpus

/-- Borel–Tits for every model of a simple group of Lie type, as
`cl_lit_borel_tits_local_parabolic_all_models` states it. -/
class ClLitBorelTitsLocalParabolicAllModels : Prop where
  cl_lit_borel_tits_local_parabolic_all_models :
    ∀ (X : Type) [Group X] (t : Open.StatedLieTag) (n r f : ℕ)
      (_ : Blueprint.LieModel X t n r f)
      (U : Subgroup X) (_ : U ≠ ⊥) (_ : IsPGroup r U),
      ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
        Subgroup.normalizer (U : Set X) ≤ P ∧
        Open.pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ Open.pCoreOf r P ∧
          U ≤ Open.pCoreOf r P ∧
        (t ≠ .Tits → Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) ∧
        (t = .Tits → (S : Subgroup X) ≤ P)

end CFSGOutside.Corpus
