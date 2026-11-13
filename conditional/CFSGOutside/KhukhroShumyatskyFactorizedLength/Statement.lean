import CFSGOutside.Common.NonsolubleLength
import CFSGOutside.Corpus.Defs.GeneralizedFitting

/-!
# Khukhro–Shumyatsky, factorized groups: the definitions of Theorem 1.1

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780, DOI 10.1007/s10231-014-0443-1, arXiv:1405.1899.

The definitions the headline theorem mentions. `IsFactorization A B` says `G = AB`. The upper generalized
Fitting series is `fstarSeries X`: `F*_0(X) = 1` and `F*_{n+1}(X)/F*_n(X) = F*(X/F*_n(X))`, where
`F* = CFSGOutside.Corpus.generalizedFitting` is `F(X) E(X)`. The generalized Fitting height `h*(X)` is
`genFittingHeight X`, the least `h` with `F*_h(X) = X`. The nonsoluble length `λ(G)` is
`CFSGOutside.NonsolubleLength.nonsolubleLength`.
-/

namespace CFSGOutside.KhukhroShumyatskyFactorizedLength

open Subgroup CFSGOutside.Corpus

/-- `G = AB`: every element of `G` is a product of an element of `A` and an element of `B`. -/
def IsFactorization {Y : Type*} [Group Y] (A B : Subgroup Y) : Prop :=
  ∀ g : Y, ∃ a ∈ A, ∃ b ∈ B, g = a * b

variable {X : Type*} [Group X]

variable (X) in
/-- The upper generalized Fitting series `F*_n(X)`, together with its normality. -/
noncomputable def fstarSeriesN : ℕ → {N : Subgroup X // N.Normal}
  | 0 => ⟨⊥, normal_bot⟩
  | n + 1 =>
    haveI := (fstarSeriesN n).2
    ⟨(generalizedFitting (X ⧸ (fstarSeriesN n).1)).comap (QuotientGroup.mk' _),
      Normal.comap inferInstance _⟩

variable (X) in
/-- The upper generalized Fitting series `F*_n(X)` (Khukhro–Shumyatsky, Ann. Mat. Pura Appl. 2015, §1):
`F*_0 = 1` and `F*_{n+1}(X)/F*_n(X) = F*(X/F*_n(X))`. -/
noncomputable def fstarSeries (n : ℕ) : Subgroup X := (fstarSeriesN X n).1

variable (X) in
/-- `h*(X) ≤ h`: the generalized Fitting height of `X` is at most `h`, that is `F*_h(X) = X`. -/
def GenFittingHeightLE (h : ℕ) : Prop := fstarSeries X h = ⊤

variable (X) in
/-- The generalized Fitting height `h*(X)` (Khukhro–Shumyatsky, Ann. Mat. Pura Appl. 2015, §1), the least
`h` with `F*_h(X) = X`. -/
noncomputable def genFittingHeight : ℕ := sInf {h | GenFittingHeightLE X h}

end CFSGOutside.KhukhroShumyatskyFactorizedLength
