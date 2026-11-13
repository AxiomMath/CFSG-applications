import CFSGOutside.Common.NonsolubleLength
import CFSGOutside.Common.NonPSolubleLength

/-!
# Khukhro–Shumyatsky, the paper's literal definitions

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*, Israel J. Math. **207**
(2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434.

The definitions the headline theorems mention: normal series with a factor predicate (`PaperSeries`), the
nonsoluble length `paperNonsolubleLength` and the maximum `2`-length `paperMaxTwoLength` of §1 (Theorem 1.1(a),
Corollary 1.2), and the non-`p`-soluble length `paperNonPSolubleLength` and the maximum `p`-length
`paperMaxPLength` (Theorem 1.1(b)). The crosswalks to the working notions are in `TheoremA` and `TheoremB`.
-/

universe u

namespace CFSGOutside.KhukhroShumyatskyNonsolubleLength

open Subgroup CFSGOutside.NonsolubleLength

section Defs

variable {X : Type u} [Group X]

/-- A normal series `1 = G₀ ≤ G₁ ≤ ⋯ ≤ G_n = X` of `X` (each `G_i` normal in `X`) whose factors
`G_{i+1}/G_i` all satisfy `P`. -/
structure PaperSeries (X : Type u) [Group X] (P : Subgroup X → Subgroup X → Prop) where
  n : ℕ
  G : ℕ → Subgroup X
  normal : ∀ i ≤ n, (G i).Normal
  mono : ∀ i < n, G i ≤ G (i + 1)
  zero : G 0 = ⊥
  top : G n = ⊤
  factor : ∀ i < n, P (G i) (G (i + 1))

open Classical in
/-- The number of factors `G_{i+1}/G_i` of the series that do not satisfy `Q`. -/
noncomputable def PaperSeries.count {P : Subgroup X → Subgroup X → Prop} (s : PaperSeries X P)
    (Q : Subgroup X → Subgroup X → Prop) : ℕ :=
  ((Finset.range s.n).filter fun i => ¬ Q (s.G i) (s.G (i + 1))).card

/-- A factor that "either is soluble or is a direct product of nonabelian simple groups". -/
def SolOrSemisimple (A B : Subgroup X) : Prop := SolubleFactor A B ∨ SemisimpleFactor A B

/-- A factor that is a `2`-group or a `2'`-group. -/
def TwoOrOdd (A B : Subgroup X) : Prop := TwoGroupFactor A B ∨ OddOrderFactor A B

variable (X)

/-- **The paper's nonsoluble length** `λ(X)`: the minimum number of nonsoluble factors in a normal
series of `X` each of whose factors either is soluble or is a direct product of nonabelian simple
groups. -/
noncomputable def paperNonsolubleLength : ℕ :=
  sInf {k | ∃ s : PaperSeries X SolOrSemisimple, s.count SolubleFactor = k}

/-- **The paper's `2`-length**: the least number of `2`-factors (factors that are not
`2'`-groups) in a normal series each of whose factors is a `2`-group or a `2'`-group. -/
noncomputable def paperTwoLength : ℕ :=
  sInf {k | ∃ s : PaperSeries X TwoOrOdd, s.count OddOrderFactor = k}

/-- **`L₂(X)`**: the maximum `2`-length (in the paper's sense) of soluble subgroups of `X`. -/
noncomputable def paperMaxTwoLength : ℕ :=
  sSup {k | ∃ H : Subgroup X, Group.IsSolvable H ∧ paperTwoLength H = k}

end Defs

end CFSGOutside.KhukhroShumyatskyNonsolubleLength

namespace CFSGOutside.KhukhroShumyatskyNonsolubleLength

open CFSGOutside.NonPSolubleLength
open CFSGOutside.KhukhroShumyatskyNonsolubleLength (PaperSeries PaperSeries.count)

variable (p : ℕ) {X : Type u} [Group X]

/-- The section `B/A` is a `p`-group. -/
def PFactor (A B : Subgroup X) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, IsPGroup p (B ⧸ A.subgroupOf B)

/-- The section `B/A` is a `p'`-group. -/
def PPrimeFactor (A B : Subgroup X) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, Nat.Coprime (Nat.card (B ⧸ A.subgroupOf B)) p

/-- A factor that is a `p`-group or a `p'`-group. -/
def POrPPrime (A B : Subgroup X) : Prop := PFactor p A B ∨ PPrimeFactor p A B

variable (X) in
/-- **The paper's `p`-solubility**: a normal series each of whose factors is either a `p`-group
or a `p'`-group. -/
def paperPSoluble : Prop := Nonempty (PaperSeries X (POrPPrime p))

variable (X) in
/-- **The paper's `p`-length**: the least number of `p`-factors (factors that are not
`p'`-groups) in such a series. -/
noncomputable def paperPLength : ℕ :=
  sInf {k | ∃ s : PaperSeries X (POrPPrime p), s.count (PPrimeFactor p) = k}

variable (X) in
/-- The maximum `p`-length (paper's sense) of `p`-soluble subgroups of `X`. -/
noncomputable def paperMaxPLength : ℕ :=
  sSup {k | ∃ H : Subgroup X, paperPSoluble p H ∧ paperPLength p H = k}

/-- The section `B/A` is `p`-soluble (paper's sense). -/
def PSolFactor (A B : Subgroup X) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, paperPSoluble p (B ⧸ A.subgroupOf B)

/-- A factor that is either `p`-soluble or a direct product of nonabelian simple groups of order
divisible by `p`. -/
def PSolOrSemisimpleP (A B : Subgroup X) : Prop := PSolFactor p A B ∨ SemisimplePFactor p A B

variable (X) in
/-- **The paper's non-`p`-soluble length** `λ_p(X)`: the minimum number of non-`p`-soluble
factors in a normal series of `X` each of whose factors is `p`-soluble or a direct product of
nonabelian simple groups of order divisible by `p`. -/
noncomputable def paperNonPSolubleLength : ℕ :=
  sInf {k | ∃ s : PaperSeries X (PSolOrSemisimpleP p), s.count (PSolFactor p) = k}

end CFSGOutside.KhukhroShumyatskyNonsolubleLength
