import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Basic definitions for Guralnick–Shumyatsky (2001)

R. Guralnick and P. Shumyatsky, *Derived subgroups of fixed points*, Israel J. Math. 126 (2001), 345–362,
DOI 10.1007/BF02784161.

We work inside a finite ambient group `X`: `G` and `A` are subgroups of `X`, `A` normalizes `G`
(so `A` acts on `G` by conjugation), `A` is an elementary abelian `q`-group and `q ∤ |G|`. This is the
semidirect product `G ⋊ A` of an action of `A` on `G`.
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

export CFSGOutside.Corpus.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {X : Type*} [Group X]

/-- The centralizer `C_H(a) = H ∩ C_X(a)` of an element `a` in a subgroup `H` (Guralnick–Shumyatsky,
Section 1). -/
def cen (H : Subgroup X) (a : X) : Subgroup X := H ⊓ centralizer ({a} : Set X)

/-- The centralizer `C_H(Y) = H ∩ C_X(Y)` of a subgroup `Y` in a subgroup `H` (Guralnick–Shumyatsky,
Section 2). -/
def cenS (H Y : Subgroup X) : Subgroup X := H ⊓ centralizer (Y : Set X)

/-- `A` is an elementary abelian `q`-group acting coprimely (by conjugation) on `G`, as in the hypotheses of
Guralnick–Shumyatsky, Theorems 1.1 and 1.4. Together with `Nat.card A = q ^ 3` this says that `A` is
elementary abelian of order `q³`. -/
structure CopAct (q : ℕ) (G A : Subgroup X) : Prop where
  prime : q.Prime
  norm : A ≤ normalizer (G : Set X)
  coprime : ¬ q ∣ Nat.card G
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  exp : ∀ a ∈ A, a ^ q = 1

/-- `Y ≤ A` with `A/Y` cyclic (`A = Y⟨g⟩` for some `g ∈ A`); used in Guralnick–Shumyatsky,
Lemma 2.2. -/
def CycQuot (A Y : Subgroup X) : Prop := Y ≤ A ∧ ∃ g ∈ A, A ≤ Y ⊔ zpowers g

/-- The subgroup `⟨P ∩ C_G(a)' | 1 ≠ a ∈ A⟩`, the right-hand side of Guralnick–Shumyatsky,
Theorem 3.1. -/
def gens (P G A : Subgroup X) : Subgroup X :=
  ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), P ⊓ ⁅cen G a, cen G a⁆

end CFSGOutside.GuralnickShumyatsky
