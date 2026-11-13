import Mathlib

/-!
# Arad, Theorem B(iii): definitions

Z. Arad, *π-homogeneity and π′-closure of finite groups*, Pacific J. Math. 51 (1974), 1–9, p. 1.

* an element is a *π-element* if its order is divisible only by primes in `π`; a group is a *π-group* if its
  order is divisible only by primes in `π`; `π′` is the set of primes not in `π`;
* `G` is *π-closed* if the π-elements of `G` form a subgroup;
* `G` is *π-homogeneous* if `N_G(H)/C_G(H)` is a π-group for every nonidentity π-subgroup `H` of `G`.
-/

namespace CFSGOutside.Arad

variable {G : Type*} [Group G]

/-- `H` is a π-group: every prime divisor of `|H|` lies in `π` (Arad 1974, p. 1). -/
def IsPiGroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p ∈ π

/-- `g` is a π′-element: no prime divisor of the order of `g` lies in `π` (Arad 1974, p. 1). -/
def IsPiPrimeElement (π : Set ℕ) (g : G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ orderOf g → p ∉ π

/-- `G` is π′-closed: the π′-elements of `G` form a subgroup (Arad 1974, p. 1). -/
def IsPiPrimeClosed (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∃ K : Subgroup G, ∀ g : G, g ∈ K ↔ IsPiPrimeElement π g

/-- `G` is π-homogeneous: `N_G(H)/C_G(H)` is a π-group for every nonidentity π-subgroup `H` of `G`
(Arad 1974, p. 1). The order of `N_G(H)/C_G(H)` is the number of cosets of `C_G(H) ∩ N_G(H)` in `N_G(H)`. -/
def IsPiHomogeneous (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H ≠ ⊥ → IsPiGroup π H →
    ∀ p : ℕ, p.Prime →
      p ∣ Nat.card (Subgroup.normalizer (H : Set G) ⧸
        (Subgroup.centralizer (H : Set G)).subgroupOf (Subgroup.normalizer (H : Set G))) → p ∈ π

/-- The Sylow `2`-subgroups of `G` are dihedral or abelian (Arad 1974, Theorem B(iii)). `DihedralGroup 2` is the
four-group. -/
def SylowTwoDihedralOrAbelian (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) ∨
    ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)

/-! Working notions used in the proof. -/

/-- A weak form of π-homogeneity, enough for the proof: an `s`-element (`s ∉ π`) that normalizes a nonidentity
`r`-subgroup (`r ∈ π`) centralizes it. -/
def HomP (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ r : ℕ, r.Prime → r ∈ π → ∀ H : Subgroup G, H ≠ ⊥ → IsPGroup r H →
    ∀ s : ℕ, s.Prime → s ∉ π → ∀ x ∈ Subgroup.normalizer (H : Set G), (∃ k : ℕ, x ^ (s ^ k) = 1) →
      x ∈ Subgroup.centralizer (H : Set G)

/-- A witness against `HomP`: a nonidentity `r`-subgroup normalized but not centralized by an `s`-element. -/
def Bad (G : Type*) [Group G] (r s : ℕ) : Prop :=
  ∃ H : Subgroup G, H ≠ ⊥ ∧ IsPGroup r H ∧
    ∃ x ∈ Subgroup.normalizer (H : Set G), x ∉ Subgroup.centralizer (H : Set G) ∧ ∃ k : ℕ, x ^ (s ^ k) = 1

/-- Every prime of `π` dividing `|M|` is contradicted by some `Bad M r s` with `r ∈ π`, `s ∉ π`. -/
def ModelBad (M : Type*) [Group M] : Prop :=
  ∀ π : Set ℕ, 2 ∉ π → ∀ p : ℕ, p.Prime → p ∈ π → p ∣ Nat.card M →
    ∃ r s : ℕ, r.Prime ∧ r ∈ π ∧ s.Prime ∧ s ∉ π ∧ Bad M r s

end CFSGOutside.Arad
