import Mathlib

/-!
# Copied corpus definitions: group order formulas `ordA`, `ordG2`, ...

Definitions copied verbatim from `CFSG/Open/Defs.lean` (lines 12 to 61) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus.Open`. The formula `ordRee` (line 56) is
in `CFSGOutside.Corpus.Defs.J1Models`.
-/

namespace CFSGOutside.Corpus.Open

/-- `|PSL(n+1, q)|`. Copy of `CFSG.Open.ordA`, `CFSG/Open/Defs.lean` line 12. -/
def ordA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1)) / Nat.gcd (n + 1) (q - 1)

/-- `|PSU(n+1, q)|`. Copy of `CFSG.Open.ordTwistedA`, `CFSG/Open/Defs.lean` line 15. -/
def ordTwistedA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - (-1 : ℤ) ^ i).toNat) /
    Nat.gcd (n + 1) (q + 1)

/-- Copy of `CFSG.Open.ordBC`, `CFSG/Open/Defs.lean` line 19. -/
def ordBC (n q : ℕ) : ℕ :=
  q ^ (n * n) * (∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)) / Nat.gcd 2 (q - 1)

/-- Copy of `CFSG.Open.ordD`, `CFSG/Open/Defs.lean` line 22. -/
def ordD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n - 1) * (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n - 1)

/-- Copy of `CFSG.Open.ordTwistedD`, `CFSG/Open/Defs.lean` line 26. -/
def ordTwistedD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n + 1) * (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n + 1)

/-- Copy of `CFSG.Open.ordG2`, `CFSG/Open/Defs.lean` line 49. -/
def ordG2 (q : ℕ) : ℕ := q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Copy of `CFSG.Open.ordTrialityD4`, `CFSG/Open/Defs.lean` line 51. -/
def ordTrialityD4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Copy of `CFSG.Open.ordSuzuki`, `CFSG/Open/Defs.lean` line 54. -/
def ordSuzuki (q : ℕ) : ℕ := q ^ 2 * (q ^ 2 + 1) * (q - 1)

end CFSGOutside.Corpus.Open
