import Mathlib

/-!
# The spectrum of the Tutte 12-cage

E. R. van Dam, W. H. Haemers, *Which graphs are determined by their spectrum?*, Linear Algebra Appl. 373 (2003)
241-272, Table 4 (entry `GD(1,2)`, `n = 126`) and Theorem 9(i).
-/

namespace CFSGOutside.VanDamHaemers

open Polynomial

/-- The adjacency spectrum of the Tutte 12-cage (the incidence graph of the generalized hexagon
of order 2): `3¹, (±√6)²¹, (±√2)²⁷, 0²⁸, (-3)¹` (van Dam-Haemers, Linear Algebra Appl. 373 (2003),
Table 4, entry `GD(1,2)`). -/
noncomputable def tutteSpectrum : Multiset ℝ :=
  {3, -3} + Multiset.replicate 28 0 + Multiset.replicate 21 (Real.sqrt 6) +
    Multiset.replicate 21 (-Real.sqrt 6) + Multiset.replicate 27 (Real.sqrt 2) +
    Multiset.replicate 27 (-Real.sqrt 2)

/-- The characteristic polynomial with spectrum `tutteSpectrum`, namely
`(x - 3)(x + 3) x²⁸ (x² - 6)²¹ (x² - 2)²⁷` (van Dam-Haemers, Table 4, entry `GD(1,2)`). -/
noncomputable def spectrumPoly : ℝ[X] := (tutteSpectrum.map fun a => X - C a).prod

end CFSGOutside.VanDamHaemers
