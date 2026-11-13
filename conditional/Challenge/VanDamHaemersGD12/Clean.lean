import CFSGOutside.VanDamHaemers.Defs
import CFSGOutside.VanDamHaemersGD12.Defs

/-!
# The collinearity graph of `GD(1,2)` is determined by its spectrum

E. R. van Dam, W. H. Haemers, *Spectral characterizations of some distance-regular graphs*, J. Algebraic
Combin. 15 (2002) 189-202, Corollary 4, case `GD(1,2)`; van Dam-Haemers, *Which graphs are determined by
their spectrum?*, Linear Algebra Appl. 373 (2003) 241-272, Table 4, row `GD(1,2)`.
-/

namespace CFSGOutsideClean.VanDamHaemersGD12

open CFSGOutside.VanDamHaemers CFSGOutside.VanDamHaemersGD12

/-- The Tutte 12-cage has the spectrum of van Dam-Haemers (2003), Table 4, row `GD(1,2)`. -/
theorem cage_charpoly : (cage.adjMatrix ℝ).charpoly = spectrumPoly := sorry

/-- The Tutte 12-cage is a connected cubic bipartite graph on `126` vertices with girth `≥ 12`. -/
theorem cage_moore : Fintype.card (Fin 126) = 126 ∧ cage.Connected ∧ (∀ v, cage.degree v = 3) ∧
    Nonempty (cage.Coloring Bool) ∧ ∀ (v : Fin 126) (c : cage.Walk v v), c.IsCycle → 12 ≤ c.length := sorry

/-- A connected cubic bipartite graph on `126` vertices with girth `≥ 12` is isomorphic to `cage`. -/
theorem iso_cage_of_moore {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length) :
    Nonempty (T ≃g cage) := sorry

/-- Every connected cubic bipartite graph on `126` vertices with girth `≥ 12` has the Table 4 spectrum. -/
theorem charpoly_of_moore {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length) :
    (T.adjMatrix ℝ).charpoly = spectrumPoly := sorry

/-- **van Dam-Haemers (2002), Corollary 4, case `GD(1,2)`.** Every graph cospectral with a connected cubic
bipartite graph `T` on `126` vertices with girth `≥ 12` is isomorphic to `T`. -/
theorem gd12_determined_by_spectrum {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length)
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hcospec : (G.adjMatrix ℝ).charpoly = (T.adjMatrix ℝ).charpoly) : Nonempty (G ≃g T) := sorry

/-- Every graph cospectral with the Tutte 12-cage `cage` is isomorphic to it. -/
theorem cage_determined_by_spectrum {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hcospec : (G.adjMatrix ℝ).charpoly = (cage.adjMatrix ℝ).charpoly) :
    Nonempty (G ≃g cage) := sorry

end CFSGOutsideClean.VanDamHaemersGD12
