import CFSGOutside.VanDamHaemersGD12.CageSpectrum
import CFSGOutside.VanDamHaemers.Paper

/-!
# The collinearity graph of `GD(1,2)` is determined by its spectrum (fast path)

E. R. van Dam, W. H. Haemers, *Spectral characterizations of some distance-regular graphs*, J. Algebraic
Combin. 15 (2002) 189-202, Corollary 4 (p. 195), case `GD(1,2)`; the same graph is the row
`126 {[3]¹, [√6]²¹, [√2]²⁷, [0]²⁸, [-√2]²⁷, [-√6]²¹, [-3]¹}, d = 6, g = 12, GD(1,2)` of Table 4 of
van Dam-Haemers, *Which graphs are determined by their spectrum?*, Linear Algebra Appl. 373 (2003) 241-272.

The collinearity graph of the generalized dodecagon `GD(1,2)` is the incidence graph of a generalized hexagon
of order `2`: a connected cubic bipartite graph on `126` vertices in which every cycle has length at least `12`
(the Tutte 12-cage). Here:

* `cage_charpoly` (no corpus input): the explicit LCF graph `cage` has the Table 4 spectrum;
* `cage_moore` (no corpus input): `cage` is connected, cubic and bipartite on `126` vertices, with girth `≥ 12`;
* `charpoly_of_moore`: every such graph has the Table 4 spectrum;
* `gd12_determined_by_spectrum`: every graph cospectral with such a graph is isomorphic to it.

The last two are conditional on the Cohen-Tits uniqueness of the generalized hexagon of order two, stated as
the class `CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality`.
-/

namespace CFSGOutside.VanDamHaemersGD12

open Matrix CFSGOutside.VanDamHaemers

/-- Isomorphic graphs have the same adjacency characteristic polynomial. -/
lemma charpoly_eq_of_iso {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H) :
    (H.adjMatrix ℝ).charpoly = (G.adjMatrix ℝ).charpoly := by
  have : H.adjMatrix ℝ = Matrix.reindex f.toEquiv f.toEquiv (G.adjMatrix ℝ) := by
    ext i j
    simp only [reindex_apply, submatrix_apply, SimpleGraph.adjMatrix_apply]
    exact if_congr (f.symm.map_adj_iff (v := i) (w := j)).symm rfl rfl
  rw [this, charpoly_reindex]

/-- The Tutte 12-cage `cage` is a connected cubic bipartite graph on `126` vertices with every cycle of length
at least `12`, i.e. the incidence graph of a generalized hexagon of order `2`. No corpus input. -/
theorem cage_moore : Fintype.card (Fin 126) = 126 ∧ cage.Connected ∧ (∀ v, cage.degree v = 3) ∧
    Nonempty (cage.Coloring Bool) ∧ ∀ (v : Fin 126) (c : cage.Walk v v), c.IsCycle → 12 ≤ c.length :=
  moore_of_spectrum cage cage_charpoly

variable [CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.{0, 0}]

/-- A connected cubic bipartite graph on `126` vertices with every cycle of length at least `12` (the
collinearity graph of `GD(1,2)`) is isomorphic to `cage`. -/
theorem iso_cage_of_moore {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length) :
    Nonempty (T ≃g cage) := by
  obtain ⟨-, hconn', hdeg', ⟨col'⟩, hcyc'⟩ := cage_moore
  obtain ⟨-, -, f, -⟩ :=
    CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.order_two_generalized_hexagons_unique_up_to_duality
      T hcard hconn hdeg col hcyc cage (by simp) hconn' hdeg' col' hcyc'
  exact ⟨f⟩

/-- The collinearity graph of `GD(1,2)` has the spectrum of van Dam-Haemers (2003), Table 4: every connected
cubic bipartite graph on `126` vertices with every cycle of length at least `12` has adjacency characteristic
polynomial `(x - 3)(x + 3) x²⁸ (x² - 6)²¹ (x² - 2)²⁷`. -/
theorem charpoly_of_moore {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length) :
    (T.adjMatrix ℝ).charpoly = spectrumPoly := by
  obtain ⟨f⟩ := iso_cage_of_moore T hcard hconn hdeg col hcyc
  rw [← charpoly_eq_of_iso f, cage_charpoly]

/-- **van Dam-Haemers (2002), Corollary 4, case `GD(1,2)`.** The collinearity graph of the generalized
dodecagon `GD(1,2)` is determined by its spectrum: if `T` is a connected cubic bipartite graph on `126`
vertices with every cycle of length at least `12`, then every graph cospectral with `T` is isomorphic to
`T`. -/
theorem gd12_determined_by_spectrum {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hcard : Fintype.card V = 126) (hconn : T.Connected) (hdeg : ∀ v, T.degree v = 3)
    (col : T.Coloring Bool) (hcyc : ∀ (v : V) (c : T.Walk v v), c.IsCycle → 12 ≤ c.length)
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hcospec : (G.adjMatrix ℝ).charpoly = (T.adjMatrix ℝ).charpoly) : Nonempty (G ≃g T) :=
  determined_by_spectrum G T (hcospec.trans (charpoly_of_moore T hcard hconn hdeg col hcyc))
    (charpoly_of_moore T hcard hconn hdeg col hcyc)

/-- **Spectrum of the Tutte 12-cage.** The Tutte 12-cage is determined by its spectrum: every finite simple graph whose
adjacency matrix has characteristic polynomial (x − 3)(x + 3)x²⁸(x² − 6)²¹(x² − 2)²⁷ is isomorphic to it. Such a
graph has 126 vertices and is connected, 3-regular, bipartite and of girth at least 12.

Source: E. R. van Dam and W. H. Haemers, Which graphs are determined by their spectrum?, Linear Algebra Appl. 373
(2003), 241–272, Table 4, entry GD(1,2). https://doi.org/10.1016/S0024-3795(03)00483-X

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem cage_determined_by_spectrum {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hcospec : (G.adjMatrix ℝ).charpoly = (cage.adjMatrix ℝ).charpoly) :
    Nonempty (G ≃g cage) :=
  iso_of_cospectral G cage cage_charpoly hcospec

end CFSGOutside.VanDamHaemersGD12
