import CFSGOutside.VanDamHaemers.GirthSpec
import CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality

/-!
# The Tutte 12-cage is determined by its spectrum (fast path)

E. R. van Dam, W. H. Haemers, *Which graphs are determined by their spectrum?*, Linear Algebra Appl. 373 (2003)
241-272, Table 4 (entry `GD(1,2)`, from Theorem 9(i)): the incidence graph of the generalized hexagon of order
`2` (the Tutte 12-cage, `126` vertices, spectrum `3¹, (±√6)²¹, (±√2)²⁷, 0²⁸, (-3)¹`) is determined by its
adjacency spectrum. Conditional on the Cohen-Tits uniqueness of the generalized hexagon of order two, stated as
a class in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.VanDamHaemers

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph with the adjacency spectrum of the Tutte 12-cage has `126` vertices, is connected,
cubic and bipartite, and has girth at least `12` (van Dam-Haemers, Linear Algebra Appl. 373 (2003),
Table 4, entry `GD(1,2)`). -/
theorem moore_of_spectrum (hspec : (G.adjMatrix ℝ).charpoly = spectrumPoly) :
    Fintype.card V = 126 ∧ G.Connected ∧ (∀ v, G.degree v = 3) ∧ Nonempty (G.Coloring Bool) ∧
      ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length :=
  ⟨card_eq G hspec, connected G hspec, degree_eq_three G hspec, nonempty_coloring G hspec,
    cycle_length_ge G hspec (degree_eq_three G hspec)⟩

/-- **van Dam-Haemers, Table 4, `GD(1,2)` (Theorem 9(i)).** The Tutte 12-cage is determined by
its spectrum: any two graphs whose adjacency matrices have the characteristic polynomial
`(x - 3)(x + 3) x²⁸ (x² - 6)²¹ (x² - 2)²⁷` are isomorphic. -/
theorem determined_by_spectrum [CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.{0, 0}]
    {V' : Type} [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V')
    [DecidableRel G'.Adj] (hspec : (G.adjMatrix ℝ).charpoly = spectrumPoly)
    (hspec' : (G'.adjMatrix ℝ).charpoly = spectrumPoly) : Nonempty (G ≃g G') := by
  obtain ⟨hcard, hconn, hdeg, ⟨col⟩, hcyc⟩ := moore_of_spectrum G hspec
  obtain ⟨hcard', hconn', hdeg', ⟨col'⟩, hcyc'⟩ := moore_of_spectrum G' hspec'
  obtain ⟨-, -, f, -⟩ :=
    CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.order_two_generalized_hexagons_unique_up_to_duality
      G hcard hconn hdeg col hcyc G' hcard' hconn' hdeg' col' hcyc'
  exact ⟨f⟩

/-- The same, phrased with cospectrality (van Dam-Haemers, Table 4, `GD(1,2)`): a graph cospectral with a
graph `T` that has the spectrum of the Tutte 12-cage is isomorphic to `T`. -/
theorem iso_of_cospectral [CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.{0, 0}]
    {V' : Type} [Fintype V'] [DecidableEq V'] (T : SimpleGraph V')
    [DecidableRel T.Adj] (hT : (T.adjMatrix ℝ).charpoly = spectrumPoly)
    (hcospec : (G.adjMatrix ℝ).charpoly = (T.adjMatrix ℝ).charpoly) : Nonempty (G ≃g T) :=
  determined_by_spectrum G T (hcospec.trans hT) hT

end CFSGOutside.VanDamHaemers
