import CFSGOutside.WittDesigns.S5824.Main
import CFSGOutside.WittDesigns.S4723.Main
import CFSGOutside.WittDesigns.S5612.Main
import CFSGOutside.WittDesigns.AutS5824.Main
import CFSGOutside.WittDesigns.AutS4723.Main
import CFSGOutside.WittDesigns.AutS5612.Main
import CFSGOutside.WittDesigns.M24FiveTransitive.Main
import CFSGOutside.WittDesigns.M24FiveTransitive.Four
import CFSGOutside.WittDesigns.M24FiveTransitive.Classification

/-!
# Witt's designs: uniqueness, automorphism groups and multiple transitivity

E. Witt, "Über Steinersche Systeme" and "Die 5-fach transitiven Gruppen von Mathieu", Abh. Math. Sem. Univ.
Hamburg 12 (1938), 256–275.

The Steiner systems `S(5,8,24)`, `S(4,7,23)` and `S(5,6,12)` are unique up to isomorphism, their automorphism
groups have the orders of `M24`, `M23` and `M12`, and these groups are 5-, 4- and sharply 5-transitive. The
headline theorems are

* `CFSGOutside.WittDesigns.Witt5824.witt_S5824_unique`,
* `CFSGOutside.WittDesigns.Witt4723.witt_S4723_unique`,
* `CFSGOutside.WittDesigns.Witt5612.witt_S5612_unique`,
* `CFSGOutside.WittDesigns.Aut5824.card_aut_S5824`,
* `CFSGOutside.WittDesigns.Aut4723.card_aut_S4723`,
* `CFSGOutside.WittDesigns.M24Five.aut_S5824_five_transitive`,
* `CFSGOutside.WittDesigns.M24Four.aut_S4723_four_transitive`,
* `CFSGOutside.WittDesigns.Witt5612.aut_hexads_sharply_five_transitive`.

The uniqueness of `S(5,8,24)` and `S(4,7,23)` reduces to Witt's uniqueness of the derived `S(3,6,22)`, the
`G22` code of `CFSGOutside.PlessSloaneG22`, and counting. The orders and the transitivity of the `M12` case use the
classification of 5-transitive groups of degree at most 80. Conditional on the corpus inputs stated as classes
in `CFSGOutside.Corpus`.
-/
