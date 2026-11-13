import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.HallPaige.DoubleCosets
import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Sporadic.Mathieu
import CFSGOutside.HallPaige.Sporadic.Tits
import CFSGOutside.HallPaige.Sporadic.Co1
import CFSGOutside.HallPaige.Sporadic.Fi23
import CFSGOutside.Corpus.HallPaige.SporadicSimple
import CFSGOutside.HallPaige.Sporadic.ONan
import CFSGOutside.HallPaige.Sporadic.Fi24Prime
import CFSGOutside.HallPaige.Sporadic.HN
import CFSGOutside.HallPaige.Sporadic.J2
import CFSGOutside.HallPaige.Sporadic.HS
import CFSGOutside.HallPaige.Sporadic.J1
import CFSGOutside.HallPaige.Sporadic.J3
import CFSGOutside.HallPaige.Sporadic.He
import CFSGOutside.HallPaige.Sporadic.McL
import CFSGOutside.HallPaige.Sporadic.Co3
import CFSGOutside.HallPaige.Sporadic.Co2
import CFSGOutside.HallPaige.Sporadic.Fi22
import CFSGOutside.HallPaige.Sporadic.Ru
import CFSGOutside.HallPaige.Sporadic.Suz
import CFSGOutside.HallPaige.Sporadic.Ly
import CFSGOutside.HallPaige.Sporadic.J4
import CFSGOutside.HallPaige.Sporadic.Th
import CFSGOutside.HallPaige.Sporadic.B
import CFSGOutside.HallPaige.Sporadic.M

/-!
# Sporadic and Tits catalogue cases from permutation labellings
-/

namespace CFSGOutside.HallPaige

open TauCeti

section
variable [h0 : Corpus.Simple]
include h0

/-- A permutation labelling gives the minimal-counterexample step. -/
theorem catalogueCase_of_permLabelling {i : CFSGIndex} [Finite i.Group]
    (h : PermLabelling i.Group) : CatalogueCase i := fun _ hP =>
  hasCompleteMapping_of_wilcoxCriterion cosetStatement (wilcoxCriterion_of_permLabelling h) hP

end

theorem finite_of_nonempty_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : Nonempty (G ≃* H)) : Finite H :=
  Finite.of_equiv G (Classical.choice e).toEquiv

section
variable [h0 : Corpus.Mathieu.Bridges] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_M11 : CatalogueCase (.sporadic .M11) :=
  haveI := finite_of_nonempty_mulEquiv Corpus.Mathieu.Bridges.m11_nonempty_mulEquiv
  catalogueCase_of_permLabelling permLabelling_M11
theorem catalogueCase_M12 : CatalogueCase (.sporadic .M12) :=
  haveI := finite_of_nonempty_mulEquiv Corpus.Mathieu.Bridges.m12_nonempty_mulEquiv
  catalogueCase_of_permLabelling permLabelling_M12
theorem catalogueCase_M22 : CatalogueCase (.sporadic .M22) :=
  haveI := finite_of_nonempty_mulEquiv Corpus.Mathieu.Bridges.m22_nonempty_mulEquiv
  catalogueCase_of_permLabelling permLabelling_M22
theorem catalogueCase_M23 : CatalogueCase (.sporadic .M23) :=
  haveI := finite_of_nonempty_mulEquiv Corpus.Mathieu.Bridges.m23_nonempty_mulEquiv
  catalogueCase_of_permLabelling permLabelling_M23
theorem catalogueCase_M24 : CatalogueCase (.sporadic .M24) :=
  haveI := finite_of_nonempty_mulEquiv Corpus.Mathieu.Bridges.m24_nonempty_mulEquiv
  catalogueCase_of_permLabelling permLabelling_M24

end

section
variable [h0 : Corpus.Simple] [h1 : Corpus.Tits.Theorems]
include h0 h1

theorem catalogueCase_tits (hv : LieTypeIndex.tits.Valid) : CatalogueCase (.lie ⟨.tits, hv⟩) :=
  haveI : Finite (Corpus.Tits.Cat ⟨.tits, hv⟩) :=
    Finite.of_equiv _ (Classical.choice (Corpus.Tits.Theorems.nonempty_mulEquiv_titsD_cat hv)).symm.toEquiv
  catalogueCase_of_permLabelling (permLabelling_tits hv)

end

section
variable [h0 : Corpus.Simple]
include h0

/-- A Wilcox criterion gives the minimal-counterexample step. -/
theorem catalogueCase_of_wilcoxCriterion {i : CFSGIndex} [Finite i.Group]
    (h : WilcoxCriterion i.Group) : CatalogueCase i := fun _ hP =>
  hasCompleteMapping_of_wilcoxCriterion cosetStatement h hP

instance (s : SporadicName) : Finite (CFSGIndex.sporadic s).Group :=
  (Corpus.Simple.fam_sporadic_converse_tauCeti s).1

end

section
variable [h0 : Corpus.Co1.Orbits] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Co1 : CatalogueCase (.sporadic .Co1) :=
  catalogueCase_of_wilcoxCriterion Co1.wilcoxCriterion

end
section
variable [h0 : Corpus.Fi23.Setup] [h1 : Corpus.Fi23.Theorems] [h2 : Corpus.Simple]
include h0 h1 h2

theorem catalogueCase_Fi23 : CatalogueCase (.sporadic .Fi23) :=
  catalogueCase_of_wilcoxCriterion Fi23.wilcoxCriterion

end

section
variable [h0 : Corpus.McL.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_McL : CatalogueCase (.sporadic .McL) :=
  catalogueCase_of_permLabelling Sporadic.McL.permLabelling

end
section
variable [h0 : Corpus.Co3.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Co3 : CatalogueCase (.sporadic .Co3) :=
  catalogueCase_of_permLabelling Sporadic.Co3.permLabelling

end
section
variable [h0 : Corpus.Co2.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Co2 : CatalogueCase (.sporadic .Co2) :=
  catalogueCase_of_permLabelling Sporadic.Co2.permLabelling

end
section
variable [h0 : Corpus.Fi22.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Fi22 : CatalogueCase (.sporadic .Fi22) :=
  catalogueCase_of_permLabelling Sporadic.Fi22.permLabelling

end
section
variable [h0 : Corpus.Ru.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Ru : CatalogueCase (.sporadic .Ru) :=
  catalogueCase_of_permLabelling Sporadic.Ru.permLabelling

end
section
variable [h0 : Corpus.Simple] [h1 : Corpus.Suz.FiniteCardLe]
include h0 h1

theorem catalogueCase_Suz : CatalogueCase (.sporadic .Suz) :=
  catalogueCase_of_permLabelling Sporadic.Suz.permLabelling

end

section
variable [h0 : Corpus.Simple]
include h0

theorem catalogueCase_J2 : CatalogueCase (.sporadic .J2) :=
  catalogueCase_of_permLabelling SporadicJ2.permLabelling
theorem catalogueCase_HS : CatalogueCase (.sporadic .HS) :=
  catalogueCase_of_permLabelling SporadicHS.permLabelling
theorem catalogueCase_J1 : CatalogueCase (.sporadic .J1) :=
  catalogueCase_of_permLabelling SporadicJ1.permLabelling

end
section
variable [h0 : Corpus.Bounds] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_J3 : CatalogueCase (.sporadic .J3) :=
  catalogueCase_of_permLabelling SporadicJ3.permLabelling
theorem catalogueCase_He : CatalogueCase (.sporadic .He) :=
  catalogueCase_of_permLabelling SporadicHe.permLabelling

end

section
variable [h0 : Corpus.ONan.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_ONan : CatalogueCase (.sporadic .ONan) :=
  catalogueCase_of_permLabelling Sporadic.ONan.permLabelling

end

section
variable [h0 : Corpus.Fi24Prime.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_Fi24Prime : CatalogueCase (.sporadic .Fi24Prime) :=
  catalogueCase_of_permLabelling Sporadic.Fi24Prime.permLabelling

end

section
variable [h0 : Corpus.HN.FiniteCardLe] [h1 : Corpus.Simple]
include h0 h1

theorem catalogueCase_HN : CatalogueCase (.sporadic .HN) :=
  catalogueCase_of_permLabelling Sporadic.HN.permLabelling

end

end CFSGOutside.HallPaige
