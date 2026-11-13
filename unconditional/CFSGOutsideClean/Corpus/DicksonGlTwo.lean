import CFSG.RankThree.SubgroupLists.DicksonGL2
import CFSGOutside.Corpus.DicksonGlTwo
import CFSGOutsideClean.Corpus.Defs.ClassicalModel

/-!
The corpus proves the statement that `CFSGOutside.Corpus.DicksonGlTwo` assumes. The copy
`CFSGOutside.Corpus.Open.StatedSL` agrees with the corpus `StatedSL` by `rfl`
(`CFSGOutsideClean.Corpus.Open.statedSL_eq`).
-/

instance CFSGOutsideClean.Corpus.dicksonGlTwo : CFSGOutside.Corpus.DicksonGlTwo :=
  ⟨fun {_} _ H hpH => CFSG.RankThree.SubgroupLists.dickson_gl_two H hpH⟩
