import CFSG.Goldschmidt.Steps.GoldType
import CFSGOutside.Corpus.ElementaryOfClauses
import CFSGOutsideClean.Corpus.Defs.J1Models

/-! The corpus proves the statement that `CFSGOutside.Corpus.ElementaryOfClauses` assumes. -/

instance CFSGOutsideClean.Corpus.elementaryOfClauses : CFSGOutside.Corpus.ElementaryOfClauses :=
  ⟨fun {_ _ _ _} hK T => CFSG.Goldschmidt.GoldType.elementary_of_clauses hK T⟩
