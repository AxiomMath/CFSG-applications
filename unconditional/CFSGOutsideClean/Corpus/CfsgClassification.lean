import Comparator.Solution
import CFSGOutside.Corpus.CfsgClassification

/-! The corpus proves the statement that `CFSGOutside.Corpus.CfsgClassification` assumes, as
`CFSGComparator.classification`. -/

instance CFSGOutsideClean.Corpus.cfsgClassification : CFSGOutside.Corpus.CfsgClassification :=
  ⟨fun G _ _ _ => TauCeti.classificationStatement_iff.1 CFSGComparator.classification.{0} G⟩
