import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator
import CFSGOutside.Corpus.MacWilliamsFourGenerator
import CFSGOutsideClean.Corpus.Defs.OpenVocabulary

/-! The corpus proves the statement that `CFSGOutside.Corpus.MacWilliamsFourGenerator` assumes. The copied
`IsElemAbelian` is `CFSG.Open.IsElemAbelian` by `Iff.rfl` (`CFSGOutsideClean.Corpus.Open.isElemAbelian_iff`). -/

instance CFSGOutsideClean.Corpus.macWilliamsFourGenerator :
    CFSGOutside.Corpus.MacWilliamsFourGenerator :=
  ⟨fun S _ _ hS hE => CFSG.Milestones.cls_connectivity_macwilliams_four_generator S hS hE⟩
