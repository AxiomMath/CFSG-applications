import CFSG.Holt.TwoGroups
import CFSGOutside.Corpus.HoltAtMostOneInvolution
import CFSGOutsideClean.Corpus.Defs.TwoGroupShapes

/-! The corpus proves the statement that `CFSGOutside.Corpus.HoltAtMostOneInvolution` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.holtAtMostOneInvolution :
    CFSGOutside.Corpus.HoltAtMostOneInvolution.{u} :=
  ⟨@CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution.{u}⟩
