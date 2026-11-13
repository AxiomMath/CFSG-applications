import CFSG.Sporadic.Mathieu.M22
import CFSGOutside.Corpus.M22Simple
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.M22Simple` assumes. -/

instance CFSGOutsideClean.Corpus.m22Simple : CFSGOutside.Corpus.M22Simple :=
  ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity⟩
