import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy

/-! The corpus proves the statement that `CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy` assumes. -/

instance CFSGOutsideClean.Corpus.sl2MinimalFaithfulZsigmondy :
    CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy :=
  ⟨@CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one⟩
