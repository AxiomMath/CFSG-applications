import CFSG.Quasithin.Background.A1cTransfer
import CFSGOutside.Corpus.ThompsonTransferLemma
import CFSGOutsideClean.Corpus.Defs.PResidual

/-! The corpus proves the statement that `CFSGOutside.Corpus.ThompsonTransferLemma` assumes. The copied
`pResidual` is the corpus definition by `rfl`. -/

universe u

instance CFSGOutsideClean.Corpus.thompsonTransferLemma : CFSGOutside.Corpus.ThompsonTransferLemma.{u} :=
  ⟨fun P _ hQP hidx _ hu hQu => CFSG.Quasithin.thompson_transfer_lemma P hQP hidx hu hQu⟩
