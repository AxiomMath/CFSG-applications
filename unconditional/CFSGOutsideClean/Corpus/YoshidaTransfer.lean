import CFSG.RankThree.Transfer.Control
import CFSGOutside.Corpus.YoshidaTransfer

/-! The corpus proves the statement that `CFSGOutside.Corpus.YoshidaTransfer` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.yoshidaTransfer : CFSGOutside.Corpus.YoshidaTransfer.{u} :=
  ⟨@CFSG.RankThree.Transfer.inf_commutator_eq_inf_map_commutator_normalizer.{u}⟩
