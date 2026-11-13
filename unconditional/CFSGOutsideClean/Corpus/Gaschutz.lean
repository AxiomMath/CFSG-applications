import CFSG.Quasithin.Background.A1cTransfer
import CFSGOutside.Corpus.Gaschutz

/-! The corpus proves the statement that `CFSGOutside.Corpus.Gaschutz` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.gaschutz : CFSGOutside.Corpus.Gaschutz.{u} :=
  ⟨@CFSG.Quasithin.gaschutz⟩
