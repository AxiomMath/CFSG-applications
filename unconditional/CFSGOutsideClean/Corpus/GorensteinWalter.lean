import CFSG.Dihedral.GorensteinWalter
import CFSGOutside.Corpus.GorensteinWalter

/-! The corpus proves the statement that `CFSGOutside.Corpus.GorensteinWalter` assumes. -/

instance CFSGOutsideClean.Corpus.gorensteinWalter : CFSGOutside.Corpus.GorensteinWalter :=
  ⟨CFSG.GorensteinWalter.gorenstein_walter⟩
