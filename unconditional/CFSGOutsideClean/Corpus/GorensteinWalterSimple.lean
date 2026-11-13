import CFSG.Dihedral.GorensteinWalter
import CFSGOutside.Corpus.GorensteinWalterSimple

/-! The corpus proves the statement that `CFSGOutside.Corpus.GorensteinWalterSimple` assumes. -/

instance CFSGOutsideClean.Corpus.gorensteinWalterSimple : CFSGOutside.Corpus.GorensteinWalterSimple :=
  ⟨fun G _ _ _ h P hd => CFSG.GorensteinWalter.gorenstein_walter G h P hd⟩
