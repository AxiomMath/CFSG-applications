import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSGOutside.Corpus.AutAlternatingBijectiveConj

/-! The corpus proves the statement that `CFSGOutside.Corpus.AutAlternatingBijectiveConj` assumes. -/

instance CFSGOutsideClean.Corpus.autAlternatingBijectiveConj : CFSGOutside.Corpus.AutAlternatingBijectiveConj :=
  ⟨fun n hn hn6 => CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6⟩
