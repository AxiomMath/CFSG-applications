import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSGOutside.Corpus.ThompsonElementaryNormalPComplement
import CFSGOutsideClean.Corpus.Defs.ElemThompson

/-! The corpus proves the statement that `CFSGOutside.Corpus.ThompsonElementaryNormalPComplement` assumes. The
copied `HasNormalPComplement` is the corpus definition, and the copied `elemThompson` equals the corpus one
(`CFSGOutsideClean.Corpus.elemThompson_eq`). -/

universe u

instance CFSGOutsideClean.Corpus.thompsonElementaryNormalPComplement :
    CFSGOutside.Corpus.ThompsonElementaryNormalPComplement.{u} :=
  ⟨fun hp2 P hC hN => by
    rw [CFSGOutsideClean.Corpus.elemThompson_eq] at hN
    exact CFSG.RankThree.Coprime.thompson_elementary_normal_p_complement hp2 P hC hN⟩
