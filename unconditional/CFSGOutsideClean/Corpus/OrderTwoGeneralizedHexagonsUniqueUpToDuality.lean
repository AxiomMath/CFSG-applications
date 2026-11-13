import CFSG.Combinatorics.HexagonUniqueDuality
import CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality

/-! The corpus proves the statement that `CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality`
assumes. -/

universe u u'

instance CFSGOutsideClean.Corpus.orderTwoGeneralizedHexagonsUniqueUpToDuality :
    CFSGOutside.Corpus.OrderTwoGeneralizedHexagonsUniqueUpToDuality.{u, u'} :=
  ⟨@CFSG.Combinatorics.HexagonUniqueDuality.order_two_generalized_hexagons_unique_up_to_duality⟩
