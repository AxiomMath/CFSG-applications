import CFSG.Quasithin.Background.F918Z8Op4d
import CFSGOutside.Corpus.Opq4dExistsMulEquivSuzukiMatrixGroup

/-! The corpus proves the statement that `CFSGOutside.Corpus.Opq4dExistsMulEquivSuzukiMatrixGroup` assumes. -/

instance CFSGOutsideClean.Corpus.opq4dExistsMulEquivSuzukiMatrixGroup :
    CFSGOutside.Corpus.Opq4dExistsMulEquivSuzukiMatrixGroup :=
  ⟨fun hX => CFSG.Quasithin.opq4d_exists_mulEquiv_suzukiMatrixGroup hX⟩
