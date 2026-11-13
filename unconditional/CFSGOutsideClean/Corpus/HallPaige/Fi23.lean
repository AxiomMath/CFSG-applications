import CFSG.Sporadic.Bridge.Fi23Surj
import CFSG.Sporadic.Fi23.Centralizer
import CFSG.Sporadic.Fi23.Fischer
import CFSG.Sporadic.Fi23.Setup
import CFSG.Sporadic.Fi23.Transposition
import CFSGOutside.Corpus.HallPaige.Fi23

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Fi23` assumes. -/

instance CFSGOutsideClean.Corpus.hpFi23Setup : CFSGOutside.Corpus.Fi23.Setup :=
  ⟨⟨CFSG.Sporadic.Fi23.matrixFacts.A_sq, CFSG.Sporadic.Fi23.matrixFacts.B_inv, CFSG.Sporadic.Fi23.matrixFacts.E_pow,
    CFSG.Sporadic.Fi23.matrixFacts.D_sq, CFSG.Sporadic.Fi23.matrixFacts.A_ne, CFSG.Sporadic.Fi23.matrixFacts.B_ne,
    CFSG.Sporadic.Fi23.matrixFacts.D_ne⟩⟩

instance CFSGOutsideClean.Corpus.hpFi23Theorems : CFSGOutside.Corpus.Fi23.Theorems :=
  ⟨CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv, CFSG.Sporadic.Fi23.f23_J, CFSG.Sporadic.Fi23.card_class_d, CFSG.Sporadic.Fi23.star_transitive⟩
