import CFSG.Blueprint.Catalog
import CFSG.Quasithin.Background.A3StructureDefs
import CFSGOutside.Corpus.Defs.Suzuki

/-! The Suzuki group definitions copied into `CFSGOutside.Corpus.Defs.Suzuki` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem suzukiN_eq (a : ℕ) {K : Type} [Field K] (u v : K) :
    CFSGOutside.Corpus.suzukiN a u v = CFSG.Blueprint.suzukiN a u v :=
  rfl

theorem suzukiS_eq (a : ℕ) {K : Type} [Field K] (u v : K) :
    CFSGOutside.Corpus.suzukiS a u v = CFSG.Blueprint.suzukiS a u v :=
  rfl

theorem suzukiD_eq (a : ℕ) {K : Type} [Field K] (l : Kˣ) :
    CFSGOutside.Corpus.suzukiD a l = CFSG.Blueprint.suzukiD a l :=
  rfl

theorem suzukiW_eq (K : Type) [Field K] :
    CFSGOutside.Corpus.suzukiW K = CFSG.Blueprint.suzukiW K :=
  rfl

theorem suzukiGroup_eq (a : ℕ) (K : Type) [Field K] :
    CFSGOutside.Corpus.suzukiGroup a K = CFSG.Blueprint.suzukiGroup a K :=
  rfl

theorem suzukiModel_eq (G : Type) [Group G] (p f : ℕ) :
    CFSGOutside.Corpus.SuzukiModel G p f = CFSG.Blueprint.SuzukiModel G p f :=
  rfl

theorem isSz_eq (e : ℕ) (X : Type) [Group X] :
    CFSGOutside.Corpus.IsSz e X = CFSG.Quasithin.IsSz e X :=
  rfl

end CFSGOutsideClean.Corpus
