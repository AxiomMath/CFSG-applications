import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 8. -/
theorem chk8 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 8 (wY 8))) (U0 dempData) (wC 8) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
