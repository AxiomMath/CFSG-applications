import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 7. -/
theorem chk7 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 7 (wY 7))) (U0 dempData) (wC 7) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
