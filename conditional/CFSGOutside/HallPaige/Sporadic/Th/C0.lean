import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 0. -/
theorem chk0 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 0 (wY 0))) (U0 dempData) (wC 0) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
