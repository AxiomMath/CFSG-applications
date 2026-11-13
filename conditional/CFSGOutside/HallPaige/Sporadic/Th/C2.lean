import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 2. -/
theorem chk2 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 2 (wY 2))) (U0 dempData) (wC 2) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
