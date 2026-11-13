import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 6. -/
theorem chk6 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 6 (wY 6))) (U0 dempData) (wC 6) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
