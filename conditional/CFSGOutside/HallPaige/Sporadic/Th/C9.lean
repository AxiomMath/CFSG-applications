import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 9. -/
theorem chk9 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 9 (wY 9))) (U0 dempData) (wC 9) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
