import CFSGOutside.HallPaige.Sporadic.Th.Defs

namespace CFSGOutside.HallPaige.Th

open CFSGOutside.Corpus.Th.KC.ThDemp CFSGOutside.Corpus.Th.KernelThDemp

/-- The cube witness of suborbit 3. -/
theorem chk3 : combChk (2 ^ 248 - 1) (blk (U0 dempData) (cubeMats 3 (wY 3))) (U0 dempData) (wC 3) =
    true := by decide +kernel

end CFSGOutside.HallPaige.Th
