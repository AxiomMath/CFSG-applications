import CFSGOutside.VanDamHaemersGD12.Compute

/-!
# The traces of `A^0, …, A^6` for the Tutte 12-cage, by kernel computation
-/

namespace CFSGOutside.VanDamHaemersGD12

/-- The trace of `A^k`: the number of closed walks of length `k`. -/
def traceW (k : ℕ) : ℕ := ((List.range 126).map fun v => (col v k).get v).sum

theorem traceW_0 : traceW 0 = 126 := by decide +kernel

theorem traceW_1 : traceW 1 = 0 := by decide +kernel

theorem traceW_2 : traceW 2 = 378 := by decide +kernel

theorem traceW_3 : traceW 3 = 0 := by decide +kernel

theorem traceW_4 : traceW 4 = 1890 := by decide +kernel

theorem traceW_5 : traceW 5 = 0 := by decide +kernel

theorem traceW_6 : traceW 6 = 10962 := by decide +kernel

end CFSGOutside.VanDamHaemersGD12
