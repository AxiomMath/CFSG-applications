import Mathlib

namespace CFSGOutside.Sutherland

theorem perm5_pow (σ : Equiv.Perm (Fin 5)) (h : Equiv.Perm.sign σ = 1) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  revert σ
  decide +kernel

end CFSGOutside.Sutherland
