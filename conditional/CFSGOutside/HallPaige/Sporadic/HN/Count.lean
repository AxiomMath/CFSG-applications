import CFSGOutside.HallPaige.Sporadic.PermKitF

/-!
# Orbit counts in blocks

`CFSGOutside.HallPaige.PermKit.countLt p n` recurses `n` deep, which is too deep for the kernel when `n` is
over a million. For `n = K * B` we count in `K` blocks of length `B`, so that the recursion depth
is at most `B`.
-/

namespace CFSGOutside.HallPaige.Sporadic.HNCount

open CFSGOutside.HallPaige.PermKit

theorem countLt_add (p : ℕ → Bool) (a b : ℕ) :
    countLt p (a + b) = countLt (fun i => p (a + i)) b + countLt p a := by
  induction b with
  | zero => simp [countLt]
  | succ b ih =>
    have h1 : countLt p (a + (b + 1)) = (if p (a + b) = true then 1 else 0) + countLt p (a + b) := rfl
    have h2 : countLt (fun i => p (a + i)) (b + 1) =
        (if p (a + b) = true then 1 else 0) + countLt (fun i => p (a + i)) b := rfl
    rw [h1, h2, ih]
    omega

/-- The sum of the counts over the first `K` blocks of length `B`. -/
def blockSum (p : ℕ → Bool) (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => blockSum p B K + countLt (fun i => p (K * B + i)) B

theorem countLt_mul (p : ℕ → Bool) (B : ℕ) : ∀ K, countLt p (K * B) = blockSum p B K := by
  intro K
  induction K with
  | zero => simp [countLt, blockSum]
  | succ K ih =>
    rw [Nat.succ_mul, countLt_add, ih]
    simp only [blockSum]
    omega

theorem countOK_of_blockSum (c : CFSGOutside.HallPaige.PermKitF.Cert) (i : ℕ) {B K : ℕ} (hn : c.n = K * B)
    (h : Nat.ble (c.levels.getD i default).m
      (blockSum (fun x => !Nat.beq ((c.levels.getD i default).F.dep x) 0) B K) = true) :
    c.countOK i = true := by
  unfold CFSGOutside.HallPaige.PermKitF.Cert.countOK
  rw [hn, countLt_mul]
  exact h

end CFSGOutside.HallPaige.Sporadic.HNCount
