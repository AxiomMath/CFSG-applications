import CFSGOutside.VanDamHaemersGD12.Defs

/-!
# Walk counts in the Tutte 12-cage, by kernel computation

This file counts the walks of the Tutte 12-cage `cage` of `Defs.lean`, storing each column of `A^k` in a binary
tree of depth `7` so that the kernel shares the work, and checks
`A^7 + 84 A^3 = 17 A^5 + 108 A` and the traces of `A^0, …, A^6`.
-/

namespace CFSGOutside.VanDamHaemersGD12

/-- A complete binary tree of natural numbers, read by the binary digits of an index. -/
inductive Tr
  | leaf : ℕ → Tr
  | node : Tr → Tr → Tr

/-- The entry at index `n`. -/
def Tr.get : Tr → ℕ → ℕ
  | .leaf z, _ => z
  | .node l r, n => if n % 2 = 0 then l.get (n / 2) else r.get (n / 2)

/-- The tree of depth `d` holding `f 0, …, f (2^d - 1)`. -/
def build : ℕ → (ℕ → ℕ) → Tr
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (build d fun n => f (2 * n)) (build d fun n => f (2 * n + 1))

lemma get_build (d : ℕ) (f : ℕ → ℕ) (n : ℕ) (hn : n < 2 ^ d) : (build d f).get n = f n := by
  induction d generalizing f n with
  | zero => simp at hn; subst hn; rfl
  | succ d ih =>
    simp only [build, Tr.get]
    split_ifs with h
    · rw [ih _ _ (by rw [pow_succ] at hn; omega)]; congr 1; omega
    · rw [ih _ _ (by rw [pow_succ] at hn; omega)]; congr 1; omega

/-- One multiplication by the adjacency matrix. -/
def step (t : Tr) : Tr := build 7 fun i => t.get (nxt i) + t.get (prv i) + t.get (chord i)

/-- The number of walks of length `k` from `i` to `v`. -/
def walks : ℕ → ℕ → ℕ → ℕ
  | 0, v, i => if i = v then 1 else 0
  | k + 1, v, i => walks k v (nxt i) + walks k v (prv i) + walks k v (chord i)

/-- The column of `A^k` at `v`, as a tree. -/
def col (v : ℕ) : ℕ → Tr
  | 0 => build 7 fun i => if i = v then 1 else 0
  | k + 1 => step (col v k)

lemma col_get (v k i : ℕ) (hi : i < 126) : (col v k).get i = walks k v i := by
  induction k generalizing i with
  | zero => rw [col, get_build _ _ _ (by omega)]; rfl
  | succ k ih =>
    rw [col, step, get_build _ _ _ (by omega), ih _ (lt_nxt i), ih _ (lt_prv i), ih _ (lt_chord i)]
    rfl

/-- The check at one vertex `v`: `A^7 + 84 A^3 = 17 A^5 + 108 A` on column `v`. -/
def colOK (v : ℕ) : Bool :=
  let t1 := col v 1
  let t3 := step (step t1)
  let t5 := step (step t3)
  let t7 := step (step t5)
  (List.range 126).all fun i => t7.get i + 84 * t3.get i == 17 * t5.get i + 108 * t1.get i

lemma colOK_eq (v : ℕ) : colOK v = (List.range 126).all fun i =>
    (col v 7).get i + 84 * (col v 3).get i == 17 * (col v 5).get i + 108 * (col v 1).get i := rfl

theorem colOK_all : (List.range 126).all colOK = true := by decide +kernel

end CFSGOutside.VanDamHaemersGD12
