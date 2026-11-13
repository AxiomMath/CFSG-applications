import Mathlib
import CFSGOutside.WittDesigns.AutS5612.Transitive

/-!
# Kernel checks for the hexads of `S(5,6,12)`

The 132 hexads are the images of one 6-set under `M12` (found by machine, checked by kernel evaluation).
Subsets of `Fin 12` are handled through their bit masks, so that kernel evaluation works on plain numbers.
Every 5-set lies in exactly one hexad, and the generators of `M12` permute the hexads.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm

@[irreducible] def hexMasks : List ℕ :=
  [123, 189, 215, 238, 287, 365, 374, 423, 442, 459, 476, 497, 567, 591, 636, 670, 683, 729, 741, 754, 814, 825, 853, 858, 867, 909, 915, 948, 966, 1000, 1071, 1118, 1141, 1179, 1206, 1229, 1251, 1272, 1331, 1340, 1351, 1369, 1386, 1422, 1429, 1449, 1490, 1508, 1565, 1594, 1619, 1638, 1641, 1671, 1708, 1713, 1738, 1748, 1803, 1814, 1829, 1868, 1904, 1944, 1954, 1985, 2110, 2141, 2151, 2191, 2227, 2266, 2281, 2292, 2347, 2357, 2382, 2387, 2424, 2454, 2457, 2476, 2501, 2530, 2587, 2605, 2646, 2666, 2673, 2709, 2726, 2744, 2755, 2764, 2823, 2844, 2866, 2889, 2916, 2954, 2977, 3024, 3095, 3129, 3147, 3180, 3186, 3228, 3237, 3242, 3270, 3281, 3341, 3354, 3366, 3412, 3425, 3459, 3504, 3528, 3598, 3619, 3636, 3653, 3672, 3721, 3730, 3808, 3857, 3880, 3906, 3972]

def maskSet (m : ℕ) : Finset (Fin 12) := Finset.univ.filter fun i => m.testBit i.val

@[irreducible] def hexads : Finset (Finset (Fin 12)) := (hexMasks.map maskSet).toFinset

def permCheck (g : Equiv.Perm (Fin 12)) : Bool :=
  hexMasks.all fun m => hexMasks.any fun m2 => decide (g • maskSet m = maskSet m2)



def threeCycle : Equiv.Perm (Fin 12) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem hexMasks_card : ∀ m ∈ hexMasks, (maskSet m).card = 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem steiner_check : ∀ m < 4096, (maskSet m).card = 5 →
    (hexMasks.filter fun m2 => maskSet m ⊆ maskSet m2).length = 1 := by decide +kernel
theorem permCheck_a : permCheck m12gA = true := by decide +kernel
theorem permCheck_b : permCheck m12gB = true := by decide +kernel
theorem threeCycle_moves : ∀ m2 ∈ hexMasks, threeCycle • maskSet 123 ≠ maskSet m2 := by decide +kernel

end CFSGOutside.WittDesigns.Witt5612
