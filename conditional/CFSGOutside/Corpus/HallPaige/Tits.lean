import Mathlib.Combinatorics.Quiver.Schreier
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.GroupAction.Defs
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Corpus input for the Tits group `²F₄(2)'`

The corpus permutation model `titsD ≤ Perm (Fin 1755)` of the Tits group, the data it is built
from, and the packed form `TitsText.F` of the same data, all copied verbatim from AxiomMath/CFSG
@ 69cb972 (the data file `results_conditional/CFSGOutside/Corpus/HallPaige/Data/tits-perm1755.txt` is a byte-for-byte copy of
`Certificates/Data/CFSGNative/TitsSchreier/tits-perm1755.txt`). The corpus theorems used are
stated as classes whose fields are the corpus statements.
-/

namespace CFSGOutside.Corpus.Tits

open Lean Elab Command

/-! ### Generic corpus definitions -/

/-- Corpus: `CFSG.Monster.B.Co2.Native.hexVal`,
Certificates/Data/CFSGNative/MonsterB/Co2Data.lean:7. -/
@[inline] def hexVal (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

/-- Corpus: `CFSG.Monster.B.Co2.Native.hexAt`,
Certificates/Data/CFSGNative/MonsterB/Co2Data.lean:10. -/
def hexAt (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => hexAt b o w * 16 + hexVal (b.get! (o + w))

/-- Corpus: `CFSG.Monster.B.Co2.Rep`, CFSG/Monster/B/Co2/PermArr.lean:62. -/
def Rep (n : ℕ) (t : Array ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, t[(x : ℕ)]! = g x

open scoped _root_.Classical in
/-- Corpus: `CFSG.Monster.B.Co2.permOfArr`, CFSG/Monster/B/Co2/PermArr.lean:105. -/
@[irreducible] noncomputable def permOfArr (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j then
    Equiv.ofBijective (fun i : Fin n => (⟨t[(i : ℕ)]!, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (congrArg Fin.val hij)))
  else 1

/-- Corpus: `CFSG.Certificates.SchreierLetter`, CFSG/Certificates/SchreierChainData.lean:10. -/
abbrev SchreierLetter (j : ℕ) := Fin j × Bool

/-- Corpus: `CFSG.Monster.B.Co2.toLetters`, CFSG/Monster/B/Co2/PermArr.lean:138. -/
def toLetters (j : ℕ) (w : List ℤ) : List (SchreierLetter j) :=
  w.filterMap fun l =>
    if h : l ≠ 0 ∧ l.natAbs ≤ j then some (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) else none

section Words

variable {G : Type*} [Group G]

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.wordIn`, CFSG/Sporadic/Schreier/TitsBasic.lean:21. -/
def wordIn (k : ℕ) (gs : ℕ → G) (w : List ℤ) : G :=
  Quiver.SchreierGraph.evalWord (fun h : Fin k => gs h) (toLetters k w)

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.tcomm`, CFSG/Sporadic/Schreier/TitsBasic.lean:24. -/
def tcomm (x y : G) : G := x⁻¹ * y⁻¹ * x * y

end Words

/-- Corpus: `CFSG.KS.mask`, Certificates/Data/Kernel/Spor/Chain.lean:11. -/
noncomputable def mask (w : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

/-- Corpus: `CFSG.KC.Enum.pg`, CFSG/Certificates/Kernel/Enum/Defs.lean:34 (`fld(p, w * i, m)`
unfolds to `Nat.land (Nat.shiftRight p (Nat.mul w i)) m`). -/
noncomputable def pg (w m p i : Nat) : Nat := Nat.land (Nat.shiftRight p (Nat.mul w i)) m

/-- Corpus: `CFSG.KS.Raw.unpack`, CFSG/Certificates/Kernel/Spor/RawDefs.lean:12. -/
noncomputable def unpack (n w P : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => pg w (mask w) P i.val

/-! ### The Tits data -/

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsPerm1755Text`,
CFSG/Sporadic/Schreier/TitsData.lean:7. -/
def titsPerm1755Text : String :=
  include_str "Data"/"tits-perm1755.txt"

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsDerivedComm`,
CFSG/Sporadic/Schreier/TitsData.lean:25. -/
def titsDerivedComm : List (List Int × List Int) :=
  [([-3, 4, -4, -1, 4, 1, 1, -4, -2],
    [-4, 2, -2, 1, -3, 3, -2, -4, 3]),
   ([-2, -1, 1, -2, -1, -3, 4, 3, -1],
    [3, -2, 2, -2, 2, 2, 1, -3, -3])]

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsHWords`, CFSG/Sporadic/Schreier/TitsData.lean:75. -/
def titsHWords : List (List Int) :=
  [[3], [4], [13]]

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsBytes1755`,
CFSG/Sporadic/Schreier/TitsArrays.lean:13. -/
def titsBytes1755 : ByteArray := titsPerm1755Text.toUTF8

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsArr1755`,
CFSG/Sporadic/Schreier/TitsArrays.lean:21. -/
@[irreducible] def titsArr1755 (L : Nat) : Array Nat :=
  Array.ofFn (n := 1755) fun i => hexAt titsBytes1755 (3 * (1755 * L + i.val)) 3

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsField1755`,
CFSG/Sporadic/Schreier/TitsArrays.lean:30. -/
def titsField1755 (L₀ m : Nat) : Array (Array Nat) :=
  Array.ofFn (n := m) fun j => titsArr1755 (L₀ + j.val)

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsGenArrs`,
CFSG/Sporadic/Schreier/TitsArrays.lean:33. -/
def titsGenArrs : Array (Array Nat) := titsField1755 0 4

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsDerivedArrs`,
CFSG/Sporadic/Schreier/TitsArrays.lean:37. -/
def titsDerivedArrs : Array (Array Nat) := titsField1755 18 13

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsU`,
CFSG/Sporadic/Schreier/TitsCertCheckInputs.lean:22. -/
def titsU (j : ℕ) : List ℤ := (titsDerivedComm.getD j ([], [])).1

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsV`,
CFSG/Sporadic/Schreier/TitsCertCheckInputs.lean:24. -/
def titsV (j : ℕ) : List ℤ := (titsDerivedComm.getD j ([], [])).2

/-! ### The permutation model -/

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsGen`, CFSG/Sporadic/Schreier/TitsCert.lean:13. -/
noncomputable def titsGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsGenArrs[i]!

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsDGen`, CFSG/Sporadic/Schreier/TitsCert.lean:18. -/
noncomputable def titsDGen (j : ℕ) : Equiv.Perm (Fin 1755) :=
  tcomm (wordIn 4 titsGen (titsU j)) (wordIn 4 titsGen (titsV j))

/-- The corpus model of the Tits group `²F₄(2)'` on 1755 points.
Corpus: `CFSG.Sporadic.Schreier.Tits.titsD`, CFSG/Sporadic/Schreier/TitsCert.lean:21. -/
noncomputable def titsD : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun j : Fin 2 => titsDGen j)

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsT`, CFSG/Sporadic/Schreier/TitsCert.lean:60. -/
noncomputable def titsT (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsDerivedArrs[i]!

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsWordGroup`, CFSG/Sporadic/Schreier/TitsLocal.lean:32. -/
noncomputable def titsWordGroup (ws : List (List ℤ)) : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure {g | ∃ w ∈ ws, wordIn 13 titsT w = g}

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsH`, CFSG/Sporadic/Schreier/TitsLocal.lean:35. -/
noncomputable def titsH : Subgroup (Equiv.Perm (Fin 1755)) := titsWordGroup titsHWords

/-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsPointStab`, CFSG/Sporadic/Schreier/TitsStab.lean:257. -/
noncomputable abbrev titsPointStab : Subgroup titsD :=
  (MulAction.stabilizer (Equiv.Perm (Fin 1755)) (0 : Fin 1755)).comap titsD.subtype

/-- Corpus: `CFSG.LieType.SeitzGeneration.Cat`, CFSG/LieType/SeitzGeneration/Defs.lean:12. -/
abbrev Cat (d : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie d).Group

/-! ### The packed table `TitsText.F`

Corpus: `CertificateChecks.KernelMisc.TitsText.F`, generated in
Certificates/Kernel/Misc/Tits/Text.lean:16 by `#kmisc_hexflat … titsPerm1755Text 3 1755 11 96`
(Certificates/Kernel/Misc/Perm/HexCmd.lean:14) through `CFSG.KS.RawGen.addTree`
(Certificates/Kernel/Sporadic/RawGen.lean) and `CFSG.KC.Tab.table`
(CFSG/Certificates/Kernel/Common/Tab.lean). The generator below is that code (the part producing
`F`), so `F` is the same declaration. -/

namespace Tab

/-- Corpus: `CFSG.KC.Tab.natT`. -/
def natT (_ : Unit := ()) : Expr := mkConst ``Nat
/-- Corpus: `CFSG.KC.Tab.fnT`. -/
def fnT (_ : Unit := ()) : Expr := mkForall `i .default natT natT
/-- Corpus: `CFSG.KC.Tab.lit`. -/
def lit (n : Nat) : Expr := mkRawNatLit n

/-- Corpus: `CFSG.KC.Tab.node`. -/
def node (l r : Expr) (t : Nat) : Expr :=
  let motive := mkLambda `_ .default (mkConst ``Bool) fnT
  let i := mkBVar 0
  mkLambda `i .default natT
    (mkAppN (mkConst ``Bool.rec [Level.one]) #[motive, l, r, mkApp2 (mkConst ``Nat.ble) (lit t) i, i])

/-- Corpus: `CFSG.KC.Tab.tree`. -/
partial def tree (leaf : Nat → Expr) (lo size base : Nat) : Expr :=
  if size == 1 then leaf lo
  else
    let h := size / 2
    node (tree leaf lo h base) (tree leaf (lo + h) h base) ((lo + h) <<< base)

/-- Corpus: `CFSG.KC.Tab.table`. -/
def table (leaf : Nat → Expr) (size base : Nat) : Expr :=
  if size == 1 then leaf 0
  else
    mkLambda `i .default natT (mkApp (tree leaf 0 size base)
      (mkApp2 (mkConst ``Nat.land) (mkBVar 0) (lit ((size <<< base) - 1))))

/-- Corpus: `CFSG.KC.Tab.constFn`. -/
def constFn (e : Expr) : Expr := mkLambda `i .default natT e

/-- Corpus: `CFSG.KC.Tab.addDef`. -/
def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

/-- Corpus: `CFSG.KS.RawGen.addTree`. -/
def addTree (F : Name) (vs : Array Nat) : CoreM Unit := do
  let cnt := max vs.size 1
  let h := Nat.log2 (2 * cnt - 1)
  addDef (F ++ `Z) natT (lit 0)
  for k in [0:vs.size] do
    addDef (F ++ Name.mkSimple s!"L{k}") natT (lit vs[k]!)
  let leaf := fun k => constFn (if k < vs.size then mkConst (F ++ Name.mkSimple s!"L{k}")
    else mkConst (F ++ `Z))
  addDef F fnT (table leaf (1 <<< h) 0)

end Tab

open Tab in
/-- The `F`-generating part of the corpus command `#kmisc_hexflat`. -/
elab "#hp_hexflat_F " pre:ident sId:ident dd:num nn:num ww:num cn:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let N := cn.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size < d * n * N then throwError "#kmisc_hexflat: {b.size} bytes, expected {d * n * N}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl (fun a t => a * 16 + hv (b.get! (d * (n * j.val + i) + t))) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `F) vals

#hp_hexflat_F CFSGOutside.Corpus.Tits.TitsText CFSGOutside.Corpus.Tits.titsPerm1755Text 3 1755 11 96

/-! ### Corpus theorems -/

/-- Corpus theorems about the permutation model of the Tits group `²F₄(2)'`. -/
class Theorems : Prop where
  /-- The corpus model is isomorphic to the TauCeti Tits group.
  Corpus: `CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat`,
  CFSG/HardMathSupport/Dickson/LocalTwoBalance/Cross/TitsAux/Cat.lean:19. -/
  nonempty_mulEquiv_titsD_cat (hv : TauCeti.LieTypeIndex.tits.Valid) :
    Nonempty (Cat ⟨.tits, hv⟩ ≃* titsD)
  /-- The point stabilizer of `0` in `titsD` is `titsH`.
  Corpus: `CFSG.Sporadic.Schreier.Tits.titsH_eq_stab`, CFSG/Sporadic/Schreier/TitsStab.lean:357. -/
  titsH_eq_stab :
    titsH = titsPointStab.map titsD.subtype
  /-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsT_mem_titsD`,
  CFSG/Sporadic/Schreier/TitsCert.lean:256. -/
  titsT_mem_titsD {i : ℕ} (hi : i < 13) : titsT i ∈ titsD
  /-- Corpus: `CFSG.Sporadic.Schreier.Tits.titsT_rep`, CFSG/Sporadic/Schreier/TitsStab.lean:12. -/
  titsT_rep
    {i : ℕ} (hi : i < 13) : Rep 1755 titsDerivedArrs[i]! (titsT i)
  /-- Corpus: `CertificateChecks.KernelMisc.TitsText.titsDerivedArrs_get`,
  Certificates/Kernel/Misc/Tits/Text.lean:32. -/
  titsDerivedArrs_get {j : Nat} (hj : j < 13) :
    titsDerivedArrs[j]! = unpack 1755 11 (TitsText.F (18 + j))

end CFSGOutside.Corpus.Tits
