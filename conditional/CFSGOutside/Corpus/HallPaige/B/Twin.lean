import Lean

/-!
# Computing the corpus matrices of the Baby Monster at elaboration time

A copy of the corpus evaluators that compute the 4370-dimensional matrices of the corpus `B` model from
the two seed files (AxiomMath/CFSG @ 69cb972):

* `CFSG/Certificates/Kernel/Common/Eval.lean` (`#kc_eval`: reading a matrix stored as a constant,
  adding the results as constants);
* `CFSG/Certificates/Kernel/BabyMonster/Twin.lean` (`natWords`, `natOfWords`, `transpose64`,
  `rowsOfStrips`, `stripsOfRows`, `spreadMask`, `mulStrips`, `invRows`, `stripBytes`, `prod`, `inv`);
* `CFSG/Certificates/Kernel/BabyMonster/TwinDy.lean` (`rep`, `rowBytes`, `stripsOf`);
* `CFSG/Certificates/Kernel/BabyMonster/TwinRank.lean` (`rankCert`, `rank`, `polyMul`, `compact8`,
  `textRows`);
* `CFSG/Certificates/Kernel/BabyMonster/Load.lean` (`#bm_text`: the seed text read in 69 blocks).

The corpus runs one `#kc_eval` per product and adds every intermediate matrix as a constant. Here the
command `#hpb_eval` runs a list of such steps in one go and adds only the matrices named after `emit`;
every step result is checked against the size and hash the corpus pins for it (`0 0` means no pin, for
matrices that are not corpus data). A matrix `M` is added as in the corpus: `M.s0, …, M.s68 : ℕ` (the
69 strips) and `M : List ℕ := [M.s0, …, M.s68]`.

The values are only computed here. Every fact about them used later is either a corpus theorem (a class
field, `Corpus/HallPaige/B.lean`) or a kernel check (`Sporadic/B/`).
-/

open Lean Elab Command Meta

namespace CFSGOutside.Corpus.B.Twin

/-! ### `Twin.lean` -/

partial def natWords (x nw : Nat) : Array UInt64 :=
  if nw ≤ 1 then #[x.toUInt64]
  else
    let h := nw / 2
    natWords (x % (1 <<< (64 * h))) h ++ natWords (x >>> (64 * h)) (nw - h)

partial def natOfWords (ws : Array UInt64) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then (if lo < hi then ws[lo]!.toNat else 0)
  else
    let mid := (lo + hi) / 2
    natOfWords ws lo mid ||| (natOfWords ws mid hi <<< (64 * (mid - lo)))

def transpose64 (a : Array UInt64) : Array UInt64 := Id.run do
  let mut a := a
  let mut w : Nat := 32
  let mut m : UInt64 := 0x00000000FFFFFFFF
  while w > 0 do
    for i in [0:64] do
      if i &&& w == 0 then
        let x := a[i]!
        let y := a[i + w]!
        let t := ((x >>> w.toUInt64) ^^^ y) &&& m
        a := a.set! (i + w) (y ^^^ t)
        a := a.set! i (x ^^^ (t <<< w.toUInt64))
    w := w / 2
    m := m ^^^ (m <<< w.toUInt64)
  return a

def rowsOfStrips (n : Nat) (S : Array Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let mut rows : Array Nat := Array.mkEmpty n
  for s in [0:nb] do
    let ws := natWords S[s]! n
    let mut rw : Array (Array UInt64) := Array.replicate 64 (Array.replicate nb 0)
    for c in [0:nb] do
      let blk := (Array.range 64).map fun j => if 64 * c + j < n then ws[64 * c + j]! else 0
      let tb := transpose64 blk
      for t in [0:64] do
        rw := rw.modify t (·.set! c tb[t]!)
    for t in [0:min 64 (n - 64 * s)] do
      rows := rows.push (natOfWords rw[t]! 0 nb)
  return rows

def stripsOfRows (n : Nat) (R : Array Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let mut S : Array Nat := Array.mkEmpty nb
  for s in [0:nb] do
    let rw := (Array.range 64).map fun t =>
      if 64 * s + t < n then natWords R[64 * s + t]! nb else Array.replicate nb 0
    let mut ws : Array UInt64 := Array.replicate (64 * nb) 0
    for c in [0:nb] do
      let tb := transpose64 ((Array.range 64).map fun t => rw[t]![c]!)
      for j in [0:64] do
        ws := ws.set! (64 * c + j) tb[j]!
    S := S.push (natOfWords ws 0 n)
  return S

def spreadMask (n : Nat) : Nat := ((1 <<< (64 * n)) - 1) / 18446744073709551615

def mulStrips (n : Nat) (A B : Array Nat) : Array Nat := Id.run do
  let S := spreadMask n
  let ws := A.map (natWords · n)
  let mut C : Array Nat := Array.replicate A.size 0
  for k in [0:n] do
    let sp := (B[k / 64]! >>> (k % 64)) &&& S
    for s in [0:A.size] do
      let w := ws[s]![k]!
      if w != 0 then C := C.modify s (· ^^^ (w.toNat * sp))
  return C

def invRows (n : Nat) (R : Array Nat) : Option (Array Nat) := Id.run do
  let mut Z : Array Nat := (Array.range n).map fun i => R[i]! ||| (1 <<< (n + i))
  for c in [0:n] do
    let mut p := c
    while p < n && (Z[p]! >>> c) &&& 1 == 0 do
      p := p + 1
    if p == n then return none
    let zp := Z[p]!
    Z := (Z.set! p Z[c]!).set! c zp
    for i in [0:n] do
      if i != c && (Z[i]! >>> c) &&& 1 == 1 then
        Z := Z.set! i (Z[i]! ^^^ zp)
  return some (Z.map (· >>> n))

def stripBytes (n : Nat) (S : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (S.size * 8 * n)
  for x in S do
    for w in natWords x n do
      for i in [0:8] do
        b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

/-! ### `TwinDy.lean` -/

def rep (x p c : Nat) : Nat := x * (((1 <<< (p * c)) - 1) / ((1 <<< p) - 1))

def rowBytes (R : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (R.size * 552)
  for x in R do
    for w in natWords x 69 do
      for i in [0:8] do
        b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

/-! ### `TwinRank.lean` -/

def rankCert (n : Nat) (M : Array Nat) : Option (Array Nat) := Id.run do
  let mut m := M
  let mut p : Array Nat := (Array.range n).map (1 <<< ·)
  let mut r := 0
  for c in [0:n] do
    let col := n - 1 - c
    let mut piv := r
    while piv < n && !m[piv]!.testBit col do
      piv := piv + 1
    if piv < n then
      let mr := m[piv]!
      let pr := p[piv]!
      m := (m.set! piv m[r]!).set! r mr
      p := (p.set! piv p[r]!).set! r pr
      for i in [r + 1:n] do
        if m[i]!.testBit col then
          m := m.modify i (· ^^^ mr)
          p := p.modify i (· ^^^ pr)
      r := r + 1
  let mut q := r
  for c in [0:n] do
    let col := n - 1 - c
    if q < n then
      let mut piv := q
      while piv < n && !p[piv]!.testBit col do
        piv := piv + 1
      if piv < n then
        let pq := p[piv]!
        p := (p.set! piv p[q]!).set! q pq
        for i in [q + 1:n] do
          if p[i]!.testBit col then
            p := p.modify i (· ^^^ pq)
        q := q + 1
  if q != n then return none
  return some p

/-- The corpus `Twin.rank` with coefficients `[1, 1]`: a rank certificate `P` for `1 + X`. -/
def rankOnePlus (n : Nat) (X : Array Nat) : Option (Array Nat) :=
  let R := rowsOfStrips n X
  let M := (Array.range n).map fun i => (1 <<< i) ^^^ R[i]!
  (rankCert n M).map (stripsOfRows n)

/-- The corpus `Twin.polyMul` with coefficients `[1, 1]`: `P * (1 + X)`. -/
def polyMulOnePlus (n : Nat) (P X : Array Nat) : Array Nat :=
  let PX := mulStrips n P X
  (Array.range P.size).map fun s => P[s]! ^^^ PX[s]!

def compact8 (x : Nat) : Nat := Id.run do
  let mut x := x
  let mut g := 1
  while g ≤ 4096 do
    let K := rep ((1 <<< g) - 1) (16 * g) (65536 / (16 * g) + 1)
    x := (x &&& K) ||| ((x >>> (7 * g)) &&& (K <<< g))
    g := 2 * g
  return x

def textRows (T : Array Nat) : Except String (Array Nat) := do
  let n := 4370
  unless T.size == 69 do throw s!"textRows: {T.size} blocks"
  let digit0 := rep 48 8 n
  let low := rep 254 8 n
  let mut R : Array Nat := Array.mkEmpty n
  for s in [0:69] do
    let m := min 64 (n - 64 * s)
    unless T[s]! >>> (35400 * m) == 0 do throw s!"block {s}: more than {m} rows"
    for t in [0:m] do
      let r := (T[s]! >>> (35400 * t)) &&& ((1 <<< 35400) - 1)
      let mut x := 0
      for l in [0:55] do
        let len := if l < 54 then 80 else 50
        unless (r >>> (8 * (81 * l + len))) &&& 255 == 10 do
          throw s!"row {64 * s + t}: line {l} not ended by a newline"
        x := x ||| (((r >>> (648 * l)) &&& ((1 <<< (8 * len)) - 1)) <<< (640 * l))
      let y := x ^^^ digit0
      unless y &&& low == 0 do throw s!"row {64 * s + t}: a byte is not a digit 0 or 1"
      R := R.push (compact8 y)
  return R

/-! ### `Load.lean` -/

partial def natLE (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 8 then
    Id.run do
      let mut acc := 0
      for k in [0:hi - lo] do
        acc := acc + (b[lo + k]!.toNat <<< (8 * k))
      return acc
  else
    let mid := lo + (hi - lo) / 2
    natLE b lo mid + (natLE b mid hi <<< (8 * (mid - lo)))

/-- The 69 blocks of a seed text file, as `#bm_text` reads them (`t0, …, t68`). -/
def textBlocks (b : ByteArray) : Except String (Array Nat) := do
  let N := 4370
  unless b.size == 21 + 4425 * N do throw s!"text file of size {b.size}"
  return (Array.range 69).map fun s =>
    natLE b (21 + 4425 * 64 * s) (21 + 4425 * min N (64 * (s + 1)))

/-! ### Reading and adding matrices (`Eval.lean`) -/

partial def readNat (e : Expr) : CoreM Nat := do
  match e with
  | .lit (.natVal v) => return v
  | .const n _ =>
    match (← getConstInfo n).value? (allowOpaque := true) with
    | some v => readNat v
    | none => throwError "#hpb_eval: {n} has no value"
  | .mdata _ e => readNat e
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then readNat (e.getArg! 1)
    else throwError "#hpb_eval: cannot read {e}"

/-- The strips of a matrix stored as a constant `M := [M.s0, …]`. -/
partial def readStrips (n : Name) : CoreM (Array Nat) := do
  let some v := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "#hpb_eval: {n} has no value"
  let mut e := v
  let mut xs : Array Nat := #[]
  repeat
    if e.isAppOfArity ``List.cons 3 then
      xs := xs.push (← readNat (e.getArg! 1))
      e := e.getArg! 2
    else if e.isAppOfArity ``List.nil 1 then
      break
    else
      throwError "#hpb_eval: {n} is not a list of strips"
  unless xs.size == 69 do throwError "#hpb_eval: {n} has {xs.size} strips"
  return xs

def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

def addMatrix (M : Name) (S : Array Nat) : CoreM Unit := do
  let natE := mkConst ``Nat
  let mut cs : Array Expr := #[]
  for s in [0:S.size] do
    let nm := M ++ Name.mkSimple s!"s{s}"
    addDef nm natE (mkRawNatLit S[s]!)
    cs := cs.push (mkConst nm)
  let lst := cs.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) natE e acc)
    (mkApp (mkConst ``List.nil [0]) natE)
  addDef M (mkApp (mkConst ``List [0]) natE) lst

def checkPin (what : String) (b : ByteArray) (size hash : Nat) : Except String Unit := do
  if size != 0 then
    unless b.size == size && b.hash.toNat == hash do
      throw s!"{what}: size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"

/-- Read a file next to the current file, checking its pinned size and hash. -/
def readPinned (rel : String) (size hash : Nat) : CommandElabM ByteArray := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let path := dir / rel
  let b ← IO.FS.readBinFile path
  unless b.size == size && b.hash.toNat == hash do
    throwError "data file {path}: size {b.size} hash {b.hash.toNat}, pinned {size} {hash}"
  return b

end CFSGOutside.Corpus.B.Twin

open CFSGOutside.Corpus.B.Twin in
/-- `#hpb_eval pre "steps" emit M₁ … Mₖ` runs the steps (one per line, names relative to `pre`):

* `text M path fileSize fileHash rowsHash stripsHash`: the seed text file `path` (relative to the
  current file), read as by `#bm_text`, then `Twin.textRows` and `Twin.stripsOf`;
* `prod M size hash A B₁ … Bₖ`: `Twin.prod`, the product `A * B₁ * ⋯ * Bₖ`;
* `inv M size hash A`: `Twin.inv`;
* `rank M size hash A`: `Twin.rank` with coefficients `1 1` (a rank certificate for `1 + A`);
* `poly M size hash P A`: `Twin.polyMul` with coefficients `1 1` (`P * (1 + A)`);

checking each result against its pin, and adds the matrices `M₁ … Mₖ` as constants `pre.Mᵢ`. A name
not produced by an earlier step is read from the environment (relative to `pre` if that exists). -/
elab "#hpb_eval " pre:ident steps:str " emit " outs:ident* : command => do
  let P := pre.getId
  let n := 4370
  let lines := (steps.getString.splitOn "\n").map (fun l => (l.splitOn " ").filter (· ≠ ""))
    |>.filter (· ≠ [])
  let mut env : Std.HashMap Name (Array Nat) := {}
  let t0 ← IO.monoMsNow
  let rd (env : Std.HashMap Name (Array Nat)) (s : String) : CommandElabM (Array Nat) := do
    let nm := s.toName
    match env[nm]? with
    | some S => return S
    | none =>
      let full := if (← getEnv).contains (P ++ nm) then P ++ nm else nm
      liftCoreM (readStrips full)
  let toNat (s : String) : CommandElabM Nat := match s.toNat? with
    | some v => pure v
    | none => throwError "#hpb_eval: expected a number, got {s}"
  let pinOk (what : String) (b : ByteArray) (size hash : Nat) : CommandElabM Unit :=
    match checkPin what b size hash with
    | .ok () => pure ()
    | .error e => throwError "#hpb_eval: {e}"
  for ws in lines do
    let line := " ".intercalate ws
    match ws with
    | ["text", m, path, fs, fh, rh, sh] =>
      let b ← readPinned path (← toNat fs) (← toNat fh)
      let T ← match textBlocks b with
        | .ok T => pure T
        | .error e => throwError "#hpb_eval {m}: {e}"
      let R ← match textRows T with
        | .ok R => pure R
        | .error e => throwError "#hpb_eval {m}: {e}"
      pinOk s!"{m} rows" (rowBytes R) 2412240 (← toNat rh)
      let S := stripsOfRows n R
      pinOk m (stripBytes n S) 2412240 (← toNat sh)
      env := env.insert m.toName S
    | "prod" :: m :: size :: hash :: a :: bs =>
      let mut C ← rd env a
      for x in bs do
        C := mulStrips n C (← rd env x)
      pinOk m (stripBytes n C) (← toNat size) (← toNat hash)
      env := env.insert m.toName C
    | ["inv", m, size, hash, a] =>
      let some R := invRows n (rowsOfStrips n (← rd env a)) | throwError "#hpb_eval {m}: singular"
      let C := stripsOfRows n R
      pinOk m (stripBytes n C) (← toNat size) (← toNat hash)
      env := env.insert m.toName C
    | ["rank", m, size, hash, a] =>
      let some C := rankOnePlus n (← rd env a) | throwError "#hpb_eval {m}: dependent rows"
      pinOk m (stripBytes n C) (← toNat size) (← toNat hash)
      env := env.insert m.toName C
    | ["poly", m, size, hash, p, a] =>
      let C := polyMulOnePlus n (← rd env p) (← rd env a)
      pinOk m (stripBytes n C) (← toNat size) (← toNat hash)
      env := env.insert m.toName C
    | _ => throwError "#hpb_eval: bad step {line}"
  let t1 ← IO.monoMsNow
  liftCoreM <| withOptions (Elab.async.set · false) do
    for o in outs do
      let some S := env[o.getId]? | throwError "#hpb_eval: {o.getId} was not computed"
      addMatrix (P ++ o.getId) S
  logInfo m!"HPBTIME steps {t1 - t0} ms, add {(← IO.monoMsNow) - t1} ms"
