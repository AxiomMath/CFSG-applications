import Lean

/-!
# Reading the corpus's compressed data files

A copy of the corpus readers `#kc_json_gz` (CFSG/Certificates/Kernel/Common/JsonGz.lean) and
`#kc_nat_items_gz` (CFSG/Certificates/Kernel/Common/NatItemsGz.lean), with the `gunzip` of
CFSG/Certificates/Kernel/Common/HarnessGz.lean, so that the Thompson data files copied verbatim from the
corpus (`Data/Th*.gz`) define the same declarations as in the corpus. The path is relative to the
directory of the current file (as for `include_str`); the decompressed size and hash are pinned as in the
corpus.
-/

open Lean Elab Command Meta

namespace CFSGOutside.Corpus.Th.Gz

/-! ### `CFSG/Certificates/Kernel/Common/HarnessGz.lean` -/

def bit (b : ByteArray) (p : Nat) : Nat :=
  ((b.get! (p >>> 3)).toNat >>> (p &&& 7)) &&& 1

def bits (b : ByteArray) (p n : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do
    v := v ||| (bit b (p + k) <<< k)
  return v

structure Huff where
  count : Array Nat
  sym : Array Nat

def Huff.ofLens (lens : Array Nat) : Huff := Id.run do
  let mut count := Array.replicate 16 0
  for l in lens do
    count := count.modify l (· + 1)
  let mut offs := Array.replicate 16 0
  for l in [1:15] do
    offs := offs.set! (l + 1) (offs[l]! + count[l]!)
  let mut sym := Array.replicate lens.size 0
  for s in [0:lens.size] do
    let l := lens[s]!
    if l != 0 then
      sym := sym.set! offs[l]! s
      offs := offs.modify l (· + 1)
  return { count, sym }

partial def Huff.decode (h : Huff) (b : ByteArray) (p : Nat) : Except String (Nat × Nat) :=
  go p 1 0 0 0
where
  go (p len code first index : Nat) : Except String (Nat × Nat) :=
    if len > 15 then .error "invalid Huffman code" else
    let code := code ||| bit b p
    let c := h.count[len]!
    if code < first + c then .ok (h.sym[index + (code - first)]!, p + 1)
    else go (p + 1) (len + 1) (code <<< 1) ((first + c) <<< 1) (index + c)

def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258]
def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
    13, 13]

def fixedLit (_ : Unit := ()) : Huff :=
  .ofLens ((Array.range 288).map fun s =>
    if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8)
def fixedDist (_ : Unit := ()) : Huff := .ofLens (Array.replicate 30 5)

def clOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def dynCodes (b : ByteArray) (p : Nat) : Except String (Huff × Huff × Nat) := do
  let nlen := bits b p 5 + 257
  let ndist := bits b (p + 5) 5 + 1
  let ncode := bits b (p + 10) 4 + 4
  let mut p := p + 14
  let mut cl := Array.replicate 19 0
  for k in [0:ncode] do
    cl := cl.set! clOrder[k]! (bits b p 3)
    p := p + 3
  let hc := Huff.ofLens cl
  let mut lens : Array Nat := #[]
  while lens.size < nlen + ndist do
    let (s, p') ← hc.decode b p
    p := p'
    if s < 16 then lens := lens.push s
    else
      let (v, r, w) := if s == 16 then (lens.back?.getD 0, 3, 2)
        else if s == 17 then (0, 3, 3) else (0, 11, 7)
      if s == 16 && lens.isEmpty then throw "repeat with no previous length"
      let n := r + bits b p w
      p := p + w
      for _ in [0:n] do
        lens := lens.push v
  if lens.size != nlen + ndist then throw "code lengths overrun"
  return (.ofLens (lens.extract 0 nlen), .ofLens (lens.extract nlen (nlen + ndist)), p)

def inflate (b : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := do
  let stop := 8 * b.size
  let mut p := 8 * start
  let mut out := ByteArray.empty
  let mut final := false
  while !final do
    if p + 3 > stop then throw "truncated stream"
    final := bits b p 1 == 1
    let ty := bits b (p + 1) 2
    p := p + 3
    if ty == 0 then
      let q := (p + 7) / 8
      if q + 4 > b.size then throw "truncated stored block"
      let len := b[q]!.toNat + 256 * b[q + 1]!.toNat
      if q + 4 + len > b.size then throw "truncated stored block"
      out := out ++ b.extract (q + 4) (q + 4 + len)
      p := 8 * (q + 4 + len)
    else if ty == 3 then throw "invalid block type"
    else
      let (lit, dist, p') ← if ty == 1 then pure (fixedLit, fixedDist, p) else dynCodes b p
      p := p'
      let mut done := false
      while !done do
        if p > stop then throw "truncated block"
        let (s, p') ← lit.decode b p
        p := p'
        if s < 256 then out := out.push s.toUInt8
        else if s == 256 then done := true
        else
          let i := s - 257
          if i ≥ 29 then throw "invalid length symbol"
          let len := lenBase[i]! + bits b p lenExtra[i]!
          p := p + lenExtra[i]!
          let (d, p') ← dist.decode b p
          p := p'
          if d ≥ 30 then throw "invalid distance symbol"
          let dst := distBase[d]! + bits b p distExtra[d]!
          p := p + distExtra[d]!
          if dst > out.size then throw "distance past the start"
          for _ in [0:len] do
            out := out.push out[out.size - dst]!
  if p > stop then throw "truncated stream"
  return (out, (p + 7) / 8)

partial def skipZ (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size && b[i]! != 0 then skipZ b (i + 1) else i + 1

def gunzip (b : ByteArray) : Except String ByteArray := do
  if b.size < 18 || b[0]! != 0x1f || b[1]! != 0x8b || b[2]! != 8 then throw "not a gzip file"
  let flg := b[3]!.toNat
  let mut i := 10
  if flg &&& 4 != 0 then i := i + 2 + b[i]!.toNat + 256 * b[i + 1]!.toNat
  if flg &&& 8 != 0 then i := skipZ b i
  if flg &&& 16 != 0 then i := skipZ b i
  if flg &&& 2 != 0 then i := i + 2
  let (out, j) ← inflate b i
  if j + 8 != b.size then throw "trailing bytes after the gzip member"
  let isize := b[j + 4]!.toNat + (b[j + 5]!.toNat <<< 8) + (b[j + 6]!.toNat <<< 16) +
    (b[j + 7]!.toNat <<< 24)
  if isize != out.size % 2 ^ 32 then throw "length differs from the gzip trailer"
  return out

/-- Read a gzip file next to the current file, checking the pinned decompressed size and hash. -/
def readPinnedGz (rel : String) (size hash : Nat) : CommandElabM ByteArray := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let path := dir / rel
  let z ← IO.FS.readBinFile path
  let b ← match gunzip z with
    | .ok b => pure b
    | .error e => throwError "data file {path}: {e}"
  let h := b.hash.toNat
  unless b.size == size && h == hash do
    throwError "data file {path}: decompressed size {b.size} hash {h}, pinned size {size} hash {hash}"
  return b

/-! ### `CFSG/Certificates/Kernel/Common/Harness.lean` -/

def natLE (b : ByteArray) (lo hi : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:hi - lo] do
    v := v ||| (b[lo + k]!.toNat <<< (8 * k))
  return v

def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

/-! ### `CFSG/Certificates/Kernel/Common/JsonGz.lean` -/

partial def ofJson (ty : Expr) (j : Json) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then
    match j with
    | .num n =>
      unless n.exponent == 0 && n.mantissa ≥ 0 do throwError "expected a natural number, got {j}"
      return mkRawNatLit n.mantissa.toNat
    | _ => throwError "expected a natural number, got {j}"
  if ty.isConstOf ``Bool then
    match j with
    | .bool true => return mkConst ``Bool.true
    | .bool false => return mkConst ``Bool.false
    | _ => throwError "expected a boolean, got {j}"
  match ty.getAppFnArgs with
  | (``List, #[α]) =>
    let .arr xs := j | throwError "expected an array, got {j}"
    let u ← getDecLevel α
    let es ← xs.mapM (ofJson α)
    return es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [u]) α e acc)
      (mkApp (mkConst ``List.nil [u]) α)
  | _ => throwError "#th_json_gz: unsupported type {ty}"

/-! ### `CFSG/Certificates/Kernel/Common/NatItemsGz.lean` -/

def items (b : ByteArray) : Except String (Array Nat) := do
  let mut out := #[]
  let mut i := 0
  while i < b.size do
    if b.size < i + 4 then throw "truncated item header"
    let n := natLE b i (i + 4)
    if b.size < i + 4 + n then throw "truncated item"
    out := out.push (natLE b (i + 4) (i + 4 + n))
    i := i + 4 + n
  return out

end CFSGOutside.Corpus.Th.Gz

open CFSGOutside.Corpus.Th.Gz in
/-- `#th_json_gz pre "path" size hash (x : T)*` defines `pre.x : T` from the field `x` of the JSON
object in the gzip file `path` (the corpus `#kc_json_gz`). -/
elab "#th_json_gz " pre:ident path:str size:num hash:num fs:("(" ident " : " term ")")* :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#th_json_gz: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#th_json_gz: {path.getString}: {e}"
  let fields := fs.map fun f => ((⟨f.raw[1]⟩ : Ident), (⟨f.raw[3]⟩ : Term))
  let defs ← liftTermElabM do
    fields.mapM fun (x, t) => do
      let ty ← instantiateMVars (← Term.elabType t)
      let v ← match j.getObjVal? x.getId.toString with
        | .ok v => pure v
        | .error e => throwError "#th_json_gz: {e}"
      return (pre.getId ++ x.getId, ty, ← ofJson ty v)
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v

open CFSGOutside.Corpus.Th.Gz in
/-- `#th_nat_items_gz pre "path" size hash x*` defines `pre.x : ℕ` from the items of the gzip file
`path`, in order (the corpus `#kc_nat_items_gz`, plain entries only). -/
elab "#th_nat_items_gz " pre:ident path:str size:num hash:num xs:ident* : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let vs ← match items b with
    | .ok vs => pure vs
    | .error e => throwError "#th_nat_items_gz: {path.getString}: {e}"
  unless xs.size == vs.size do
    throwError "#th_nat_items_gz: {path.getString} has {vs.size} items, {xs.size} names given"
  withSync do
    for (x, v) in xs.zip vs do
      addDef (pre.getId ++ x.getId) (mkConst ``Nat) (mkRawNatLit v)
