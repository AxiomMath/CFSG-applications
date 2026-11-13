import CFSGOutside.HallPaige.Sporadic.J4.GenLit

/-!
# The kernel checks for `J₄`

Boolean checks over the data of `CFSGOutside.HallPaige.Sporadic.J4.Data`, each evaluated by the
kernel (`decide +kernel`) in the generated modules `Tab*`, `For*`, `Gen*`, `Wit*`, `Misc*`, `XC*`.

* `sb m` is the packed basis of the `m`-th subspace `S m` of the `Hj`-orbit of `W = S 0`;
* `tab k m`: `S m ᵥ* xJ k = S (tab k m)`;
* `fgen f m`, `ftgt f m`: the edge at `m` of the `f`-th Schreier forest
  (`S m ᵥ* g = S (ftgt f m)` for the generator `g` of index `fgen f m`, roots have `fgen = 7`);
* forests `0, …, 6` reduce the subspace `h' • W` modulo `Hj ∩ P Hj P⁻¹` (`P = pathElt pℓ`),
  forests `7 + c` reduce `h₂⁻¹ • W` modulo the stabilizer of the subspace `Q c = P⁻¹ • S rep`;
* candidate `i` is the double coset representative `rwOf i`, with the triangle witness
  `candH i`, `candK i`.
-/

namespace CFSGOutside.HallPaige.J4

open CFSGOutside.Corpus.J4 CFSGOutside.HallPaige.F2

noncomputable section

def sb (m : ℕ) : List ℕ := unpack 112 10 (SbL.getD m 0)
def spv (m : ℕ) : List ℕ := unpack 7 10 (SpL.getD m 0)
def fld (w N m : ℕ) : ℕ := (N >>> (w * m)) &&& (2 ^ w - 1)
def tab (k m : ℕ) : ℕ := fld 11 (TabN.getD k 0) m
def tinv (k m : ℕ) : ℕ := fld 11 (TinvN.getD k 0) m
def fgen (f m : ℕ) : ℕ := fld 14 (ForN.getD f 0) m >>> 11
def ftgt (f m : ℕ) : ℕ := fld 14 (ForN.getD f 0) m &&& 2047
def gw (f j : ℕ) : List ℕ := gwL.getD (8 * f + j) []
def gm (f j : ℕ) : List ℕ := unpackM (GmN.getD (8 * f + j) 0)
def qb (c : ℕ) : List ℕ := unpack 112 10 (qbL.getD c 0)
def qp (c : ℕ) : List ℕ := unpack 7 10 (qpL.getD c 0)

/-- `f m` for all `lo ≤ m < hi`. -/
def allR (lo hi : ℕ) (f : ℕ → Bool) : Bool := (List.range' lo (hi - lo)).all f

def imgChk (R bs tbs : List ℕ) : Bool := bs.all fun b => red tbs (vmL R b) == 0
def wImgChk (w bs tbs : List ℕ) : Bool := bs.all fun b => red tbs (applyW lm w b) == 0

def pathW (p : List ℕ) : List ℕ := p.map fun l => if l = 1 then 6 else 7
def pathInvW (p : List ℕ) : List ℕ := p.reverse.map fun l => if l = 1 then 6 else 8
def invW (w : List ℕ) : List ℕ := w.reverse.map fun l => if l < 3 then l + 3 else l - 3

/-- Packed product of a word in the letters `±1, ±2` (`a`, `b` and inverses). -/
def letZ (l : ℤ) : List ℕ := if l = 1 then lm 6 else if l = 2 then lm 7 else if l = -1 then lm 6 else lm 8
def wordZ (w : List ℤ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) (idm 112) (fun l _ ih => mmL (letZ l) ih) w

/-- Packed power. -/
def powM (R : List ℕ) (n : ℕ) : List ℕ := Nat.rec (idm 112) (fun _ acc => mmL acc R) n

def chkRref (m : ℕ) : Bool := rrefB (sb m) (spv m)
def chkTab (k m : ℕ) : Bool := decide (tab k m < 1771) && imgChk (lm k) (sb m) (sb (tab k m))
def chkTinv (k m : ℕ) : Bool := decide (tinv k m < 1771) && tab k (tinv k m) == m
def chkFor (f m : ℕ) : Bool :=
  fgen f m == 7 || (decide (fgen f m < 7) && decide (ftgt f m < 1771) &&
    imgChk (gm f (fgen f m)) (sb m) (sb (ftgt f m)))

def reach (f : ℕ) : ℕ → ℕ → Bool
  | 0, m => fgen f m == 7
  | n + 1, m => fgen f m == 7 || reach f n (ftgt f m)

def chkGen (f j : ℕ) : Bool := (gw f j).all (fun l => decide (l < 6)) && wordM lm (gw f j) == gm f j

def qv (l : ℕ) : ℕ := applyW lm (pathInvW (repPaths.getD l [])) rootBits
def chkStab (l j : ℕ) : Bool := vmL (gm l j) (qv l) == qv l

def chkQ (c : ℕ) : Bool :=
  rrefB (qb c) (qp c) && wImgChk (pathW (repPaths.getD (clsL.getD c 0) [])) (sb (clsRep.getD c 0)) (qb c) &&
    (List.range 7).all fun j => imgChk (gm (7 + c) j) (qb c) (qb c)

def rootsOf (f : ℕ) : List ℕ := (List.range 1771).filter fun m => fgen f m == 7
def chkCls (l : ℕ) : Bool := rootsOf l == ((clsL.zip clsRep).filter fun p => p.1 == l).map Prod.snd

def ncand : ℕ := candC.length
def chkCand (c : ℕ) : Bool :=
  rootsOf (7 + c) == ((candC.zip candI).filter fun p => p.1 == c).map Prod.snd

def chkU (j : ℕ) : Bool := wImgChk (uwL.getD j []) (sb 0) (sb j) && (uwL.getD j []).all (fun l => decide (l < 3))

def rwOf (i : ℕ) : List ℕ :=
  uwL.getD (candI.getD i 0) [] ++ pathInvW (repPaths.getD (clsL.getD (candC.getD i 0) 0) []) ++
    invW (uwL.getD (clsRep.getD (candC.getD i 0) 0) [])
def fullW (i : ℕ) : List ℕ := rwOf i ++ candH.getD i [] ++ rwOf i ++ candK.getD i [] ++ rwOf i

def poolL (l : ℕ) : Bool := decide (9 ≤ l) && decide (l < 43)
def chkWit (i : ℕ) : Bool :=
  wImgChk (fullW i) (sb 0) (sb 0) && (candH.getD i []).all poolL && (candK.getD i []).all poolL

def chkMisc : Bool :=
  clsL.length == 36 && clsRep.length == 36 && candI.length == ncand &&
  (List.range 36).all (fun c => decide (clsL.getD c 0 < 7) && decide (clsRep.getD c 0 < 1771)) &&
  (List.range ncand).all (fun i => decide (candC.getD i 0 < 36) && decide (candI.getD i 0 < 1771) &&
    needJ.contains (candI.getD i 0) && needJ.contains (clsRep.getD (candC.getD i 0) 0)) &&
  needJ.all (fun j => decide (j < 1771))

def chkPool : Bool := (List.range 17).all fun j => imgChk (lm (26 + j)) (sb 0) (sb 0)

def bitAt (R : List ℕ) (i j : ℕ) : Bool := (R.getD i 0).testBit j
def chkKlein : Bool :=
  decide (kleinJ < 16) &&
  mmL (lm 25) (lm 25) == idm 112 && mmL (lm (9 + kleinJ)) (lm (9 + kleinJ)) == idm 112 &&
  mmL (lm 25) (lm (9 + kleinJ)) == mmL (lm (9 + kleinJ)) (lm 25) &&
  decide (kleinPos.getD 0 0 < 112) && decide (kleinPos.getD 1 0 < 112) &&
  decide (kleinPos.getD 2 0 < 112) && decide (kleinPos.getD 3 0 < 112) &&
  decide (kleinPos.getD 4 0 < 112) && decide (kleinPos.getD 5 0 < 112) &&
  bitAt (lm 25) (kleinPos.getD 0 0) (kleinPos.getD 1 0) != bitAt (idm 112) (kleinPos.getD 0 0) (kleinPos.getD 1 0) &&
  bitAt (lm (9 + kleinJ)) (kleinPos.getD 2 0) (kleinPos.getD 3 0) !=
    bitAt (idm 112) (kleinPos.getD 2 0) (kleinPos.getD 3 0) &&
  bitAt (lm 25) (kleinPos.getD 4 0) (kleinPos.getD 5 0) !=
    bitAt (lm (9 + kleinJ)) (kleinPos.getD 4 0) (kleinPos.getD 5 0)

def par (x : ℕ) : Bool := xf (fun k => x.testBit k) 112
def chkFun : Bool :=
  decide (funW < 10) && (sb 0).all (fun w => par (funN &&& w) == false) &&
    par (funN &&& vmL (lm 6) ((sb 0).getD funW 0)) == true

end

end CFSGOutside.HallPaige.J4
