import CFSGOutside.Corpus.HallPaige.Th.Gz
import CFSGOutside.Corpus.HallPaige.Th.Kernel

/-!
# Copied corpus data: the Dempwolff certificate of `Th`

The data files are byte-for-byte copies of corpus files (AxiomMath/CFSG @ 69cb972), read with the copied
readers of `Th/Gz.lean` under the same pinned sizes and hashes as in the corpus:

* `Data/ThDemp-demp.json.gz` is `Certificates/Kernel/ThDemp/data/demp.json.gz`
  (`#kc_json_gz CFSG.KD.ThDemp`, Certificates/Kernel/ThDemp/Data.lean:8);
* `Data/ThDemp-orb.json.gz` is `Certificates/Kernel/ThDemp/data/orb.json.gz`
  (`#kc_json_gz CFSG.KD.ThDempO`, Certificates/Kernel/ThDemp/OrbData.lean:8);
* `Data/ThSeed_const.items.gz` is `CFSG/Certificates/Kernel/Th/S/Data/data/Seed_const.items.gz`
  (`#kc_nat_items_gz CFSG.KD.ThSeed`, CFSG/Certificates/Kernel/Th/S/Data/Seed_const.lean:13).
-/

#th_json_gz CFSGOutside.Corpus.Th.KD.ThDemp "../Data/ThDemp-demp.json.gz" 4437334
  12767656790841757507
  (c : Nat) (rm : Nat) (tm0 : Nat) (tm1 : Nat) (tm2 : Nat) (tm3 : Nat) (tm4 : Nat) (tm5 : Nat)
  (tm6 : Nat) (tm7 : Nat) (up : Nat) (dg : Nat) (ONE : Nat) (regs : List Nat) (cs1 : List Nat)
  (cs2 : List Nat) (r1 : Nat) (nreg : Nat) (rd : Nat) (pr : Nat) (npr : Nat) (L : Nat)
  (fr : List Nat) (bv : List Nat) (osz : List Nat) (pts : List (List Nat))
  (tr : List (List Nat)) (tree : List (List Nat)) (ord : List (List Nat))
  (res : List (List Nat))

#th_json_gz CFSGOutside.Corpus.Th.KD.ThDempO "../Data/ThDemp-orb.json.gz" 6338015
  2327803327457774673
  (Ti : List (List Nat)) (words : List (List Nat)) (sb : List Nat)
  (grp : List (List (List (List Nat)))) (ky : List Nat) (par : List Nat) (edges : List Nat)
  (ord : List Nat) (fx5 : List Nat) (x5 : Nat) (x31 : Nat) (yb : Nat) (dm : Nat) (f5 : Nat)
  (v5 : Nat) (qm : Nat) (gs5 : Nat) (gs31 : Nat) (Ga : Nat) (Gb : Nat) (gd0 : Nat) (gd1 : Nat)

#th_nat_items_gz CFSGOutside.Corpus.Th.KD.ThSeed "../Data/ThSeed_const.items.gz" 47636
  10674603790107308401
  SA SB SF SAf SFf SFx

namespace CFSGOutside.Corpus.Th.KernelThDemp

open CFSGOutside.Corpus.Th.KC.ThDemp

/-- Corpus: `CertificateChecks.KernelThDemp.dempData`, Certificates/Kernel/ThDemp/Data.lean:23. -/
noncomputable def dempData : DempData where
  c := CFSGOutside.Corpus.Th.KD.ThDemp.c
  rm := CFSGOutside.Corpus.Th.KD.ThDemp.rm
  tm0 := CFSGOutside.Corpus.Th.KD.ThDemp.tm0
  tm1 := CFSGOutside.Corpus.Th.KD.ThDemp.tm1
  tm2 := CFSGOutside.Corpus.Th.KD.ThDemp.tm2
  tm3 := CFSGOutside.Corpus.Th.KD.ThDemp.tm3
  tm4 := CFSGOutside.Corpus.Th.KD.ThDemp.tm4
  tm5 := CFSGOutside.Corpus.Th.KD.ThDemp.tm5
  tm6 := CFSGOutside.Corpus.Th.KD.ThDemp.tm6
  tm7 := CFSGOutside.Corpus.Th.KD.ThDemp.tm7
  up := CFSGOutside.Corpus.Th.KD.ThDemp.up
  dg := CFSGOutside.Corpus.Th.KD.ThDemp.dg
  ONE := CFSGOutside.Corpus.Th.KD.ThDemp.ONE
  SA := CFSGOutside.Corpus.Th.KD.ThSeed.SA
  SB := CFSGOutside.Corpus.Th.KD.ThSeed.SB
  regs := CFSGOutside.Corpus.Th.KD.ThDemp.regs
  cs1 := CFSGOutside.Corpus.Th.KD.ThDemp.cs1
  cs2 := CFSGOutside.Corpus.Th.KD.ThDemp.cs2
  r1 := CFSGOutside.Corpus.Th.KD.ThDemp.r1
  nreg := CFSGOutside.Corpus.Th.KD.ThDemp.nreg
  rd := CFSGOutside.Corpus.Th.KD.ThDemp.rd
  pr := CFSGOutside.Corpus.Th.KD.ThDemp.pr
  npr := CFSGOutside.Corpus.Th.KD.ThDemp.npr
  L := CFSGOutside.Corpus.Th.KD.ThDemp.L
  fr := CFSGOutside.Corpus.Th.KD.ThDemp.fr
  bv := CFSGOutside.Corpus.Th.KD.ThDemp.bv
  osz := CFSGOutside.Corpus.Th.KD.ThDemp.osz
  pts := CFSGOutside.Corpus.Th.KD.ThDemp.pts
  tr := CFSGOutside.Corpus.Th.KD.ThDemp.tr
  tree := CFSGOutside.Corpus.Th.KD.ThDemp.tree
  ord := CFSGOutside.Corpus.Th.KD.ThDemp.ord
  res := CFSGOutside.Corpus.Th.KD.ThDemp.res

/-- Corpus: `CertificateChecks.KernelThDemp.orbData`, Certificates/Kernel/ThDemp/OrbData.lean:21. -/
noncomputable def orbData : OrbData where
  Ti := CFSGOutside.Corpus.Th.KD.ThDempO.Ti
  words := CFSGOutside.Corpus.Th.KD.ThDempO.words
  sb := CFSGOutside.Corpus.Th.KD.ThDempO.sb
  grp := CFSGOutside.Corpus.Th.KD.ThDempO.grp
  ky := CFSGOutside.Corpus.Th.KD.ThDempO.ky
  par := CFSGOutside.Corpus.Th.KD.ThDempO.par
  edges := CFSGOutside.Corpus.Th.KD.ThDempO.edges
  ord := CFSGOutside.Corpus.Th.KD.ThDempO.ord
  fx5 := CFSGOutside.Corpus.Th.KD.ThDempO.fx5
  x5 := CFSGOutside.Corpus.Th.KD.ThDempO.x5
  x31 := CFSGOutside.Corpus.Th.KD.ThDempO.x31
  yb := CFSGOutside.Corpus.Th.KD.ThDempO.yb
  dm := CFSGOutside.Corpus.Th.KD.ThDempO.dm
  f5 := CFSGOutside.Corpus.Th.KD.ThDempO.f5
  v5 := CFSGOutside.Corpus.Th.KD.ThDempO.v5
  qm := CFSGOutside.Corpus.Th.KD.ThDempO.qm
  gs5 := CFSGOutside.Corpus.Th.KD.ThDempO.gs5
  gs31 := CFSGOutside.Corpus.Th.KD.ThDempO.gs31
  Ga := CFSGOutside.Corpus.Th.KD.ThDempO.Ga
  Gb := CFSGOutside.Corpus.Th.KD.ThDempO.Gb
  gd0 := CFSGOutside.Corpus.Th.KD.ThDempO.gd0
  gd1 := CFSGOutside.Corpus.Th.KD.ThDempO.gd1

end CFSGOutside.Corpus.Th.KernelThDemp
