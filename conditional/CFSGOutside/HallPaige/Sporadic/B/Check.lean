import CFSGOutside.Corpus.HallPaige.B.Defs

/-!
# Boolean forms of the corpus strip checks

The corpus checks `AllStrips Ws A C` (`C = A * W₁ * ⋯ * Wₖ`, strip by strip) and `AllStripsX Q P R`
(`R = P * (Q + 1)`) are inductive predicates assembled from one kernel-evaluated equation per strip
(the corpus tactic `bm_strips4`). Here the same equations are folded into one boolean, evaluated by the
kernel (`decide +kernel`), and turned back into the predicates.
-/

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.KC.BM CFSGOutside.Corpus.B.KC.BM.Fix

/-- All strip equations `mulW Ws aᵢ = cᵢ`. -/
noncomputable def allStripsB (Ws : List (List Nat)) : List Nat → List Nat → Bool
  | a :: as, c :: cs => Nat.beq (mulW Ws a) c && allStripsB Ws as cs
  | [], [] => true
  | _, _ => false

theorem allStrips_of_allStripsB {Ws : List (List Nat)} :
    ∀ {A C : List Nat}, allStripsB Ws A C = true → AllStrips Ws A C
  | [], [], _ => .nil
  | a :: as, c :: cs, h => by
    simp only [allStripsB, Bool.and_eq_true] at h
    exact .cons a c as cs h.1 (allStrips_of_allStripsB h.2)
  | [], _ :: _, h => by simp [allStripsB] at h
  | _ :: _, [], h => by simp [allStripsB] at h

/-- All strip equations `(Q · pᵢ) xor pᵢ = rᵢ` of a rank certificate. -/
noncomputable def allStripsXB (Q : List Nat) : List Nat → List Nat → Bool
  | a :: as, c :: cs => Nat.beq (Nat.xor (mulS Q a) a) c && allStripsXB Q as cs
  | [], [] => true
  | _, _ => false

theorem allStripsX_of_allStripsXB {Q : List Nat} :
    ∀ {P R : List Nat}, allStripsXB Q P R = true → AllStripsX Q P R
  | [], [], _ => .nil
  | a :: as, c :: cs, h => by
    simp only [allStripsXB, Bool.and_eq_true] at h
    exact .cons a c as cs h.1 (allStripsX_of_allStripsXB h.2)
  | [], _ :: _, h => by simp [allStripsXB] at h
  | _ :: _, [], h => by simp [allStripsXB] at h

/-- A rank certificate `(P, R)` for `rank (M - 1) = k`, as one boolean. -/
noncomputable def rankChk (M P R : List Nat) (k : Nat) : Bool :=
  wfMat P && wfMat R && allStripsXB M P R && shapeOK R k && echFrom P k

theorem rankChk_spec {M P R : List Nat} {k : Nat} (h : rankChk M P R k = true) :
    wfMat P = true ∧ wfMat R = true ∧ AllStripsX M P R ∧ shapeOK R k = true ∧ echFrom P k = true := by
  simp only [rankChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, allStripsX_of_allStripsXB h.1.1.2, h.1.2, h.2⟩

end CFSGOutside.HallPaige.B
