import CFSGOutside.Serre.Paper
import CFSGOutsideClean.Corpus.LieOrderBridgeHolds
import CFSGOutsideClean.Corpus.OrdProjLeOfMulEq

/-!
# Serre (2013), Théorème 5 (Artin): `Σ_ℓ ∩ Σ_ℓ' = ∅`

J.-P. Serre, *Un critère d'indépendance pour une famille de représentations ℓ-adiques*,
Comment. Math. Helv. 88 (2013), 541-554, §6.4. The orders of the catalogue groups of Lie type and Artin's
estimate of their `s`-parts are supplied by the corpus. Neither the paper nor the proof uses the classification.
-/

open CFSGOutside.Serre

/-- **ℓ-adic independence criterion.** For a prime ℓ ≥ 5 let Σ_ℓ be the class of finite groups isomorphic to a finite
simple group of Lie type in characteristic ℓ or to the cyclic group of order ℓ. If ℓ and ℓ′ are distinct primes,
both at least 5, then a group in Σ_ℓ and a group in Σ_ℓ′ never have the same order. In particular no finite group
lies in both classes.

Source: J.-P. Serre, Un critère d'indépendance pour une famille de représentations ℓ-adiques, Comment. Math. Helv.
88 (2013), 541–554, Théorème 5 and the remark on orders after it, §6.4. https://arxiv.org/abs/1006.2442 -/
theorem CFSGOutsideClean.Serre.card_ne_of_inSigma {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') {G G' : Type} [Group G] [Finite G]
    [Group G'] [Finite G'] (hG : InSigma ℓ G) (hG' : InSigma ℓ' G') : Nat.card G ≠ Nat.card G' :=
  CFSGOutside.Serre.card_ne_of_inSigma hℓ hℓ' h5 h5' hne hG hG'

/-- **Serre (2013), Théorème 5.** "Si `ℓ'` est premier `≥ 5` et distinct de `ℓ`, on a
`Σ_ℓ ∩ Σ_ℓ' = ∅`": no finite group belongs to both `Σ_ℓ` and `Σ_ℓ'`. -/
theorem CFSGOutsideClean.Serre.sigma_disjoint {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ')
    (hne : ℓ ≠ ℓ') (G : Type) [Group G] [Finite G] : ¬ (InSigma ℓ G ∧ InSigma ℓ' G) :=
  CFSGOutside.Serre.sigma_disjoint hℓ hℓ' h5 h5' hne G

/-- `PSL₂(𝔽₅)`, the omitted duplicate `A₁(5)`, belongs to `Σ₅`. -/
theorem CFSGOutsideClean.Serre.psl2_five_mem_sigma :
    InSigma 5 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
  CFSGOutside.Serre.psl2_five_mem_sigma

/-- `A₅` belongs to `Σ₅`: it is `PSL₂(𝔽₅)` (the catalogue lists it as an alternating group). -/
theorem CFSGOutsideClean.Serre.alternatingGroup_five_mem_sigma :
    InSigma 5 (alternatingGroup (Fin 5)) :=
  CFSGOutside.Serre.alternatingGroup_five_mem_sigma
