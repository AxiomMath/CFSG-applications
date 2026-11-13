import CFSGOutside.Serre.Defs

/-!
# Serre (2013), Théorème 5

J.-P. Serre, *Un critère d'indépendance pour une famille de représentations ℓ-adiques*,
Comment. Math. Helv. 88 (2013), 541-554, §6.4. For distinct primes `ℓ, ℓ' ≥ 5`, the sets `Σ_ℓ` and `Σ_ℓ'`
of §6.1 (`CFSGOutside.Serre.InSigma`) are disjoint, and in fact groups in them have different orders.
-/

open CFSGOutside.Serre

/-- **Serre (2013), Théorème 5, strong form** (after Artin and Kimmerle–Lyons–Sandling–Teague).
"La démonstration donne même un résultat plus fort: si `G` appartient à `Σ_ℓ` et `G'` appartient à
`Σ_ℓ'`, leurs ordres `|G|` et `|G'|` sont distincts", for distinct primes `ℓ, ℓ' ≥ 5`. -/
theorem CFSGOutsideClean.Serre.card_ne_of_inSigma {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') {G G' : Type} [Group G] [Finite G]
    [Group G'] [Finite G'] (hG : InSigma ℓ G) (hG' : InSigma ℓ' G') : Nat.card G ≠ Nat.card G' :=
  sorry

/-- **Serre (2013), Théorème 5.** "Si `ℓ'` est premier `≥ 5` et distinct de `ℓ`, on a
`Σ_ℓ ∩ Σ_ℓ' = ∅`": no finite group belongs to both `Σ_ℓ` and `Σ_ℓ'`. -/
theorem CFSGOutsideClean.Serre.sigma_disjoint {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ')
    (hne : ℓ ≠ ℓ') (G : Type) [Group G] [Finite G] : ¬ (InSigma ℓ G ∧ InSigma ℓ' G) :=
  sorry

/-- `PSL₂(𝔽₅)`, the omitted duplicate `A₁(5)`, belongs to `Σ₅`. -/
theorem CFSGOutsideClean.Serre.psl2_five_mem_sigma :
    InSigma 5 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
  sorry

/-- `A₅` belongs to `Σ₅`: it is `PSL₂(𝔽₅)` (the catalogue lists it as an alternating group). -/
theorem CFSGOutsideClean.Serre.alternatingGroup_five_mem_sigma :
    InSigma 5 (alternatingGroup (Fin 5)) :=
  sorry
