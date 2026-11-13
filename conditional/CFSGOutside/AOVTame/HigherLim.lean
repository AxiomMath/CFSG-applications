import Mathlib

/-!
# Higher limits

For a small category `D` and a functor `F : D ⥤ Ab`, the higher limits `lim^i F` are the
cohomology groups of the cosimplicial abelian group (Bousfield–Kan)
`[n] ↦ ∏_{σ ∈ N_n(D)} F(σ_n)`, where `N_n(D)` is the set of chains `σ₀ → ⋯ → σₙ` of composable
morphisms of `D`, with coface maps induced by precomposition and, on the last vertex, by `F`.
These are the right derived functors of `lim : (D ⥤ Ab) ⥤ Ab`.
-/

namespace AndersenOliverVentura.Tame.HigherLim

open CategoryTheory

variable {D : Type} [SmallCategory D] (F : D ⥤ AddCommGrpCat.{0})

/-- Precomposition of an `n`-simplex of the nerve with `θ : [m] → [n]`. -/
def restr {m n : SimplexCategory} (θ : m ⟶ n) (σ : ComposableArrows D n.len) :
    ComposableArrows D m.len :=
  θ.toOrderHom.monotone.functor ⋙ σ

@[simp] lemma restr_obj {m n : SimplexCategory} (θ : m ⟶ n) (σ : ComposableArrows D n.len)
    (i : Fin (m.len + 1)) : (restr θ σ).obj i = σ.obj (θ.toOrderHom i) := rfl

lemma restr_id {n : SimplexCategory} (σ : ComposableArrows D n.len) : restr (𝟙 n) σ = σ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    erw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg σ.map (Subsingleton.elim _ _))

lemma restr_comp {l m n : SimplexCategory} (θ : l ⟶ m) (θ' : m ⟶ n) (σ : ComposableArrows D n.len) :
    restr (θ ≫ θ') σ = restr θ (restr θ' σ) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    erw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg σ.map (Subsingleton.elim _ _))

/-- The cochains of degree `n`: `∏_{σ ∈ N_n(D)} F(σ_n)`. -/
def cochains (n : SimplexCategory) : AddCommGrpCat.{0} :=
  AddCommGrpCat.of (∀ σ : ComposableArrows D n.len, F.obj (σ.obj (Fin.last n.len)))

lemma transport {n : ℕ} (c : ∀ σ : ComposableArrows D n, F.obj (σ.obj (Fin.last n)))
    {τ σ : ComposableArrows D n} (h : τ = σ) :
    c σ = F.map (eqToHom (congrArg (fun x : ComposableArrows D n => x.obj (Fin.last n)) h)) (c τ) := by
  subst h; simp

/-- The coface map induced by `θ : [m] → [n]`. -/
def coface {m n : SimplexCategory} (θ : m ⟶ n) : cochains F m ⟶ cochains F n :=
  AddCommGrpCat.ofHom
    { toFun := fun c σ => F.map (σ.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m.len)))))
        (c (restr θ σ))
      map_zero' := by funext σ; exact map_zero _
      map_add' := fun a b => by funext σ; exact map_add _ _ _ }

lemma coface_apply {m n : SimplexCategory} (θ : m ⟶ n) (c : cochains F m)
    (σ : ComposableArrows D n.len) :
    coface F θ c σ = F.map (σ.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m.len)))))
      (c (restr θ σ)) := rfl

/-- The Bousfield–Kan cosimplicial abelian group of `F`. -/
def cosimplicial : CosimplicialObject AddCommGrpCat.{0} where
  obj := cochains F
  map := coface F
  map_id n := by
    ext c
    funext σ
    change coface F (𝟙 n) c σ = c σ
    rw [coface_apply, transport F c (restr_id σ)]
    have : σ.map (homOfLE (Fin.le_last ((𝟙 n : n ⟶ n).toOrderHom (Fin.last n.len)))) =
        eqToHom (congrArg (fun x : ComposableArrows D n.len => x.obj (Fin.last n.len))
          (restr_id σ)) := by
      exact ((congrArg σ.map (Subsingleton.elim _ (𝟙 _))).trans (σ.map_id _)).trans
        (eqToHom_refl _ _).symm
    rw [this]
    rfl
  map_comp {l m n} θ θ' := by
    ext c
    funext σ
    change coface F (θ ≫ θ') c σ = coface F θ' (coface F θ c) σ
    rw [coface_apply, coface_apply, coface_apply, transport F c (restr_comp θ θ' σ)]
    have : σ.map (homOfLE (Fin.le_last ((θ ≫ θ').toOrderHom (Fin.last l.len)))) =
        eqToHom (congrArg (fun x : ComposableArrows D l.len => x.obj (Fin.last l.len))
          (restr_comp θ θ' σ)) ≫ (restr θ' σ).map (homOfLE (Fin.le_last (θ.toOrderHom
            (Fin.last l.len)))) ≫ σ.map (homOfLE (Fin.le_last (θ'.toOrderHom (Fin.last m.len)))) := by
      refine Eq.trans ?_ (congrArg (· ≫ _) (eqToHom_refl _ _).symm)
      erw [Category.id_comp]
      change _ = σ.map _ ≫ σ.map _
      erw [← σ.map_comp]
      exact congrArg σ.map (Subsingleton.elim _ _)
    rw [this]
    erw [F.map_comp, F.map_comp]
    rfl

/-- `lim^i F`. -/
noncomputable def lim (i : ℕ) : AddCommGrpCat.{0} :=
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{0}).obj (cosimplicial F)).homology i

end AndersenOliverVentura.Tame.HigherLim
