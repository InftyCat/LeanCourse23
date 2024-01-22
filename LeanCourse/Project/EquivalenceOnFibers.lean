import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration
import LeanCourse.Project.SplitFibrationViaGrothendieck
import LeanCourse.Project.FibrationBicategory
import LeanCourse.Project.CounitOnFibers
import LeanCourse.Project.CartesianFunctors
set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 1500000
set_option quotPrecheck false

universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories
 variable {B : Cat.{v₁ , v₁}} {I : B}
 variable {P : fibration B}
 notation "E" => E'_obj (P:=P) (I:=I)
 notation u  "°" X => cartesianLiftFromFibration P u X
def idCartLift {X : P [I]} : cartesianLiftOfAlong X (𝟙 _) := by
      use ⟨ X , ⟨ 𝟙 _ , by aesop ⟩ ⟩
      intro J v L
      let L' := transportLift (Category.comp_id _) L
      use L'.φ
      constructor
      sorry --aesop
      intro φ hφ
      apply Subtype.ext
      rw [← Category.comp_id φ.1]
      rw [hφ]
      rfl

@[simps] noncomputable def functorOnFibers (X : P [I]) : (fundamentalFibration.obj I).1.left ⥤ P.1.left where
  obj := fun u  ↦ (u.hom ° X).Y.1
  map := fun {uv u} v  ↦ by

    simp
    have this : v.left ≫ u.hom = uv.hom := Over.w v
    rw [← this]
    exact ((u.hom ° X).2 _ _).choose.1;
  map_id := by sorry
  map_comp := by sorry

@[simps] noncomputable def OverMorphOnFibers (X : P [I]) : (fundamentalFibration.obj I).1 ⟶ P.1 := by
  apply Over.homMk
  swap
  exact functorOnFibers X
  sorry
  /-
  apply extFunctor
  swap
  constructor
  · intro Y Z f


  · sorry
-/



theorem equivOnFibers [Cleavage P] : IsEquivalence E := by
  have essSurj : EssSurj E := by
    constructor
    intro X
    let F : fundamentalFibration.obj I ⥤c P := ⟨
      OverMorphOnFibers X ,
      by sorry
      ⟩
    use F
    constructor
    rw [E'_obj_obj]
    unfold E_obj_obj
    unfold toFunctorOnFibers
    unfold objMappingBetweenFibers
    simp
    exact (cartesianLiftIsUnique (P:=P.1.hom) (idCartLift) (𝟙 _ ° X)).choose





  have full : Full E := by
    constructor ; swap
    · intro X Y f
      constructor ; swap

      · apply NatTrans.mk ; swap
        · intro u
          --exact (reindexing u.hom).map f
        · sorry
      · sorry

    · sorry

  have faithful : Faithful E := by sorry
  apply Equivalence.ofFullyFaithfullyEssSurj
