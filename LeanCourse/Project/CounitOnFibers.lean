import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
--import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration
import LeanCourse.Project.SplitFibrationViaGrothendieck
import LeanCourse.Project.FibrationBicategory
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
-- variable {B : Cat.{v₁ , v₁}} {I J K : B}
instance {B : Cat.{v₁ , v₁}} {I : B}  : Category (Over I) := commaCategory



def discreteFibration (B : Cat) := {P : fibration B //  isDiscreteOverB P.1}


noncomputable instance {P : discreteFibration B} : Cleavage P.1 where
  Cart' :=  cartesianLiftFromFibration P.1


lemma splitFromDiscrete {P : discreteFibration B} : split (P:=P.1) instCleavageValFibrationIsDiscreteOverBOverCatCategoryIsFibration :=
  by
    intro I X
    constructor

    let lift := Cleavage.Cart' (𝟙 _) X
    have ez : (coerc lift.φ).1 = (Cleavage.Cart' (𝟙 _) X).φ.1 := rfl
    have goal : isIdentity ( (coerc lift.φ).1) := discImpWeakDisc P.2 (coerc lift.φ)


    have isWeakDisc : weakDiscreteOverB P.1.1 := by apply discImpWeakDisc ; exact P.2
    exact isWeakDisc (coerc (Cleavage.Cart' (𝟙 I) X).φ)
    /-
    ∀ {J K} (u : J ⟶ I) (v : K ⟶ J) , ∃ p : (v * u * X).1 = ((v ≫ u) * X).1 ,
    eqToHom p ≫ Cart (v ≫ u) X = Cart v (u * X) ≫ Cart u X
    -/
    intro J K u v
    apply extInv (transLift (Cleavage.Cart' u X).1 (Cleavage.Cart' v (u * X)).1) ((Cleavage.Cart' (v ≫ u) X).1)
    exact uniqueLiftFromDiscreteness P.2

def Fib (B : Cat) : Cat :=Bundled.of (fibration B)
@[simps] def yoObj {B : Cat.{v₁,u₁ }} (P : fibration B) : (Fib B) ᵒᵖ ⥤ Cat where
  obj := fun Q ↦ ⟨ Q.unop ⟶ P , instCategoryHomFibrationToQuiverToCategoryStructInstCategoryFibration⟩
  map := fun F ↦  (Bicategory.precomposing _ _ P).obj F.unop
--def precomp {C : Cat.{v₁,u₁}} {D : Cat.{v₂,u₂}} {E : Cat.{v₃,u₃}} (F : C ⥤ D) : (D ⥤ E)  ⥤ (C ⥤ E)
 -- where --


@[simps] def PSh_rest {C : Cat.{v₁,u₁}} {D : Cat.{v₂,u₂}} (F : C ⥤ D) : PShCat.{v₂ , u₂ , s₁ , t₁} D ⥤ PShCat.{v₁ , u₁ , s₁ , t₁} C where
  obj := fun G ↦ F.op ⋙ G
  map := CategoryTheory.whiskerLeft F.op


@[simps] def yo  {B : Cat.{v₁,u₁ }} : Fib B ⥤ PShCat (Fib B) where
  obj := yoObj
  map := fun f ↦ ⟨ fun X ↦  (Bicategory.postcomposing _ _ _).obj f ,  by intro Y Z g ; apply strongAssoc  ⟩
  map_id := fun X ↦ by apply NatTrans.ext' ; ext ; aesop
  map_comp := fun f g ↦ by apply NatTrans.ext' ; ext ; aesop
def U (P : splitFibration B) : fibration B := P.1
def psh {B : Cat} : (Fib B) ⥤ PShCat B := yo ⋙ (PSh_rest (fundamentalFibration (B:=B)))
def Sp {B : Cat} : (Fib B) ⥤ splitFibration B := psh ⋙ Grothendieck
-- def myId {B : Cat} {I : ↑ B} : obj_over (P:=fundamentalFibration.obj I) I := ⟨ Over.mk (𝟙 I ) , rfl ⟩

variable {P : fibration B}

@[simp]def E_obj_obj {I : B} (X : (fundamentalFibration.obj I ⟶ P)) :  obj_over (P:=P.1.hom) I := (X / I).obj ⟨Over.mk (𝟙 I ) , rfl ⟩

@[simps] def E_obj_map {I : B} {F G : (fundamentalFibration.obj I ⟶ P)} (f : F ⟶ G) : E_obj_obj F ⟶E_obj_obj G
  := ⟨ rewrittenTrafo f.1 ⟨ Over.mk (𝟙 I ) , rfl ⟩ , by apply f.2⟩
@[simp] lemma cartesianIdTrans' {A : B} {T : obj_over A} (F : P ⥤c Q) : rewrittenTrafo (𝟙 F.1.1) T = 𝟙 ((F / A).obj T).1 := by simp ; aesop
@[simp] lemma idCartFunctor {P Q : fibration B} (F : P ⟶ Q) : ∀ X,  ((𝟙 F : F =>c F).1).app X = 𝟙 (F.1.left.obj X) := fun X ↦ rfl

def E_obj_map_id {I : B} (X : (fundamentalFibration.obj I ⟶ P)) :
  E_obj_map (𝟙 X) = 𝟙 (E_obj_obj X) := by
  apply Subtype.ext ; rw [E_obj_map]
  aesop

-- def E_obj_map_comp
@[simps!] def E'_obj  {I : B} : (fundamentalFibration.obj I ⟶ P) ⥤ obj_over (P:=P.1.hom) I where
  obj := fun X ↦ E_obj_obj X
  map := fun f ↦ E_obj_map f
  map_id := fun X ↦ E_obj_map_id X
  map_comp := fun f g ↦ by apply Subtype.ext ; unfold E_obj_map ; aesop

-- def E' : yo ⋙ (PSh_rest (fundamentalFibration (B:=B)))
