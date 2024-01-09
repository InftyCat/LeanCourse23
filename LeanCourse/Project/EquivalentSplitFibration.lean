import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration
import LeanCourse.Project.SplitFibrationViaGrothendieck
import LeanCourse.Project.FibrationBicategory
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

noncomputable def cartesianLiftFromFibration (P : fibration B) {J I} (u : J ⟶ I) (X : P[I]) : cartesianLiftOfAlong X u := ⟨(P.2 u X).choose , (P.2 u X).choose_spec⟩



def discreteFibration (B : Cat) := {P : fibration B //  isDiscreteOverB P.1}


noncomputable instance {P : discreteFibration B} : Cleavage P.1 where
  Cart' :=  cartesianLiftFromFibration P.1

lemma splitFromDiscrete {P : discreteFibration B} : split (P:=P.1) instCleavageValFibrationIsDiscreteOverBOverCatCategoryForAllαCategoryHomToQuiverToCategoryStructStrObj_overObjToQuiverToCategoryStructToPrefunctorIdLeftDiscretePUnitDiscreteCategoryFromPUnitObjToQuiverToCategoryStructToPrefunctorRightHomExistsLiftOfAlongIsCartesian :=
  by
    intro I X
    constructor
    -- let f := by sorry (cartesianLiftFromFibration P (𝟙 _) X).1
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
    have myident : transLift (Cleavage.Cart' u X).1 (Cleavage.Cart' v (u * X)).1 = (Cleavage.Cart' (v ≫ u) X).1
      :=  uniqueLiftFromDiscreteness P.2

    let p : (v * u * X).1 = ((v ≫u ) * X).1 := by
      calc
      (v * u * X).1 =  (transLift (Cleavage.Cart' u X).1 (Cleavage.Cart' v (u * X)).1).Y := by rfl
       _ = (Cleavage.Cart' (v ≫ u) X).1.Y := by rw [myident]
       _ = ((v ≫u ) * X).1 := rfl
    use p

    -- have goal : isIdentity (↑) := by apply isWeakDisc

    sorry --

  /-

  def split {P : fibration B} (c : Cleavage P) : Prop :=
  ∀ {I} (X : P[I]) , isIdentity (Y:=X.1) (Cart (𝟙 I) X)  ∧
  ∀ {I J K} (u : J ⟶ I) (v : K ⟶ J) (X : P[I]) , ∃ p : (v * u * X).1 = ((v ≫ u) * X).1 ,
    eqToHom p ≫ Cart (v ≫ u) X = Cart v (u * X) ≫ Cart u X
  -/



def Fib (B : Cat) : Cat :=Bundled.of (fibration B)
def yo_obj {B : Cat.{v₁,u₁ }} (P : fibration B) : (Fib B) ᵒᵖ ⥤ Cat where
  obj := fun Q ↦ ⟨ Q.unop ⟶ P , instCategoryHomFibrationToQuiverToCategoryStructInstCategoryFibration⟩
  map := fun F ↦  (Bicategory.precomposing _ _ P).obj F.unop
--def precomp {C : Cat.{v₁,u₁}} {D : Cat.{v₂,u₂}} {E : Cat.{v₃,u₃}} (F : C ⥤ D) : (D ⥤ E)  ⥤ (C ⥤ E)
 -- where --


def PSh_rest {C : Cat.{v₁,u₁}} {D : Cat.{v₂,u₂}} (F : C ⥤ D) : PShCat.{v₂ , u₂ , s₁ , t₁} D ⥤ PShCat.{v₁ , u₁ , s₁ , t₁} C where
  obj := fun G ↦ F.op ⋙ G
  map := CategoryTheory.whiskerLeft F.op


def yo  {B : Cat.{v₁,u₁ }} : Fib B ⥤ PShCat (Fib B) where
  obj := yo_obj
  map := fun f ↦ ⟨ fun X ↦  (Bicategory.postcomposing _ _ _).obj f ,  by sorry ⟩
  map_id := fun X ↦ sorry
  map_comp := by sorry
def U (P : splitFibration B) : fibration B := P.1
def Sp {B : Cat} : (Fib B) ⥤ splitFibration B := yo ⋙ (PSh_rest (domainFibration (B:=B))) ⋙ Grothendieck
-- def myId {B : Cat} {I : ↑ B} : obj_over (P:=domainFibration.obj I) I := ⟨ Over.mk (𝟙 I ) , rfl ⟩

variable {P : fibration B}

def E_obj_obj {I : B} (X : (domainFibration.obj I ⟶ P)) :  obj_over (P:=P.1.hom) I := (X / I).obj ⟨Over.mk (𝟙 I ) , rfl ⟩

def E_obj_map {I : B} {F G : (domainFibration.obj I ⟶ P)} (f : F ⟶ G) : E_obj_obj F ⟶E_obj_obj G
  := ⟨ rewrittenTrafo f.1 ⟨ Over.mk (𝟙 I ) , rfl ⟩ , by apply f.2⟩
@[simp] lemma cartesianIdTrans' {A : B} {T : obj_over A} (F : P ⥤c Q) : rewrittenTrafo (𝟙 F.1.1) T = 𝟙 ((F / A).obj T).1 := by simp ; aesop
@[simp] lemma idCartFunctor {P Q : fibration B} (F : P ⟶ Q) : ∀ X,  ((𝟙 F : F =>c F).1).app X = 𝟙 (F.1.left.obj X) := fun X ↦ rfl
/-
  --def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
  @[simp] def compCartTrans {F G H: P ⥤c Q} (η: F =>c G) (ε : G =>c H) : F =>c H := ⟨
     η.1 ≫ ε.1  ,
    fun T ↦ by
      have toProve : rewrittenTrafo (η.1 ≫ ε.1) T = rewrittenTrafo η.1 T ≫ rewrittenTrafo ε.1 T := by simp ; aesop
      rw [toProve]
      apply compPresVertical
      exact η.2 T
      exact ε.2 T

    ⟩
-/
def E_obj_map_id {I : B} (X : (domainFibration.obj I ⟶ P)) :
  E_obj_map (𝟙 X) = 𝟙 (E_obj_obj X) := by
  apply Subtype.ext ; rw [E_obj_map]
  have lol' : 𝟙 ((X.1).left.obj (Over.mk (𝟙 I))) = 𝟙 (E_obj_obj X).1 := rfl
  simp
  assumption

-- def E_obj_map_comp
def E_obj {I : B} : (domainFibration.obj I ⟶ P) ⥤ obj_over (P:=P.1.hom) I where
  obj := fun X ↦ E_obj_obj X
  map := fun f ↦ E_obj_map f
  map_id := fun X ↦ E_obj_map_id X
  map_comp := sorry

/-
lemma SpP {I : B} : (Sp.obj P) ↓ I ≅ Bundled.of (domainFibration.obj I ⟶ P) := by sorry
def E : Sp.obj P ⥤c P := ⟨ by sorry , by sorry ⟩
-/
