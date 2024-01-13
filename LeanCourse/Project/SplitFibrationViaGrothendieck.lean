import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Grothendieck
-- import Mathlib.CategoryTheory.Bundled
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration


set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 1500000
set_option quotPrecheck false

universe v₁ u₁ v₂ u₂   --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories
-- notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
variable {B : Cat.{v₁ , u₁}} {I J K : B}
-- def tot' (P : PShCat B) : Type _ := ()
def tot (P : PShCat.{v₁ , u₁ , s₁ , t₁ } B) : Cat.{max v₁ t₁,max u₁ s₁ } := Bundled.of (CategoryTheory.Grothendieck P) -- , Grothendieck.instCategoryGrothendieck⟩
def totop (P : PShCat.{v₁ , u₁ , s₁ , t₁ } B) : Cat.{_,_} := Bundled.of ((tot P)ᵒᵖ)
--Bundled.of (tot' P) Grothendieck.instCategoryGrothendieck
-- def coercCat (B : Cat.{v₁ , u₁ }) : Cat.{max v₁ v₂ , max u₁ u₂} := by sorry
-- def coercType (B : Type u₁ ) : Type (max u₁ v₁) := B
variable {B : Cat.{v₁,v₁}}

def Grth (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) : Over (B) :=
Over.mk ( by
  let erg : totop P ⟶ B := Functor.leftOp (CategoryTheory.Grothendieck.forget P) -- (coercCat.{_,_,u₁,v₁} B)
  exact erg
  )
def fiberToSection {P : PShCat.{v₁ , v₁ , v₁ , v₁ } B} {I : ↑ B} (X : obj_over (P:=(Grth P).hom) I) :
 P.obj (Opposite.op I) := (P.map (eqToHom (congrArg Opposite.op X.2))).obj (X.1.1.2)
def sectionToFiber  {P : PShCat.{v₁ , v₁ , v₁ , v₁ } B} {I : ↑ B} (X : P.obj (Opposite.op I)) : obj_over (P:=(Grth P).hom) I := by
  use ⟨Opposite.op I , X⟩
  rfl
def cleavage (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) {J I : ↑B}
  (u : J ⟶ I)
  (X : obj_over (P:=(Grth P).hom) I) : cartesianLiftOfAlong (P:=(Grth P).hom) X u := by

  let φ : liftOfAlong X u := by
    let Y:= sectionToFiber <| (P.map u.op).obj (fiberToSection X)
    use Y
    let u' : Y.1 ⟶ X.1 := by
      use eqToHom (congrArg Opposite.op X.2) ≫  u.op ≫  (eqToHom <| symm (congrArg Opposite.op Y.2))
      sorry
    use u'
    sorry
  use φ
  sorry

def Grothendieck_obj (P : PShCat B) : splitFibration B where
  P:= ⟨Grth P , fun u X ↦ by
    let cl := cleavage P u X
    exact ⟨cl.1 , cl.2⟩
    ⟩
  c := ⟨cleavage P  ⟩
  isSplit := by sorry


def Grothendieck : PShCat B ⥤ splitFibration B where
  obj := fun P => Grothendieck_obj P
  map := by sorry
  map_comp := by sorry
  map_id := by sorry
