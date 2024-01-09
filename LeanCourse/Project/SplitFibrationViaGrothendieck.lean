import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Grothendieck
-- import Mathlib.CategoryTheory.Bundled
import LeanCourse.Project.FiberedCategories
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
variable {B : Cat.{v₁ , u₁}} {I J K : B}
-- def tot' (P : PShCat B) : Type _ := ()
def tot (P : PShCat.{v₁ , u₁ , s₁ , t₁ } B) : Cat.{max v₁ t₁,max u₁ s₁ } := Bundled.of (CategoryTheory.Grothendieck P) -- , Grothendieck.instCategoryGrothendieck⟩
def totop (P : PShCat.{v₁ , u₁ , s₁ , t₁ } B) : Cat.{_,_} := Bundled.of ((tot P)ᵒᵖ)
--Bundled.of (tot' P) Grothendieck.instCategoryGrothendieck
-- def coercCat (B : Cat.{v₁ , u₁ }) : Cat.{max v₁ v₂ , max u₁ u₂} := by sorry
-- def coercType (B : Type u₁ ) : Type (max u₁ v₁) := B
variable {B : Cat.{v₁,v₁}}
def Grothendieck_obj' (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) : Over B := by
  apply Over.mk
  let Grothendieck_obj'' : totop P ⥤ ↑B := Functor.leftOp (CategoryTheory.Grothendieck.forget P) -- (coercCat.{_,_,u₁,v₁} B)
  -- let helper : (tot P)ᵒᵖ ⟶ B := Grothendieck_obj'
--max v₁ t₁ ,max u₁ s₁
  -- use Grothendieck_obj''
  sorry
  exact (totop P)

def Grothendieck_obj (P : PShCat B) : splitFibration B where
  P:= ⟨Grothendieck_obj' P , by sorry⟩
  c := by sorry
  isSplit := by sorry


def Grothendieck : PShCat B ⥤ splitFibration B where
  obj := fun P => Grothendieck_obj P
  map := by sorry
  map_comp := by sorry
  map_id := by sorry
