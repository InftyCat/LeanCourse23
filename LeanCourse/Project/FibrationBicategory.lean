import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Bicategory.Basic
import LeanCourse.Project.FiberedCategories
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 500000
universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].
variable {B : Cat.{v₁, u₁}}
namespace FiberedCategories
def whiskerLeft {P Q R : fibration B} (F : P ⥤c Q)
{G H : Q ⥤c R} (η : G =>c H) : ((F ≫ G) =>c (F ≫ H)) := ⟨ Bicategory.whiskerLeft F.1.1 η.1 ,  fun {A} T ↦ by sorry⟩

instance : Bicategory (fibration B) where
  whiskerLeft := whiskerLeft
  whiskerRight := by sorry
  associator := by sorry
  leftUnitor := by sorry
  rightUnitor := by sorry
  whiskerLeft_id := by sorry
  whiskerLeft_comp := by sorry
  id_whiskerLeft  := by sorry
  comp_whiskerLeft := by sorry
  id_whiskerRight  := by sorry
  comp_whiskerRight  := by sorry
  whiskerRight_id  := by sorry
  whiskerRight_comp  := by sorry
  whisker_assoc := by sorry
  whisker_exchange := by sorry
  pentagon  := by sorry
  triangle := by sorry
