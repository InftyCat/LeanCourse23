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
def und {P Q : fibration B} {F G : P ⟶ Q} (η : F ⟶ G) : F.1.1 ⟶ G.1.1 := η.1
@[simp] def whiskerLeft {P Q R : fibration B} (F : P ⥤c Q)
{G H : Q ⥤c R} (η : G =>c H) : ((F ≫ G) =>c (F ≫ H)) := ⟨ CategoryTheory.whiskerLeft F.1.1 η.1 ,  fun {A} T ↦  η.2 (( F / A).obj (T))⟩
@[simp] def whiskerRight {P Q R : fibration B} {G H : P ⥤c Q}   (η : G =>c H) (F : Q ⥤c R)
: ((G ≫ F) ⟶ (H ≫ F)) := ⟨ CategoryTheory.whiskerRight η.1 F.1.1  ,  fun {A} T ↦ ((F / A).map ((trafoOnFibers η A).app T)).2⟩

instance : Bicategory (fibration B) where
  whiskerLeft := whiskerLeft
  whiskerRight := fun η F ↦ whiskerRight η F
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

class isEquivalenceInBicategory {C : Type u₁ } [Bicategory C] {P Q  : C}  (F : P ⟶ Q) where
  /-- The inverse functor to `F` -/
  inverse : Q ⟶ P
  /-- Composition `F ⋙ inverse` is isomorphic to the identity. -/
  unitIso : 𝟙 P ≅ F ≫ inverse
  /-- Composition `inverse ⋙ F` is isomorphic to the identity. -/
  counitIso : inverse ≫  F ≅ 𝟙 Q
--theorem strongAssoc {P Q RS : fibration B} {F : P ⟶ Q}{H : R ⟶ S} : (F ≫ G) ≫ H = F ≫ G ≫ H := by rw [Category.assoc]
open Bicategory

theorem strongAssoc {P Q R S : fibration B} {F : P ⟶ Q}{H : R ⟶ S} :
  (postcomposing Q R S).obj H ⋙ (precomposing P Q S).obj F = (precomposing P Q R).obj F ⋙ (postcomposing P R S).obj H := by

  apply Functor.ext ; swap

  simp
  intro X Y η
  rw [eqToHom_refl,eqToHom_refl,Category.comp_id,Category.id_comp]
  rw [Functor.comp_map,Functor.comp_map,]
  apply Subtype.ext
  rfl
