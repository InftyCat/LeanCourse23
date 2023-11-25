
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

set_option autoImplicit true

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].
variable {𝕏 : Type u₂} {B : Type u₁} [Category.{v₁} B] [Category.{v₂} 𝕏] {P : 𝕏 ⥤ B}
namespace FiberedCategories

def comp {X Y Z : B}  : (X ⟶ Y) → (Y ⟶ Z ) → (X ⟶ Z) := fun f g => f ≫ g
def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := by rw [h]  ; exact f
--subst h := by sorry

def isCartesian {X Y : 𝕏} (φ : Y ⟶ X) := ∀ {Z : 𝕏} (v : P.obj Z ⟶ P.obj Y) (θ : Z ⟶ X) , ∃! (ψ : Z ⟶ Y) , P.map ψ = v ∧ ψ ≫ φ = θ
def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') := {α : X.1 ⟶ X'.1 // substCod X'.2 (P.map α) = substDom X.2 (u) }

structure mor_over {A A' : B} (u : A ⟶ A') where
  X : obj_over ( P := P) A
  X' : obj_over ( P := P) A'
  α : X.1 ⟶ X'.1
  isLift : substCod X'.2 (P.map α) = substDom X.2 (u)
def verticalOver (A : B) := mor_over (P := P) (𝟙 A)



instance Fib : Category (obj_over ( P:= P) A) where
  Hom ( X X' : obj_over A) := over_hom (𝟙 A) X X' -- { α : verticalOver A // α.X = X ∧ α.X' = X' }
  id (X : obj_over A) := ⟨ 𝟙 X.1 , by sorry ⟩
  comp {X} {Y} {Z} f g := ⟨  f.1 ≫ g.1 , by  sorry ⟩


end FiberedCategories
