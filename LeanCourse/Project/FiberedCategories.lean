
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
structure over {A A' : B} {u : A ⟶ A'} where
  X : 𝕏
  X' : 𝕏
  hY : P.obj X = A
  hZ : P.obj X' = A'
  isLift : substCod hZ (P.map α) = substDom hY (u)
def verticalOver {X Y : 𝕏} (A : B) (α : Y ⟶ X) := ∃ (hY : P.obj Y = A) (hZ : P.obj X = A) , substCod hZ (P.map α) = substDom hY (𝟙 A)
example {X : 𝕏} : verticalOver (P := P) (P.obj X) (𝟙 X) := by
  use rfl , rfl
  aesop_cat
structure FiberOver (A : B) where
  X : 𝕏
  Y : 𝕏
  α : Y ⟶ X
  isvert : verticalOver ( P:=P) A α


-- instance Fib (A : B) : Category where

end FiberedCategories
