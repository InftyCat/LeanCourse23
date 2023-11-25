
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
def univ {Y Z : B} (h : Y = Z) : Y ⟶ Z := by rw [h] ; exact 𝟙 Z
def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := f ≫univ h -- by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := univ h ≫ f -- by rw [h]  ; exact f


def isCartesian {X Y : 𝕏} (φ : Y ⟶ X) := ∀ {Z : 𝕏} (v : P.obj Z ⟶ P.obj Y) (θ : Z ⟶ X) , ∃! (ψ : Z ⟶ Y) , P.map ψ = v ∧ ψ ≫ φ = θ

def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') := {α : X.1 ⟶ X'.1 //
   P.map α ≫ univ X'.2  = univ X.2 ≫ u }


instance Fib : Category (obj_over ( P:= P) A) where
  Hom ( X X' : obj_over A) := over_hom (𝟙 A) X X' -- { α : verticalOver A // α.X = X ∧ α.X' = X' }
  id (X : obj_over A) := ⟨ 𝟙 X.1 , by
    rw [@Functor.map_id]
    aesop_cat
    ⟩
  comp {X} {Y} {Z} f g := ⟨  f.1 ≫ g.1 , by
    rw [@Functor.map_comp]
    rw [Category.assoc]
    rw [g.2]
    rw [← Category.assoc]
    rw [f.2]
    aesop_cat
     ⟩
structure cartesianLift {J I : B} (u : J ⟶ I) ( X : obj_over (P:=P) I) where
  Y : obj_over (P:=P) J
  φ : over_hom u Y X
  isCart : isCartesian (P := P) φ.1
def fibration := ∀ {J I : B} (u : J ⟶ I) (X : obj_over I) , cartesianLift ( P:=P) u X


end FiberedCategories
