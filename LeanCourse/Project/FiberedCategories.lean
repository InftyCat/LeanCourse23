
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

def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := f ≫ CategoryTheory.eqToHom h -- by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := CategoryTheory.eqToHom h ≫ f -- by rw [h]  ; exact f




def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
instance : CoeSort (obj_over (P:=P) A) 𝕏 := ⟨fun α ↦ α.1⟩
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') := {α : X.1 ⟶ X'.1 //
   P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2 ≫ u }


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
structure liftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I)  where
  Y : obj_over (P:=P) J
  φ : over_hom u Y X
def isHyperCartesian {J I : B} {u : J ⟶ I} {X : obj_over (P:=P) I} (τ: liftOfAlong X u):=
  ∀ {K : B} (v : K ⟶ J) (L: liftOfAlong X (v ≫u )) ,
    ∃! ψ : over_hom v L.Y τ.Y , ψ.1 ≫ τ.2.1 = L.φ.1
def isCartesian {J I : B} {u : J ⟶ I} {X : obj_over (P:=P) I} (τ: liftOfAlong X u):=
  ∀ (L: liftOfAlong X (𝟙 J  ≫u )) ,
    ∃! ψ : L.Y  ⟶ τ.Y , ψ.1 ≫ τ.2.1 = L.φ.1
def cartesianLiftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I) := {L : liftOfAlong X u // isCartesian L }
theorem cartesianLiftIsUnique {J I : B} {u : J ⟶ I} {X : obj_over (P:=P) I} (L L' : cartesianLiftOfAlong X u) :
  ∃! α : L'.1.Y ≅ L.1.Y , α.hom.1 ≫ L.1.φ.1 = L'.1.φ.1 := by
    obtain ⟨Y , φ⟩ := L.1
    obtain ⟨Z , ψ⟩ := L'.1
    have this := L.2 -- (𝟙 _)
    have me := Category.id_comp u
    have Y' : liftOfAlong X (𝟙 J ≫ u):= by rw [me] ; exact L'.1

    -- specialize L.2 L'.1
    obtain ⟨ α , hα  ⟩ := this
    have α : Z ⟶ Y := by sorry
    let α : Z ≅ Y  := ⟨ α , by sorry , by sorry, by sorry ⟩

    use α

def fibration := ∀ {J I : B} (u : J ⟶ I) (X : obj_over I) , cartesianLiftOfAlong ( P:=P) X u


end FiberedCategories
