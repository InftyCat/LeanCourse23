import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition

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
local notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
variable {B : Cat.{v₁ , u₁}} {I J K : B}
-- scoped infixr:80 " >> " => fun F G => transLift G F

-- scoped infixr:80 " ↓ " => fun P A =>obj_over (P:=P.1.hom) A


class Cleavage (P : fibration B)  : Type (max u₁ v₁) where
  Cart' : ∀ {J I : B} (u : J ⟶ I ) (X: P[I] ) , cartesianLiftOfAlong (P:=P.1.hom) X u

open Cleavage

scoped notation u " * " X => (Cart' u X).Y
variable  {P : fibration B} [Cleavage P]
-- scoped notation "Cart" u:0 X:0 => (Cart' u X).φ.1 -- would prefer that TODO
-- notation "Cart u X => (Cart' u X).φ.1
@[simp] def Cart {J I : B} (u : J ⟶ I) (X : P[I]) : (u * X).1 ⟶ X.1 := (Cart' u X).φ.1 --abbrev seems to yield problems later letting aesop show, that splitfibrations form a category







def map' {P : fibration B} {J I : B} {X Y : P[I]}  (u : J ⟶ I) (α : X ⟶ Y )
  (uX : cartesianLiftOfAlong X u) (uY : cartesianLiftOfAlong Y u):
  ∃! φ : uX.Y ⟶ uY.Y , φ.1 ≫ uY.φ.1 = uX.φ.1 ≫ α.1 := by

    let lift : liftOfAlong Y (u ≫ 𝟙 I) := transLift ⟨ _ , coercBack α⟩  (uX).1
    let lift' : liftOfAlong Y (u ) := transportLift (by rw [Category.comp_id ]) lift
    exact (weakCartifCartesian (uY) lift')


    -- exact uniq
notation u " ⋆ " f => map' u f (Cart' u _) (Cart' u _)
/-
Remark: The reason why map' is so general (instead of just talking about the preferred cartesian lifts Cart') is that I thought I need
the map for any choice of lift
-/
--notation (priority := high) u " ⋆ " f => map' u f

lemma map_comp'  (u : J ⟶ I) {X Y Z : P[I]}
(α : X ⟶Y) (β : Y ⟶Z ) : (u ⋆ α).choose ≫(u ⋆ β).choose = (u ⋆ (α≫β) ).choose := by
    let hcomp := (u ⋆ (α ≫β  )).choose_spec
    let hφ :=  ((u ⋆ α).choose_spec).1
    let hψ :=  ((u ⋆ β).choose_spec).1
    apply hcomp.2
    have hφ : ((u ⋆ α).choose).1 ≫ (Cart (u) (Y)) =  (Cart u X) ≫ α.1 := hφ
    have hψ : ((u ⋆ β).choose).1 ≫ Cart u Z =  Cart u Y ≫ β.1 := hψ
    have ass : (Cart' u X).φ.1 ≫ (α ≫ β).1 = ((Cart' u X).φ.1 ≫ α.1) ≫ β.1 := by
      rw [Category.assoc] ;
      simp
    rw [ass]
    have hts : ((u ⋆ α).choose.1 ≫(u ⋆ β).choose.1) ≫ Cart u Z
      = (Cart u X ≫ α.1) ≫ β.1 := by rw [Category.assoc , hψ , ← Category.assoc , hφ] ;
    exact hts
lemma map_id' {P : fibration B} [Cleavage P] (u : J ⟶ I) {X : P[I]} :
  𝟙 _ = (u ⋆ (𝟙 X)).choose := by
    apply ((u ⋆ (𝟙 X) ).choose_spec).2
    aesop_cat
/-
Remark: Note, that even we have already choosen a cleavage the following functor is still not computable, because lean has to choose
(although it is unique) the morphism from map'.
-/

noncomputable def reindexing  {P : fibration B} [Cleavage P] (u : J ⟶ I) : P[I] ⥤ P[J] where
  obj := fun X ↦ u * X
  map := fun {X}{Y} α ↦ (u ⋆ α).choose
  map_comp := fun {X} {Y} {Z} α β ↦ by symm ; exact (map_comp' u α β)
  map_id := fun X ↦ by symm ; exact map_id' (P:=P) u

def c {P : fibration B} [Cleavage P]  (u : J ⟶ I) (v : K ⟶ J) (X : P[I]) :
   ∃! α : (v * (u * X)) ≅ (v ≫u ) * X ,
   (α.hom.1 ≫ Cart (v ≫ u) X) = Cart v (u * X) ≫ Cart u X  := by
  let Y : cartesianLiftOfAlong X (v ≫u ):=⟨ transLift (Cart' u X).1 (Cart' v (u * X)).1  , compPresCartesian _ _⟩
  exact cartesianLiftIsUnique (Cart' (v ≫ u) X) Y
