import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import LeanCourse.Project.FiberedCategories
set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 200000
set_option quotPrecheck false
universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories

variable {B : Cat.{v₁ , u₁}} {I J K : B}
-- scoped infixr:80 " >> " => fun F G => transLift G F

scoped infixr:80 " ↓ " => fun P A =>obj_over (P:=P.1.hom) A
notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A

class Cleavage (P : fibration B)  : Type (max u₁ v₁) where
  Cart' : ∀ {J I : B} (u : J ⟶ I ) (X: P[I] ) , cartesianLiftOfAlong (P:=P.1.hom) X u

open Cleavage

scoped notation u " * " X => (Cart' u X).Y
variable  {P : fibration B} [Cleavage P]
-- scoped notation "Cart" u X => (Cart' u X).φ.1 would prefer that TODO
def Cart {J I : B} (u : J ⟶ I) (X : P[I]) : (u * X).1 ⟶ X.1 := (Cart' u X).φ.1
def transport   {A A' : B} {u u' : A ⟶ A'} {X : P[A]} {X' : P[A']}
  (p : u = u') (f : over_hom u X X') : over_hom u' X X' := by
  use f.1
  rw [← whisker_eq (CategoryTheory.eqToHom X.2) p]
  exact f.2
def transportLift {J I : B} {X : P[I]} {u u' : J ⟶ I}(p : u = u')
  (L : liftOfAlong X u) : liftOfAlong (P:=P.1.hom) X u' := by
  obtain ⟨  Y , φ ⟩ := L
  exact ⟨ Y , transport p φ⟩

def map' {P : fibration B} [Cleavage P] {J I : B} {X Y : P[I]}  (u : J ⟶ I) (α : X ⟶ Y ) :
  ∃! φ : (u*X) ⟶ u * Y , φ.1 ≫ Cart u Y = Cart u X ≫ α.1 := by
    let sth : isCartesian (Cart' u Y).1 := (Cart' u Y).isCart
    let lift : liftOfAlong Y (u ≫ 𝟙 I) := transLift ⟨ _ , coercBack α⟩  (Cart' u X).1
    let lift' : liftOfAlong Y (u ) := transportLift (by rw [Category.comp_id ]) lift
    exact (weakCartifCartesian (Cart' u Y) lift')


    -- exact uniq
notation u " ⋆ " f => map' u f
--notation (priority := high) u " ⋆ " f => map' u f

lemma map_comp'  (u : J ⟶ I) {X Y Z : P[I]}
(α : X ⟶Y) (β : Y ⟶Z ) : (u ⋆ α).choose ≫(u ⋆ β).choose = (u ⋆ (α≫β) ).choose := by
    let hcomp := (u ⋆ (α ≫β  )).choose_spec
    let hφ :=  ((u ⋆ α).choose_spec).1
    let hψ :=  ((u ⋆ β).choose_spec).1
    apply hcomp.2
    have hφ : ((u ⋆ α).choose).1 ≫ Cart u Y =  Cart u X ≫ α.1 := hφ
    have hψ : ((u ⋆ β).choose).1 ≫ Cart u Z =  Cart u Y ≫ β.1 := hψ
    have ass : Cart u X ≫ (α ≫ β).1 = (Cart u X ≫ α.1) ≫ β.1 := by
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


noncomputable def reindexing  {P : fibration B} [Cleavage P] (u : J ⟶ I) : P[I] ⥤ P[J] where
  obj := fun X ↦ u * X
  map := fun {X}{Y} α ↦ (u ⋆ α).choose
  map_comp := fun {X} {Y} {Z} α β ↦ by symm ; exact (map_comp' u α β)
  map_id := fun X ↦ by symm ; exact map_id' (P:=P) u
def split {P : fibration B} (c : Cleavage P) : Prop :=
  ∀ {I} (X : P[I]) , isIdentity (Y:=X.1) (Cart (𝟙 I) X)  ∧
  ∀ {I J K} (u : J ⟶ I) (v : K ⟶ J) (X : P[I]) , ∃ p : (v * u * X).1 = ((v ≫ u) * X).1 ,
    eqToHom p ≫ Cart (v ≫ u) X = Cart v (u * X) ≫ Cart u X
structure splitFibration (B : Cat) where
 P : fibration B
 c : Cleavage P
 isSplit : split c
instance : CoeOut (splitFibration B) (fibration B) := ⟨ fun α ↦ α.1⟩
instance (P : splitFibration B) : Cleavage P.1 where
  Cart' := P.c.Cart'

def splitCartesianFunctor (P Q : splitFibration B) := {F : P ⥤c Q.1 //
  ∀ {I} {J} (u : J ⟶ I) (X : P.1 ↓ I) ,
    ∃ (p : (u * ((F / I).obj X)).1 = (F / J).obj (u * X) ) ,
    eqToHom p ≫ (F.1.left).map (Cart u X) = Cart u ((F / I).obj X) }
scoped notation P "⥤cs" Q => splitCartesianFunctor P Q
-- scoped infixr:80 " >> " => fun F G => transLift G F

def compOfSplitFuncs {P Q R : splitFibration B} (F : P ⥤cs Q) (G: Q ⥤cs R) :
  P ⥤cs R := ⟨ F.1 ≫ G.1 , fun {I} {J} u X ↦ by
  let FX := (F.1 / I).obj X
  have p' : (u * ((G.1 / I).obj FX)).1 = (G.1 / J).obj (u * FX) :=    (G.2 u ((F.1 / I).obj X)).choose
  --
  have q :  (u * ((F.1 / I).obj X)).1 = ((F.1 / J).obj (u * X)) :=  (F.2 u X).choose
  have p : (u * ((F.1≫G.1 / I ).obj X)).1  = ((F.1≫G.1 / J ).obj (u * X)).1 := by
    calc (u * ((F.1≫G.1 / I ).obj X)).1
      = (u * ((G.1 / I).obj FX)).1 := rfl
    _ = (G.1 / J).obj (u * ((F.1 / I).obj X)) := p'
    _ = ((G.1 / J).obj ((F.1 / J).obj (u * X))).1 := by rw [q]
    _ = ((F.1≫G.1 / J ).obj (u * X)).1 := rfl
    -- exact (F.2 u X).choose

  use p

  sorry ⟩


/-

instance : Category (splitFibration B) where
  Hom := splitCartesianFunctor
  id := fun P ↦ ⟨ (𝟙 P.1) , fun u X ↦ by use rfl ; simp ; aesop ⟩
  comp := compOfSplitFuncs
-/
