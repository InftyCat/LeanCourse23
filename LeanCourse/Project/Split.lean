import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage

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
def split {P : fibration B} (c : Cleavage P) : Prop :=
  ∀ {I} (X : P[I]) , isIdentity (Y:=X.1) (Cart (𝟙 I) X)  ∧
  ∀ {J K} (u : J ⟶ I) (v : K ⟶ J) , ∃ p : (v * u * X).1 = ((v ≫ u) * X).1 ,
    eqToHom p ≫ Cart (v ≫ u) X = Cart v (u * X) ≫ Cart u X
structure splitFibration (B : Cat) where
 P : fibration B
 c : Cleavage P
 isSplit : split c
instance : CoeOut (splitFibration B) (fibration B) := ⟨ fun α ↦ α.1⟩
instance (P : splitFibration B) : Cleavage P.1 where
  Cart' := P.c.Cart'
def fiber_Cat (F : splitFibration B) (I : B) : Cat where
  α := obj_over (P:=F.1.1.hom) I
scoped infixr:80 " ↓ " => fiber_Cat


def splitCartesianFunctor (P Q : splitFibration B) := {F : P ⥤c Q.1 //
  ∀ {I} {J} (u : J ⟶ I) (X) ,
    ∃ (p : (u * ((F / I).obj X)).1 = (F / J).obj (u * X) ) ,
    eqToHom p ≫ (F.1.left).map (Cart u X) = Cart u ((F / I).obj X) }
scoped notation P "⥤cs" Q => splitCartesianFunctor P Q
-- scoped infixr:80 " >> " => fun F G => transLift G F

def compOfSplitFuncsPath {P Q R : splitFibration B} (F : P ⥤cs Q) (G: Q ⥤cs R) {u : J ⟶I} {X} :
 (u * ((F.1≫G.1 / I ).obj X)).1  = ((F.1≫G.1 / J ).obj (u * X)).1  := by
  let FX := (F.1 / I).obj X
  have p' : (u * ((G.1 / I).obj FX)).1 = (G.1 / J).obj (u * FX) :=    (G.2 u FX).choose
  have q :  (u * ((F.1 / I).obj X)).1 = ((F.1 / J).obj (u * X)).1 :=  (F.2 u X).choose
  calc (u * ((F.1≫G.1 / I ).obj X)).1
      = (u * ((G.1 / I).obj FX)).1 := rfl
    _ = ((G.1 / J).obj (u * ((F.1 / I).obj X))).1 := p'
    _ = G.1.1.left.obj ((u * ((F.1 / I).obj X)).1) := rfl
    _ = G.1.1.left.obj ((F.1 / J).obj (u * X)).1 := by rw [q]
    _ = ((G.1 / J).obj ((F.1 / J).obj (u * X))).1 := rfl
    _ = ((F.1≫G.1 / J ).obj (u * X)).1 := rfl
def compOfSplitFuncs {P Q R : splitFibration B} (F : P ⥤cs Q) (G: Q ⥤cs R) :
  P ⥤cs R := ⟨ F.1 ≫ G.1 , fun {I} {J} u X ↦ by
  let FX := (F.1 / I).obj X
  have p' : (u * ((G.1 / I).obj FX)).1 = (G.1 / J).obj (u * FX) :=    (G.2 u FX).choose
  --
  have q :  (u * ((F.1 / I).obj X)).1 = ((F.1 / J).obj (u * X)).1 :=  (F.2 u X).choose
  have p : (u * ((F.1≫G.1 / I ).obj X)).1  = ((F.1≫G.1 / J ).obj (u * X)).1 := compOfSplitFuncsPath F G
  use p
  have sth : eqToHom p = eqToHom p' ≫ G.1.1.left.map (eqToHom q) := by rw [eqToHom_map , eqToHom_trans]
  rw [sth, Category.assoc]
  have this : G.1.1.left.map (eqToHom q) ≫ G.1.1.left.map (F.1.1.left.map (Cart u X) ) =
    (G.1.1.left).map (Cart u (((F.1 / I).obj X)))  := by
      rw [← Functor.map_comp ]
      exact congr_arg G.1.1.left.map ((F.2 u X).choose_spec)
  have bf : G.1.1.left.map (F.1.1.left.map (Cart u X) ) = ((F.1 ≫ G.1).1).left.map (Cart u X) := rfl
  rw [← bf , whisker_eq (eqToHom p') this]
  rw [(G.2 u FX).choose_spec]
  simp⟩
@[simp , ext] lemma extSplitFunc {P Q : splitFibration B} (F G : P ⥤cs Q) (t : F.1 = G.1) : F = G := Subtype.ext t
instance : Category (splitFibration B) where
  Hom := splitCartesianFunctor
  id := fun P ↦ ⟨ (𝟙 P.1) , fun u X ↦ by use rfl ; simp ; aesop ⟩
  comp := compOfSplitFuncs
