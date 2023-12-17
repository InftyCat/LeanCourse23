import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import LeanCourse.Project.FiberedCategories
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
variable {B : Cat.{v₁ , v₁}} {I J K : B}
notation (priority := high) P "[" A "]" => obj_over (P:=P.hom) A
instance : Category (Over I) := commaCategory
def isSingleton (X : Type _) : Prop := ∃ x : X , ∀ y : X , x = y
def isSingletonImpIsProp {X : Type _} (s : isSingleton X) (y y' : X) :  y = y' := by
  trans s.choose
  · symm ; exact s.choose_spec y
  · exact s.choose_spec y'
-- def isDiscreteFibration (P : fibration B) := weakDiscreteOverB P.1
def isDiscreteOverB (P : Over B) : Prop := ∀ {J I} (u : J ⟶ I ) (X : obj_over (P:=P.hom) I),
 isSingleton (liftOfAlong X u )

def discreteIsCartesian  {P : Over B} (disc : isDiscreteOverB P) : fibration B := ⟨ P , fun {J I} u X ↦ by

  let φ : liftOfAlong X u  := (disc u X).choose
  use φ
  intro K v Z
  simp at K
  let ψ := (disc v (φ.1)).choose
  let tLift := transLift φ ψ
  have this : Z = tLift :=  isSingletonImpIsProp (disc _ _) Z tLift
  rw [this]
  use ψ.φ
  constructor
  rfl
  intro y _
  let ψ' : liftOfAlong φ.Y v := ⟨ _ , y⟩
  have goal : ψ' = ψ := isSingletonImpIsProp (disc _ _) ψ' ψ
  trans ψ'.φ
  rfl
  congr
  ⟩

def weakDiscreteOverB (P : Over B) := ∀ {D : B} {X Y : obj_over (P:=P.hom) D} (f : X ⟶ Y) , isIdentity f.1

def Ov (I : B) : Cat := ⟨  Over I , commaCategory  ⟩
def domainOver (I : B) : Over B where
  left := Ov I
  right := default
  hom := Over.forget I

def domainLift {A : B} (u : J ⟶ I) (X : obj_over I) : liftOfAlong (B:=B) (P:=(domainOver A).hom) X u := by
      let a := u ≫ eqToHom (symm X.2)
      let y : J ⟶ A  := a ≫ X.1.hom
      let Y : obj_over (P:=(domainOver A).hom) J := ⟨ Over.mk y , rfl⟩
      let α : Y.1 ⟶ X.1 := Over.homMk a
      -- let hα : (domainOver A).hom.map α ≫ eqToHom (_ : (domainOver A).hom.obj ↑X = I) = eqToHom (_ : (domainOver A).hom.obj ↑Y = J) ≫ u
      exact ⟨Y , ⟨ α , by rw [eqToHom_refl , Category.id_comp ] ; apply (comp_eqToHom_iff _ _ _).2 ; aesop⟩  ⟩

lemma strongDiscreteness {A : B} (u : J ⟶ I ) (X : obj_over I)
  (L : liftOfAlong (P:=(domainOver A).hom) X u) :  ∃ (p :  L.Y.1 = (domainLift u X).Y.1) , L.φ.1 = eqToHom p ≫ (domainLift u X).φ.1  := by
  obtain ⟨ Y , φ ⟩ := L
  obtain ⟨φ , hφ⟩ := φ
  let p : Y.1 = (domainLift u X).Y.1 := by
    apply Subtype.ext
  use p
  have lol : φ.left = u
  have this : Y.1.hom = φ.left ≫ X.1.hom := by aesop
  simp
  apply Over.OverMorphism.ext
lemma domainIsDiscrete (A : B) : isDiscreteOverB (domainOver A) := fun {J I} u X ↦ by use (domainLift u X) ; sorry



/- lemma domainIsDisc : isDiscrete (domainFibration A) := fun {D} {X} {Y} f ↦ by
  let p : X.1 = Y.1 := by
    sorry
  use p
  apply Over.OverMorphism.ext
  let helper : f.1.left = CategoryTheory.eqToHom (_root_.trans X.2 (symm Y.2))
    := by rw [← eqToHom_trans] ;  apply (comp_eqToHom_iff _ _ _).1 ; exact f.2
  rw [helper]
  sorry

  /-
   ∀ {K : B} (v : K ⟶ J) (L: liftOfAlong X (v ≫u )) ,
    ∃! ψ : over_hom v L.Y τ.Y , ψ.1 ≫ τ.φ.1 = L
  -/
-/
def domainFibration (A : B) : fibration B := discreteIsCartesian (domainIsDiscrete A)
