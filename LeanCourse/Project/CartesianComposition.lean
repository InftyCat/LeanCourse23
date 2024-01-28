import Mathlib.CategoryTheory.Over
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

variable {B : Cat.{v₁ , u₁}} {I J K : B}
notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
@[simps] def  transport  {P : fibration B} {A A' : B} {u u' : A ⟶ A'} {X : P[A]} {X' : P[A']}
  (p : u = u') (f : over_hom u X X') : over_hom u' X X' := by
  use f.1
  rw [← whisker_eq (CategoryTheory.eqToHom X.2) p]
  exact f.2

@[simp] def transportLift {J I : B} {P : fibration B} {X : P[I]} {u u' : J ⟶ I}(p : u = u')
  (L : liftOfAlong X u) : liftOfAlong (P:=P.1.hom) X u' := by
  obtain ⟨  Y , φ ⟩ := L
  exact ⟨ Y , transport p φ⟩
def over_hom_comp {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {X : P[I]} {Y:P[J]}{Z:P[K]}
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom (v ≫ u) Z X := (transLift ⟨ _ , φ ⟩ ⟨_ , ψ⟩ ).φ
@[simps!] def over_comp    {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {w : K ⟶ I} {X : P[I]} {Y:P[J]}{Z:P[K]}
  (comm : v ≫ u = w)
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom w Z X
  := transport comm (over_hom_comp φ ψ)
lemma compPresCartesian' {P : fibration B} {u : J ⟶ I }  {v : K ⟶ J} {t : K ⟶ I} {X : P[I]}
   (Y : cartesianLiftOfAlong X u) (Z : cartesianLiftOfAlong Y.Y v) (comm : v ≫ u = t):
   isCartesian (⟨ _ , over_comp comm Y.φ Z.φ ⟩  ) := fun {L} w W ↦ by
    let W' : liftOfAlong X ((w ≫ v) ≫ u) := transportLift (by rw [symm comm , symm (Category.assoc _ _ _)]) W

    obtain ⟨ ψY , hψY ⟩ :=  (Y.2 (w ≫ v) W')
    obtain ⟨ ψZ , hψZ ⟩ := (Z.2 w ⟨ _ , ψY  ⟩ )
    let ψZ : over_hom w W.Y Z.Y := by
      have this : W'.Y = W.Y := by simp
      rw [← this]
      exact ψZ

    use ψZ
    constructor
    have this : W.φ.1 = ψZ.1 ≫ (Z.φ.1 ≫ Y.1.φ.1 )  := calc
      W.φ.1 = W'.φ.1 := rfl
      _     = ψY.1 ≫ Y.φ.1 :=  symm hψY.1
      _     = (ψZ.1 ≫Z.φ.1) ≫ Y.φ.1 := by apply eq_whisker (symm hψZ.1)
      _     = ψZ.1 ≫ (Z.φ.1 ≫ Y.1.φ.1 ) := Category.assoc _ _ _
    rw [this]
    rfl
    intro ψZ' hψZ'
    apply hψZ.2 ψZ'
    -- simp
    let ψY' : over_hom (w ≫ v) W.1 Y.Y := (transLift Z.1 ⟨ _ , ψZ' ⟩ ).φ
    have this : ψY' = ψY := by
      apply hψY.2 ψY' ;
      calc
      ψY'.1 ≫Y.φ.1 = (ψZ'.1 ≫ Z.φ.1 ) ≫ Y.φ.1 := rfl
      _ = ψZ'.1 ≫ (Z.φ.1  ≫ Y.φ.1) := Category.assoc _ _ _
      _ = W'.φ.1  := hψZ'
    have this : ψY'.1 = ψY.1 := congrArg _ this
    rw [← this]
    rfl
    -- apply hψY.2
lemma compPresCartesian {P : fibration B} {u : J ⟶ I }  {v : K ⟶ J} {X : P[I]}
   (Y : cartesianLiftOfAlong X u) (Z : cartesianLiftOfAlong Y.Y v) :
   isCartesian (transLift Y.1 Z.1 ) := compPresCartesian' Y Z rfl



lemma compCartesianMorphisms  {P : fibration B}  {X Y Z : P.1.left} {f : X ⟶ Y} {g : Y ⟶ Z}
  (isCf : isCartesianMorphism P.1 f) (isCg : isCartesianMorphism P.1 g) :
  (isCartesianMorphism P.1 (f ≫ g)) := by
    unfold isCartesianMorphism ;
    let lg : liftOfAlong ⟨ Z , rfl⟩ _ := morphismToLift (P:=P.1.hom) g
    let lf : liftOfAlong ⟨ Y , rfl⟩ _ := morphismToLift (P:=P.1.hom) f
    let path : _ = (P.1.hom.map (f ≫ g))  := by rw [Functor.map_comp]
    let oc : over_hom (P.1.hom.map (f ≫ g)) _ _:= over_comp path lg.φ lf.φ
    have this : morphismToLift  (P:=P.1.hom) (f ≫ g) = ⟨ _ , oc ⟩  := by sorry
    rw [this]
    let goal : isCartesian ⟨ lf.Y , oc⟩  := compPresCartesian' (P:=P) ⟨ _ , isCg⟩ ⟨ _ ,isCf⟩  path
    assumption
