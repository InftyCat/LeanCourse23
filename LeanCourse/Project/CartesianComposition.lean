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

variable {B : Cat.{v₁ , u₁}} {I J K : B}  {P : Over B}
local notation (priority := high) P "[" A "]" => obj_over (P:=P.hom) A
@[simps] def  transport {A A' : B} {u u' : A ⟶ A'} {X : P[A]} {X' : P[A']}
  (p : u = u') (f : over_hom u X X') : over_hom u' X X' := by
  use f.1
  rw [← whisker_eq (CategoryTheory.eqToHom X.2) p]
  exact f.2

@[simp] def transportLift {J I : B} {X : P[I]} {u u' : J ⟶ I}(p : u = u')
  (L : liftOfAlong X u) : liftOfAlong (P:=P.hom) X u' := by
  obtain ⟨  Y , φ ⟩ := L
  exact ⟨ Y , transport p φ⟩

@[simps!] def over_hom_comp {K J I : B} {u : J ⟶I } {v : K ⟶J } {X : P[I]} {Y:P[J]}{Z:P[K]}
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom (v ≫ u) Z X := (transLift ⟨ _ , φ ⟩ ⟨_ , ψ⟩ ).φ
@[simps!] def over_comp    {K J I : B} {u : J ⟶I } {v : K ⟶J } {w : K ⟶ I} {X : P[I]} {Y:P[J]}{Z:P[K]}
  (comm : v ≫ u = w)
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom w Z X
  := transport comm (over_hom_comp φ ψ)

notation f ">[" comm "]>" g => over_comp comm g f
notation f ">>" g => over_hom_comp g f
lemma liftOfAlong_ext  {I : B} {X : obj_over (P:=P.hom) I} {u : J ⟶ I} {L L' : liftOfAlong X u}
  (p : L.Y.1 = L'.Y.1) (hφ : L.φ.1 = (eqToHom p) ≫ L'.φ.1  ) : L = L' := by
    obtain ⟨ Y , φ ⟩ := L
    obtain ⟨ Y' , φ'⟩ := L'
    cases Y
    --cases Y'
    dsimp at p
    subst p
    --cases Y'
    cases φ
    dsimp at hφ
    rw [Category.id_comp] at hφ
    subst hφ
    rfl
lemma extInv {B : Cat} {P : Over B} {J I : B} {u : J ⟶ I} {X : obj_over (P:=P.hom) I} (l1 l2 : liftOfAlong X u) (myident : l1 = l2) :
  ∃ p : l1.Y.1 = l2.Y.1 , eqToHom p ≫ l2.φ.1 = l1.φ.1 := by
    subst myident
    use rfl
    rw [eqToHom_refl,Category.id_comp]



lemma compPresCartesian'  {u : J ⟶ I }  {v : K ⟶ J} {t : K ⟶ I} {X : P[I]}
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
lemma compPresCartesian{u : J ⟶ I }  {v : K ⟶ J} {X : P[I]}
   (Y : cartesianLiftOfAlong X u) (Z : cartesianLiftOfAlong Y.Y v) :
   isCartesian (transLift Y.1 Z.1 ) := compPresCartesian' Y Z rfl



lemma compCartesianMorphisms  {X Y Z : P.left} {f : X ⟶ Y} {g : Y ⟶ Z}
  (isCf : isCartesianMorphism P f) (isCg : isCartesianMorphism P g) :
  (isCartesianMorphism P (f ≫ g)) := by
    unfold isCartesianMorphism ;
    let lg : liftOfAlong ⟨ Z , rfl⟩ _ := morphismToLift (P:=P.hom) g
    let lf : liftOfAlong ⟨ Y , rfl⟩ _ := morphismToLift (P:=P.hom) f
    let path : _ = (P.hom.map (f ≫ g))  := by rw [Functor.map_comp]
    let oc : over_hom (P.hom.map (f ≫ g)) _ _:= over_comp path lg.φ lf.φ
    have this : morphismToLift  (P:=P.hom) (f ≫ g) = ⟨ _ , oc ⟩  := by
      apply liftOfAlong_ext ; swap
      · rfl
      · rw [over_comp_coe,morphismToLift_coe,morphismToLift_coe,morphismToLift_coe] ;
        simp


    rw [this]
    let goal : isCartesian ⟨ lf.Y , oc⟩  := compPresCartesian' (P:=P) ⟨ _ , isCg⟩ ⟨ _ ,isCf⟩  path
    assumption
lemma swapPaths {C : Cat} {X X' Y Y' : C} {s : X = X'} {t : Y = Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'} (this : f ≫ eqToHom t = eqToHom s ≫ f') :
  eqToHom (s.symm) ≫ f = f' ≫ eqToHom (t.symm) := by calc
    eqToHom s.symm ≫ f =
    eqToHom (s.symm) ≫ (f ≫  eqToHom (t)) ≫ eqToHom (symm t) := by symm ; rw [Category.assoc] ; apply (_≫=· ) ; rw [eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = eqToHom (s.symm) ≫ (eqToHom (s) ≫ f') ≫ eqToHom (symm t)  := by rw [this]
    _ = (eqToHom (s.symm) ≫ eqToHom (s) ≫ f') ≫ eqToHom (symm t)  := by rw [← Category.assoc]
     _ = ((eqToHom (s.symm) ≫ eqToHom (s)) ≫ f') ≫ eqToHom (symm t)  := by apply (· =≫_ ) ; rw [← Category.assoc]
    _ = _ := by rw [eqToHom_trans , eqToHom_refl , Category.id_comp]
lemma VerticalAsPath {P : fibration B} {I} {X Y : obj_over (P:=P.1.hom) I} {f : X.1 ⟶ Y.1} (isV : isVertical f) : P.1.hom.map f = eqToHom (X.2.trans Y.2.symm) := by
  calc
  P.1.hom.map f = (P.1.hom.map f ≫ eqToHom (Y.2)) ≫ eqToHom Y.2.symm := by symm ; rw [Category.assoc, eqToHom_trans,eqToHom_refl,Category.comp_id]
  _ = eqToHom X.2 ≫ eqToHom Y.2.symm := by apply (· =≫_) ; exact isV
  _ = _ := by rw [eqToHom_trans]
def idCartLift {X : P [I]} : cartesianLiftOfAlong X (𝟙 _) := by
      use ⟨ X , ⟨ 𝟙 _ , by aesop ⟩ ⟩
      intro J v L
      let L' := transportLift (Category.comp_id _) L
      use L'.φ
      constructor
      aesop
      intro φ hφ
      apply Subtype.ext
      rw [← Category.comp_id φ.1]
      rw [hφ]
      rfl
