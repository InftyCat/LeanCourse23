import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
-- import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.FibrationBicategory
import LeanCourse.Project.CounitOnFibers
import LeanCourse.Project.CartesianFunctors
--import LeanCourse.Project.PreSheavesOfCategories
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

 variable {B : Cat.{v₁ , v₁}} {I : B}
 variable {P : fibration B}
 local notation "E" => E'_obj (P:=P) (I:=I)
 notation u  "°" X => cartesianLiftFromFibration P u X
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
noncomputable def functorOnFibers_map' {X : P [I]} {uv u : ((fundamentalFibration.obj I).1).left.1} (v : uv ⟶ u) :  over_hom v.left ((v.left ≫ u.hom) ° X).Y (u.hom ° X).Y :=
  ((u.hom ° X).2 _ _).choose
noncomputable def compar {uv u : ((fundamentalFibration.obj I).1).left.1}  {X : P [I]} (v : uv ⟶ u) : ((uv.hom) ° X).Y.1 ⟶ ((v.left ≫ u.hom) ° X).Y.1 := eqToHom ((by rw [Over.w v]))
noncomputable def functorOnFibers_map {X : P [I]} {uv u : ((fundamentalFibration.obj I).1).left.1} (v : uv ⟶ u) :  (uv.hom ° X).Y.1 ⟶ (u.hom ° X).Y.1 :=
  compar v ≫ (functorOnFibers_map' v).1
noncomputable def functorOnFibers (X : P [I]) : (fundamentalFibration.obj I).1.left ⥤ P.1.left where
  obj := fun u  ↦ (u.hom ° X).Y.1
  map := functorOnFibers_map
  map_id := by
    intro u ;
    let uX := u.hom ° X
    have th : (functorOnFibers_map' (𝟙 u)).1 ≫ (uX.φ.1)= ((𝟙 _ ≫ u.hom) ° X).φ.1 := (uX.2 (𝟙 _) ((𝟙 _ ≫ u.hom) ° X)).choose_spec.1
    have p : ((𝟙 u.left ≫ u.hom)°X).toliftOfAlong.Y.1 = uX.Y.1 := by rw [Category.id_comp]
    have th' : eqToHom p≫ (uX.φ.1)= ((𝟙 _ ≫ u.hom) ° X).φ.1 := by sorry
    have q : ⟨ eqToHom p , by sorry⟩ = functorOnFibers_map' (𝟙 u)   :=
      (uX.2 (𝟙 _) ((𝟙 _ ≫ u.hom) ° X)).choose_spec.2 ⟨ eqToHom p , by sorry⟩  th'
    trans  eqToHom (by rw [Over.w (𝟙 _)]) ≫ (functorOnFibers_map' (𝟙 u)).1
    · rfl
    · rw [← congrArg (fun x ↦ x.1) q,eqToHom_trans,eqToHom_refl]


  map_comp := fun {uvw} {uv} {u} w v ↦ by sorry

@[simps!] noncomputable def OverMorphOnFibers (X : P [I]) : (fundamentalFibration.obj I).1 ⟶ P.1 := by
  apply Over.homMk
  swap
  exact functorOnFibers X
  apply extFunctor
  swap
  constructor
  · intro Y Z f
    sorry


  · sorry
  sorry

theorem equivOnFibers : IsEquivalence E := by


  have full : Full E := by
    constructor ; swap
    · intro X Y f
      constructor ; swap

      · apply NatTrans.mk ; swap
        · intro u
          let morph : u ⟶ Over.mk (𝟙 _) := Over.homMk u.hom
          let fib := fundamentalFibration.obj I
          have isDisc : isDiscreteOverB fib.1 := domainIsDiscrete I


          have isCart1 : isCartesianMorphism P.1 (X.1.left.map morph):= X.2 morph (automaticallyCart morph)
          have isCart2 : isCartesianMorphism P.1 (Y.1.left.map morph):= Y.2 morph (automaticallyCart morph)
          let X' := E_obj_obj X
          let Y' := E_obj_obj Y
          have p1 : P.1.hom.obj X' = I := (comm X).symm
          have p2 : P.1.hom.obj Y' = I := (comm Y).symm
          -- let f1 := P.1.hom.map (X.1.left.map morph) ≫  eqToHom p1
          -- have t1 : P.1.hom.obj ((X.1).left.obj u) = u.left := sorry
          have t2 : P.1.hom.obj ((Y.1).left.obj u) = u.left := by rw [← comm Y] ; rfl


          have tdiff : P.1.hom.obj ((X.1).left.obj u) = P.1.hom.obj ((Y.1).left.obj u) := by rw [← comm X] ; exact (symm t2)

          have help :eqToHom tdiff ≫ eqToHom t2 ≫ u.hom = (P.1).hom.map ((X.1).left.map morph) ≫ eqToHom (by rw [← comm X] ; rfl) := by
            rw [← Category.assoc] ;
            rw [rwFuncComp X morph ,eqToHom_trans]
            rfl


          let f2 := P.1.hom.map (Y.1.left.map morph) ≫  eqToHom p2
          let lX : cartesianLiftOfAlong (X') (eqToHom tdiff ≫ eqToHom t2  ≫ u.hom) :=  cartesianMorphismToCartLift'' (help) isCart1
          let lY : cartesianLiftOfAlong (Y') (eqToHom t2 ≫ u.hom)  := cartesianMorphismToCartLift'' (by sorry) isCart2


          let myMap : over_hom (eqToHom tdiff) lX.Y lY.Y  := by
          --Unfortunately I cant apply map' from cleavage because X(u) and Y(u) are not in the same fiber
            let myLift : liftOfAlong Y' (eqToHom tdiff ≫ eqToHom t2  ≫ u.hom) :=  ⟨  _ , over_comp (by rw [Category.comp_id]) (coercBack f) lX.φ  ⟩
            exact (lY.2 (eqToHom tdiff) myLift).choose
          exact myMap.1
        · sorry
      · sorry

    · sorry

  have essSurj : EssSurj E := by
    constructor
    intro X
    let F : fundamentalFibration.obj I ⥤c P := ⟨
      OverMorphOnFibers X ,
      by sorry
      ⟩
    use F
    constructor
    rw [E'_obj_obj]
    unfold E_obj_obj
    unfold toFunctorOnFibers
    unfold objMappingBetweenFibers
    simp
    exact (cartesianLiftIsUnique (P:=P.1.hom) (idCartLift) (𝟙 _ ° X)).choose




  have faithful : Faithful E := by sorry
  apply Equivalence.ofFullyFaithfullyEssSurj
-- theorem
