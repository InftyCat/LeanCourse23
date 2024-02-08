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

noncomputable def fufi {X : P [I]} {uv u : ((fundamentalFibration.obj I).1).left.1} (v : uv ⟶ u) :
  ∃! φ : over_hom v.left (uv.hom ° X).Y (u.hom ° X).Y , φ.1 ≫ (u.hom ° X).φ.1 = ((uv.hom) ° X).1 :=
   ((u.hom ° X).2 v.left (transportLift (by aesop) ((uv.hom) ° X).1))

noncomputable def functorOnFibers (X : P [I]) : (fundamentalFibration.obj I).1.left ⥤ P.1.left where
  obj := fun u  ↦ (u.hom ° X).Y.1
  map := fun v ↦ (fufi v).choose.1
  map_id := by
    intro u ;
    symm
    have : ⟨ 𝟙 (u.hom ° X).Y.1 , _⟩ = (fufi (𝟙 u)).choose  := (fufi (𝟙 u)).choose_spec.2 ⟨ 𝟙 _ , by simp ; rw [Over.id_left,Category.comp_id] ⟩ (by simp)
    exact congrArg (fun x ↦ x.1) this

  map_comp := fun {uvw} {uv} {u} w v ↦ by

    let owc : over_hom (w ≫ v).left (uvw.hom ° X).Y (u.hom ° X).Y  := over_comp (P:=P.1)  (by aesop) (fufi v).choose (fufi w).choose --

    have : owc = (fufi (w ≫ v)).choose := by
      apply (fufi (w ≫ v)).choose_spec.2
      rw [over_comp_coe,Category.assoc,(fufi v).choose_spec.1,(fufi w).choose_spec.1]
    symm
    exact congrArg (fun x ↦ x.1) this

notation "f >[ comm ]> g" => over_comp comp f g
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
noncomputable def equivOnFibersFull {X Y : fundamentalFibration.obj I ⟶ P}  (f: E'_obj.obj X ⟶ E'_obj.obj Y) (u: ((fundamentalFibration.obj I).1).left.1)
  : X.1.left.obj u ⟶ Y.1.left.obj u := by -- ∃! α : over_hom (by sorry) (X / u.1.left)Y.1.left.obj u := by
          let morph : u ⟶ Over.mk (𝟙 _) := Over.homMk u.hom
          have t2 : P.1.hom.obj ((Y.1).left.obj u) = u.left := by rw [← comm Y] ; rfl
          let u' := eqToHom t2  ≫ u.hom
          have tdiff : P.1.hom.obj ((X.1).left.obj u) = P.1.hom.obj ((Y.1).left.obj u) := by rw [← comm X] ; exact (symm t2)
          have help :eqToHom tdiff ≫ u' = (P.1).hom.map ((X.1).left.map morph) ≫ eqToHom (by rw [← comm X] ; rfl) := by
            rw [← Category.assoc] ;
            rw [rwFuncComp X morph ,eqToHom_trans]
            rfl
          let lX : cartesianLiftOfAlong (E_obj_obj X) (eqToHom tdiff ≫ u') :=  cartesianMorphismToCartLift'' (help) (X.2 morph (automaticallyCart morph))
          let lY : cartesianLiftOfAlong (E_obj_obj Y) u'  := cartesianMorphismToCartLift'' (by rw [rwFuncComp Y] ; rfl) (Y.2 morph (automaticallyCart morph))

          exact (lY.2 (eqToHom tdiff) ⟨  _ , over_comp (by rw [Category.comp_id]) (coercBack f) lX.φ  ⟩).choose.1


/-

theorem equivOnFibers : IsEquivalence E := by


  have full : Full E := by
    constructor ; swap
    · intro X Y f
      constructor ; swap

      · apply NatTrans.mk ; swap
        · intro u
          apply equivOnFibersFull f u
        · intro uv u v ;
          sorry
          --apply Subtype.ext

      · intro A T
        sorry

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
