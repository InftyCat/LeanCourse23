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
def compPath {X Y : fundamentalFibration.obj I ⟶ P} {u: ((fundamentalFibration.obj I).1).left.1}:
  P.1.hom.obj ((X.1).left.obj u) ⟶ P.1.hom.obj ((Y.1).left.obj u) := eqToHom (by  rw [← comm X, comm Y]  )
noncomputable def equivOnFibersFullCartSrc {X Y : fundamentalFibration.obj I ⟶ P}
  (f: E'_obj.obj X ⟶ E'_obj.obj Y)
  (u: ((fundamentalFibration.obj I).1).left.1)
  :  cartesianLiftOfAlong (E_obj_obj X)
    (compPath ≫
    (eqToHom ((by rw [← comm Y] ; rfl) ) ≫

    u.hom) : P.1.hom.obj ((X.1).left.obj u) ⟶ I) := by
      let morph : u ⟶ Over.mk (𝟙 _) := Over.homMk u.hom
      exact cartesianMorphismToCartLift'' (by rw [← Category.assoc , rwFuncComp X morph ] ; unfold compPath ; rw [eqToHom_trans] ; rfl) (X.2 morph (automaticallyCart morph))
noncomputable def equivOnFibersFullCartTrg {X Y : fundamentalFibration.obj I ⟶ P}
  (f: E'_obj.obj X ⟶ E'_obj.obj Y)
  (u: ((fundamentalFibration.obj I).1).left.1)
  :  cartesianLiftOfAlong (E_obj_obj Y)
    ((eqToHom ((by rw [← comm Y] ; rfl) ) ≫ u.hom) : P.1.hom.obj ((Y.1).left.obj u) ⟶ I) := by
      let morph : u ⟶ Over.mk (𝟙 _) := Over.homMk u.hom
      exact cartesianMorphismToCartLift'' (by rw [rwFuncComp Y] ; rfl) (Y.2 morph (automaticallyCart morph))
noncomputable def equivOnFibersFull {X Y : fundamentalFibration.obj I ⟶ P}  (f: E'_obj.obj X ⟶ E'_obj.obj Y) (u: ((fundamentalFibration.obj I).1).left.1)
  : ∃! ψ : over_hom (P:=P.1.hom) compPath (equivOnFibersFullCartSrc f u).Y (equivOnFibersFullCartTrg f u).Y,
    ψ.1 ≫ (equivOnFibersFullCartTrg f u).φ.1 = (over_comp (by rw [Category.comp_id]) (coercBack f) (equivOnFibersFullCartSrc f u).φ ).1 :=  -- X.1.left.obj u ⟶ Y.1.left.obj u := by ----
          (equivOnFibersFullCartTrg f u).2 compPath ⟨  _ , over_comp (by rw [Category.comp_id]) (coercBack f) (equivOnFibersFullCartSrc f u).φ⟩



notation "⟪ " v "  ⟫" => (morphismToLift (P:=(fundamentalFibration.obj I).1.hom) v).φ
notation f ">[" comm "]>" g => over_comp comm g f
notation f ">>" g => over_hom_comp g f
theorem equivOnFibers : IsEquivalence E := by


  have full : Full E := by
    constructor ; swap
    · intro X Y f
      constructor ; swap

      · apply NatTrans.mk ; swap
        · intro u
          exact (equivOnFibersFull f u).choose.1
        · intro uv u v ;
          /-
          lemma liftFromCartesiannessIsUnique  {P : fibration B} {J I : B} {X  : P[I]} {Y : P [J]} {u : J ⟶ I}
  {C : liftOfAlong X u} (isw : isWeakCartesian C) {f f' : Y ⟶ C.Y} (p : f.1 ≫ C.φ.1 = f'.1 ≫ C.φ.1) : f = f' := by

          -/
          let Yv : over_hom v.left ⟨ Y.1.left.obj uv , rfl⟩ ⟨ Y.1.left.obj u , rfl⟩ := ⟨ Y.1.left.map v , by sorry ⟩
          --have p : v.left ≫ compPath = compPath ≫ v.left := by sorry
          let mor1 := ((equivOnFibersFull f uv).choose >> mappingOverHom Y ⟪ v ⟫)
          have : (mappingOverHom X ⟪ v ⟫  >[ by sorry]> (equivOnFibersFull f u).choose)
            = mor1 := by
            apply liftFromCartesiannessIsUnique (weakCartifCartesian (equivOnFibersFullCartTrg f u)) sorry

          --apply Subtype.ext

      · intro A T
        sorry

    · sorry
  sorry
/-
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
