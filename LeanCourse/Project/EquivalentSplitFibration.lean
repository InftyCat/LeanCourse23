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
import LeanCourse.Project.Split
import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration
import LeanCourse.Project.SplitFibrationViaGrothendieck
import LeanCourse.Project.FibrationBicategory
import LeanCourse.Project.CounitOnFibers
import LeanCourse.Project.EquivalenceOfFibrations
import LeanCourse.Project.EquivalenceOnFibers

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
variable {P : fibration B}

/-
lemma SpP {I : B} : (Sp.obj P) ↓ I ≅ Bundled.of (fundamentalFibration.obj I ⟶ P) := by sorry
-/
open Over
lemma weird {I J : Bᵒᵖ} {u : I ⟶ J} : (Over.map u.unop).obj (Over.mk (𝟙 J.unop)) = Over.mk u.unop := by
  trans Over.mk (𝟙 J.unop ≫ u.unop)
  · rfl
  · apply congrArg _ ; apply Category.id_comp
lemma replaceTargetOfFiberMap {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) :
  ((((yoObj P).map (fundamentalFibration.map (f.unop.1.unop)).op).obj X.unop.fiber.unop).1).left.obj (Over.mk (𝟙 Y.unop.1.unop)) =
      X.unop.2.unop.1.left.obj (Over.mk f.unop.1.unop) := by
      obtain ⟨⟨ I⟩  , ⟨ X ⟩ ⟩:= X
      obtain ⟨⟨ J ⟩  , ⟨ Y ⟩ ⟩ := Y
      obtain ⟨⟨ u ⟩  , ⟨ α ⟩  ⟩ :=f
      simp ; apply congrArg (X.1.left.obj) ; exact weird
def fiberMap {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) :
  Y.unop.2.unop.1.left.obj (Over.mk (𝟙 _)) ⟶ X.unop.2.unop.1.left.obj (Over.mk f.unop.1.unop)
  := by
    obtain ⟨⟨ I⟩  , ⟨ X ⟩ ⟩:= X
    obtain ⟨⟨ J ⟩  , ⟨ Y ⟩ ⟩ := Y
    have this := replaceTargetOfFiberMap f
    obtain ⟨⟨ u ⟩  , ⟨ α ⟩  ⟩ :=f
    let fst : Y.1.left.obj (Over.mk (𝟙 J ) ) ⟶ _  :=
      (α.1.app (Over.mk (𝟙 J)))

    let fst := fst ≫ eqToHom (this)
    exact fst

@[simp] def E_functor_map {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) : ((E'_obj).obj Y.unop.fiber.unop).1 ⟶((E'_obj).obj X.unop.fiber.unop).1  :=
  fiberMap f ≫ X.unop.2.unop.1.left.map (Over.homMk f.unop.1.unop)
  /-
  by
    obtain ⟨⟨ I⟩  , ⟨ X ⟩ ⟩:= X
    obtain ⟨⟨ J ⟩  , ⟨ Y ⟩ ⟩ := Y

    obtain ⟨⟨ u ⟩  , ⟨ α ⟩  ⟩ :=f

    simp
    let fst := fiberMap f
    %let snd : X.1.left.obj (Over.mk u) ⟶ X.1.left.obj (Over.mk (𝟙 I)):= X.1.left.map (Over.homMk u)
    exact (fst ≫ snd)
    -- (↑((((PSh_rest fundamentalFibration).obj (yo.obj P)).map u).obj X)).left.obj (Over.mk (𝟙 J.unop ))
    -- apply (· ≫ fst )
    -/

lemma exchangeLaw {C : Cat} {X Y Z W  V : C} {f : X ⟶ Y} {g : Y ⟶Z } {h : Z ⟶ V} {i : V ⟶ W} :
  f ≫ (g ≫ h) ≫ i = (f ≫ g)  ≫ (h ≫ i) := by
  rw [Category.assoc , Category.assoc]

lemma compCartTransExt {P Q : fibration B} {F G H:  P ⟶ Q} (η: F ⟶ G) (ε : G ⟶ H) : (η ≫ ε).1 = η.1 ≫ ε.1 := rfl
def forgetFibration {P Q : fibration B} : (⟨ P ⟶ Q , instCategoryHomFibrationToQuiverToCategoryStructInstCategoryFibration ⟩ : Cat)  ⥤ (P.1.left ⥤ Q.1.left)  where
  obj := fun F ↦ F.1.left
  map := fun f ↦ f.1
lemma E_functor_map_comp  {X' Y' Z' : (Sp.obj P).1.1.left} (g : Z' ⟶Y') (f : Y' ⟶ X') : E_functor_map (g ≫ f) = E_functor_map g ≫ E_functor_map f := by sorry
/-
    let X:= X'.unop.2.unop
    let Y:= Y'.unop.2.unop
    let Z := Z'.unop.2.unop

    let β:= fiberMap g

    let α := fiberMap f
    rw [E_functor_map ]
    let v := g.unop.1.unop
    let u := f.unop.1.unop
    let v' : mk (v ≫ u) ⟶ mk u := homMk v
    let v'' :  mk v ⟶ mk (𝟙 _ ) := homMk v
    have hv' : v' = (Over.map u).map v'' ≫ eqToHom (weird) := by
      apply OverMorphism.ext
      simp
      let m := g.unop.base.unop
      symm
      calc
        m ≫ (eqToHom weird).left
          = m ≫ (Over.forget _).map (eqToHom weird) := rfl
        _ = m ≫ eqToHom rfl := by rw [eqToHom_map] ;
        _ = m  ≫ 𝟙 _ := by rw [eqToHom_refl]
        _ = m := by apply Category.comp_id


    let u' : mk u ⟶ mk (𝟙 _ ) := homMk u
    let vu : mk (v ≫ u) ⟶mk (𝟙 _ ) := homMk (v ≫ u)
    let restFunctor := (((PSh_rest fundamentalFibration).obj (yo.obj P)))
    let a' := f.unop.2.unop
    let b' := g.unop.2.unop



    let a : Y.1.left ⟶ ((restFunctor.map ⟨ u ⟩ ).obj X).1.left := a'.1
    let α2 : Y.1.left.obj (mk v) ⟶X.1.left.obj (mk (v ≫  u))  := a.app (mk v)



    let h := g ≫ f
    let b : Z.1.left ⟶ ((restFunctor.map ⟨ v ⟩ ).obj Y).1.left := g.unop.2.unop.1
    let ab : Z.1.left ⟶ ((restFunctor.map ⟨ v ≫ u ⟩ ).obj X).1.left := h.unop.2.unop.1

    let compPath := congrArg (fun F ↦ (F.obj X).1.left ) (symm ( restFunctor.map_comp ⟨u⟩ ⟨v⟩))
    -- have test : congrArg (fun x ↦ x.1) compInFiberCrypticPath = compPath := rfl

    let vf : ((restFunctor.map ⟨ v ⟩ ).obj Y).1.left ⟶
      (((restFunctor.map ⟨ v ≫ u ⟩ ).obj X)).1.left :=
      ((restFunctor.map ⟨ v ⟩ ).map a').1 ≫ eqToHom compPath

    have complicated : ((restFunctor.map ⟨ v ⟩ ).map a').1.app (mk (𝟙 _)) ≫ eqToHom ((Functor.congr_obj compPath (mk (𝟙 _))).trans (replaceTargetOfFiberMap h)) = eqToHom (replaceTargetOfFiberMap g) ≫ α2 := by sorry



    have wow : ab = b ≫vf := by calc
      ab = (g ≫f).unop.fiber.unop.1 := rfl
      _ = (b' ≫  ((restFunctor.map ⟨ v ⟩ ).map a') ≫ eqToHom compInFiberCrypticPath ).1 := congrArg (fun x ↦ x.1) (compInFiber f g)
      _ = b'.1 ≫ ((restFunctor.map ⟨ v ⟩ ).map a').1 ≫ eqToHom compPath := by
        rw [compCartTransExt , compCartTransExt]
        apply (whisker_eq _)
        apply (whisker_eq _)


        calc (eqToHom (compInFiberCrypticPath (P:=restFunctor))).1 = forgetFibration.map (eqToHom (compInFiberCrypticPath (P:=restFunctor))) := rfl
        _ = eqToHom compPath := by rw [eqToHom_map]

    have fiberMapComp : fiberMap (g ≫f )  =  β≫ α2 := by
      calc
         fiberMap h = ab.app (mk (𝟙 _)) ≫ eqToHom (replaceTargetOfFiberMap h) := rfl
         _ = ((b.app (mk (𝟙 _))) ≫ vf.app (mk (𝟙 _))) ≫ eqToHom (replaceTargetOfFiberMap h) := by apply eq_whisker _ ; rw [wow] ; rfl
         _ = b.app (mk (𝟙 _)) ≫ vf.app (mk (𝟙 _)) ≫ eqToHom (replaceTargetOfFiberMap h) := Category.assoc _ _ _
         _ = b.app (mk (𝟙 _)) ≫ (((restFunctor.map ⟨ v ⟩ ).map a').1.app (mk (𝟙 _)) ≫ (eqToHom compPath).app (mk (𝟙 _) )) ≫ eqToHom (replaceTargetOfFiberMap h) := by rfl
         _ = b.app (mk (𝟙 _)) ≫ ((restFunctor.map ⟨ v ⟩ ).map a').1.app (mk (𝟙 _)) ≫ eqToHom (Functor.congr_obj compPath (mk (𝟙 _))) ≫ eqToHom (replaceTargetOfFiberMap h) := (whisker_eq _ (by rw [eqToHom_app, Category.assoc]))
         _ = b.app (mk (𝟙 _)) ≫ eqToHom (replaceTargetOfFiberMap g) ≫ α2 := by
                                          apply ((b.app (mk (𝟙 _))) ≫= ·);
                                          --rw [← Category.assoc] ;
                                          rw [eqToHom_trans]
                                          exact complicated
         _ = β ≫ α2 :=  by rw [←Category.assoc ] ; apply eq_whisker _ ; rfl



    have myNat : Y.1.left.map v''  ≫ α = α2  ≫ X.1.left.map v'
      := by


        have goal : Y.1.left.map v'' ≫ a.app (mk (𝟙 _)) = α2 ≫ ((restFunctor.map ⟨ u ⟩ ).obj _).1.left.map v''  := a.naturality v''
        have this : α = a.app (mk (𝟙 _ )) ≫ eqToHom (replaceTargetOfFiberMap f) := rfl
        rw [this , ← Category.assoc , goal, Category.assoc]
        apply whisker_eq α2
        have goal : ((restFunctor.map ⟨ u ⟩ ).obj _).1.left.map v'' ≫ eqToHom (replaceTargetOfFiberMap f) = X.1.left.map v' := by
          rw [hv', Functor.map_comp]
          apply whisker_eq (((restFunctor.map ⟨ u ⟩ ).obj _).1.left.map v'')
          symm
          apply eqToHom_map


        exact goal
    have helper : vu = v'  ≫ u'  := rfl


    have xhelper : X.1.left.map vu = X.1.left.map v' ≫ X.1.left.map u' := by rw [← Functor.map_comp , congrArg X.1.left.map helper]
    have t : (homMk ((g ≫ f).unop.base.unop) : mk (v ≫ u) ⟶mk (𝟙 _ ))  = vu := rfl
    rw [fiberMapComp , t,  xhelper , ← exchangeLaw, ← myNat , exchangeLaw]
    simp



-/


def E_functor : (Sp.obj P).1.1.left ⥤ P.1.left where
  obj := fun X ↦ ((E'_obj).obj X.unop.fiber.unop).1
  map :=  E_functor_map

  map_comp := E_functor_map_comp
  map_id := by sorry
lemma E_functor_IsOverB :  E_functor ⋙ P.1.hom = (Sp.obj P).1.1.hom  := by sorry


def E (P : fibration B) : Sp.obj P ⥤c P := ⟨
  Over.homMk E_functor E_functor_IsOverB , by sorry ⟩
theorem TriangleOnFibersCommutes {P : fibration  B} {I : B} :
  fiberComparisonFunctor (psh.obj P) (Opposite.op I) ⋙
  (toFunctorOnFibers (E P) I) =
  E'_obj (P:=P) (I:=I) := by
    apply Functor.ext ; swap ; intro X; simp ; apply Subtype.ext ; aesop ;
    sorry
theorem EisEquiv {P : fibration B} : IsEquivalence (E P).1.left := by
  apply equivalenceOfFibrationsCheckOnFibers ;
  intro I ;
  let X :=  psh.obj P
  apply IsEquivalence.cancelCompLeft (fiberComparisonFunctor X (Opposite.op I)) _
  · exact fiberComparisonIsEquivalence
  · rw [TriangleOnFibersCommutes] ; exact equivOnFibers

/-
def pseudoNatural {Q : PShCat B} :=
  { η : {I : B} → Q.obj (Opposite.op I) ⥤ P[I]  //
  ∀ {J I} (u : J ⟶ I) , η ⋙ reindexing u = Q.map u.op ⋙ η  }
variable {P : fibration B} {Q : PShCat B}
def GrothendieckIntroRule_map {Q : PShCat B} (η : {I : B} → Q.obj (Opposite.op I) ⥤ P[I] )
  {I J : B} {X : Q.obj (Opposite.op I)} {Y : Q.obj (Opposite.op J)}
  (u : J ⟶ I) {α : Y ⟶ (Q.map u.op).obj X} :  (η.obj Y).1 ⟶  (η.obj X).1 := by
    apply ((η.map α).1 ≫ · )
-/
  /-
def GrothendieckIntroRule {Q : PShCat B} (η : {I : B} → Q.obj (Opposite.op I) ⥤ P[I] ) : (Grth Q).left ⥤ P.1.left where
  obj := fun X ↦ (η.obj X.unop.fiber).1
  map := fun {X} {Y} f ↦ by
    obtain ⟨I , X⟩:= X
    obtain ⟨J , Y⟩ := Y
    obtain ⟨u , α ⟩ :=f

    exact ((η.map α).1 ≫ sorry)
    -- apply (η.map α ≫ · )


  -/
