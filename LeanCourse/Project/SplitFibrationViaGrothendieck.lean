import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Grothendieck
-- import Mathlib.CategoryTheory.Bundled
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
--import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration


set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 1500000
set_option quotPrecheck false

universe v₁ u₁ v₂ u₂   --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories
-- notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
variable {B : Cat.{v₁ , v₁}} {I J K : B}
-- def tot' (P : PShCat B) : Type _ := ()
@[simps] def opFunctor : Cat.{v₁,u₁} ⥤ Cat.{v₁,u₁} where
  obj := fun X ↦ Bundled.of (X ᵒᵖ)
  map := fun F ↦ Functor.op F


def tot (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) : Cat.{v₁,v₁} := Bundled.of (CategoryTheory.Grothendieck (P ⋙ opFunctor)) -- , Grothendieck.instCategoryGrothendieck⟩
def totop (P : PShCat.{v₁ , v₁ , v₁ , v₁ }  B) : Cat.{_,_} := Bundled.of ((tot P)ᵒᵖ)
--Bundled.of (tot' P) Grothendieck.instCategoryGrothendieck
-- def coercCat (B : Cat.{v₁ , u₁ }) : Cat.{max v₁ v₂ , max u₁ u₂} := by sorry
-- def coercType (B : Type u₁ ) : Type (max u₁ v₁) := B
variable {B : Cat.{v₁,v₁}}
def Grth' (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) :  totop P ⟶ B := Functor.leftOp (CategoryTheory.Grothendieck.forget (P ⋙ opFunctor))
 -- (coercCat.{_,_,u₁,v₁} B)

def Grth (P : PShCat.{v₁ , v₁ , v₁ , v₁ } B) : Over (B) := Over.mk (Grth' P)

/-
theorem compInFiber' {P : PShCat.{v₁ , v₁ , v₁ , v₁ } B} {X Y Z  : tot P} (f : Z ⟶Y) (g : Y ⟶ X) :
(f ≫g ).fiber = eqToHom ((by sorry) : ((P ⋙ opFunctor).map (f.base ≫g.base)).obj Z.fiber =  ((P ⋙ opFunctor).map g.base).obj (((P ⋙ opFunctor).map f.base).obj Z.fiber))
 ≫  (((P ⋙ opFunctor).map (g.base)).map (f.fiber)) ≫ g.fiber := by apply CategoryTheory.Grothendieck.comp_fiber
  -- (g ≫f).unop.fiber.unop = (g.unop.fiber.unop) ≫ ((P.map (g.unop.base.unop)).map (f.unop.fiber)).unop ≫ eqToHom (by sorry):= by
-/
variable {P : PShCat.{v₁ , v₁ , v₁ , v₁ } B}
notation "fiber" => obj_over (P:=(Grth P).hom)
theorem compInFiber'  {X Y Z  : totop P} (f : Y ⟶Z) (g : X ⟶ Y) :
(f.unop ≫ g.unop ).fiber = eqToHom (by sorry : Opposite.op ((P.map (f.unop.base ≫g.unop.base)).obj Z.unop.fiber.unop) =  Opposite.op ((P.map g.unop.base).obj ((P.map f.unop.base).obj Z.unop.fiber.unop)))
 ≫  (Opposite.op ((P.map (g.unop.base)).map (f.unop.fiber.unop))) ≫ g.unop.fiber := by
  apply CategoryTheory.Grothendieck.comp_fiber
def compInFiberCrypticPath  {X Y Z  : totop P} {f : Y ⟶Z} {g : X ⟶ Y} : ((P.map g.unop.base).obj ((P.map f.unop.base).obj Z.unop.fiber.unop))= ((P.map (f.unop.base ≫g.unop.base)).obj Z.unop.fiber.unop) := by
  erw [Functor.map_comp, Functor.comp_obj]
theorem compInFiber {X Y Z  : totop P} (f : Y ⟶Z) (g : X ⟶ Y) :
(g ≫ f ).unop.fiber.unop = g.unop.fiber.unop
 ≫  (((P.map (g.unop.base)).map (f.unop.fiber.unop))) ≫
  eqToHom (compInFiberCrypticPath) := by
  have this : (g ≫ f ).unop.fiber.unop = (f.unop ≫ g.unop).fiber.unop := by aesop
  rw [this , congrArg (fun x ↦ x.unop) (compInFiber' f g)]
  aesop
def fiberToSection {I : ↑ B} (X : fiber I) :
 P.obj (Opposite.op I) := (P.map (eqToHom (congrArg Opposite.op X.2))).obj  X.1.unop.fiber.unop

def sectionToFiber   {I : ↑ B} (X : P.obj (Opposite.op I)) : fiber I := by
  use ⟨Opposite.op I , Opposite.op X⟩
  rfl
lemma Grthmap {X Y : (Grth P).left} {u' : Y ⟶X} : (Grth P).hom.map u' = u'.unop.base.unop := rfl
lemma extOverHom {J I : B} {u : J ⟶I } {X : fiber I} {Y : fiber J} (ψ' ψ: over_hom u Y X) : ψ'.1.unop.base = ψ.1.unop.base := by
  have t1 := ψ'.2
  have t2 := ψ.2
  let g := eqToHom X.2
  apply Quiver.Hom.unop_inj
  apply ((IsIso.of_iso (eqToIso X.2)).mono_of_iso).right_cancellation


  rw [Grthmap ] at t1
  rw [Grthmap] at t2
  rw [eqToIso.hom ]
  rw [t1,t2]


def cleavage{J I : ↑B}
  (u : J ⟶ I)
  (X : fiber I) : cartesianLiftOfAlong (P:=(Grth P).hom) X u := by
  let Y:= sectionToFiber <| (P.map u.op).obj (fiberToSection X)
/-
  let myφIso : (Y.1).unop.fiber.unop  ≅ (((P ⋙ opFunctor).map
        (eqToHom (_ : Opposite.op (X.1).unop.1.unop = Opposite.op I) ≫
          u.op ≫ eqToHom (_ : Opposite.op J = (Y.1).unop.base))).obj
    (X.1).unop.fiber).unop
    -/
  let myφIso : (((P ⋙ opFunctor).map
        (eqToHom (_ : Opposite.op (X.1).unop.1.unop = Opposite.op I) ≫
          u.op ≫ eqToHom (_ : Opposite.op J = (Y.1).unop.base))).obj
    (X.1).unop.fiber) ≅ (Y.1).unop.fiber
  := by
      apply eqToIso
      aesop
  let myφ : liftOfAlong X u := by
    use Y
    let u' : Y.1 ⟶ X.1 := by
      use eqToHom (congrArg Opposite.op X.2) ≫  u.op ≫  (eqToHom <| symm (congrArg Opposite.op Y.2))
      use myφIso.hom.unop
    use u'
    have this : u'.unop.base = eqToHom (congrArg Opposite.op X.2) ≫  u.op ≫  (eqToHom <| symm (congrArg Opposite.op Y.2)) := rfl
    have this : u'.unop.base.unop =  (eqToHom <| (Y.2)) ≫ u ≫  eqToHom (symm X.2):= by rw [congrArg (fun x ↦ x.unop) this] ; simp ; apply (_ ≫= ·  ); sorry

    rw [Grthmap , this, Category.assoc]
    apply (_ ≫= · )
    rw [Category.assoc]
    rw [eqToHom_trans, eqToHom_refl]
    exact Category.comp_id u
  use myφ
  intro K v L
  obtain ⟨  Z  , ⟨ φ ⟩ , hφ  ⟩  := L
  let P' := P ⋙ opFunctor
  have targetEq : ((P'.map φ.base).obj (X.1).unop.fiber) = (P'.map (v.op ≫ Opposite.op (eqToHom Z.2))).obj (Y.1).unop.fiber := by sorry
  -- obtain ⟨ ⟨K' , Z ⟩ ⟩  := Z.1

  let Λ :  (Z.1).unop.fiber.unop ⟶ ((P'.map φ.base).obj (X.1).unop.fiber).unop := φ.fiber.unop
  let Λ : Z.1 ⟶ Y.1 := ⟨ _ ,  (eqToHom (symm targetEq)) ≫ Opposite.op Λ⟩
  let ψ : over_hom v Z Y := by use Λ ; sorry
  use ψ
  have goal : (ψ.1 ≫ myφ.φ.1).unop= φ  := by simp ; sorry
  have goal : ψ.1 ≫ myφ.φ.1 = ⟨ φ ⟩  := congrArg Opposite.op goal
  constructor
  exact goal
  intro ψ' hψ'
  apply Subtype.ext
  -- have l : myφIso.hom = myφ.φ.1.unop.fiber.unop := rfl
  let thisFunctor : P'.obj (Y.1.unop.base) ⟶ P'.obj (Z.1.unop.base)  :=(P'.map (ψ.1).unop.base)
  let mφ : _ ⟶ Y.1.unop.fiber := myφ.φ.1.unop.fiber
  have g : Epi (thisFunctor.map mφ) := (IsIso.of_iso (thisFunctor.mapIso myφIso)).epi_of_iso
  apply Quiver.Hom.unop_inj
  exact Grothendieck.ext _ _ (extOverHom ψ' ψ) (by
      -- ((IsIso.of_iso myφIso).mono_of_iso).right_cancellation
      apply g.left_cancellation

      --have hψ' : myφ.1.φ.unop.fiber ≫ ψ'
      sorry
      --have goal : thisFunctor.map mφ ≫ ψ.1.unop.fiber = φ.fiber := by sorry

      --rw   [← Category.assoc , hψ' , goal]
      )


def Grothendieck_obj (P : PShCat B) : splitFibration B where
  P:= ⟨Grth P , fun u X ↦ by
    let cl := cleavage u X
    exact ⟨cl.1 , cl.2⟩
    ⟩
  c := ⟨cleavage  ⟩
  isSplit := by sorry


def Grothendieck : PShCat B ⥤ splitFibration B where
  obj := fun P => Grothendieck_obj P
  map := by sorry
  map_comp := by sorry
  map_id := by sorry
def fiberComparisonFunctorObj {P : PShCat B} {I : Bᵒᵖ } (X : P.obj I) : (Grothendieck_obj P) ↓ I.unop :=  ⟨ ⟨ I , Opposite.op X⟩  , rfl⟩
def fiberComparisonFunctor_map_fib {P : PShCat B} {I : Bᵒᵖ }  {X Y : P.obj I} (f : X ⟶ Y) :
  (fiberComparisonFunctorObj X).1.unop.fiber.unop ⟶ (((P ⋙ opFunctor).map (𝟙 I)).obj (fiberComparisonFunctorObj Y).1.unop.fiber).unop := f ≫ eqToHom (by rw [Functor.map_id] ; rfl)
@[simps] def fiberComparisonFunctor (P : PShCat B) (I : Bᵒᵖ ) : P.obj I ⥤ (Grothendieck_obj P) ↓ I.unop where --≌
  obj := fun X ↦ fiberComparisonFunctorObj X
  map := fun f ↦ by exact ⟨ ⟨ 𝟙 I , Opposite.op (fiberComparisonFunctor_map_fib f)⟩  , by aesop ⟩
  map_id := by sorry
  map_comp := by sorry
theorem fiberComparisonIsEquivalence {P : PShCat B} {I : Bᵒᵖ } : IsEquivalence (fiberComparisonFunctor P I) := by sorry

lemma cartMorphsAreIsosOnFiber {P : PShCat B} {X Y : totop P} {f : X ⟶ Y} (isCart : isCartesianMorphism (Grth P) f) : IsIso f.unop.fiber.unop  := by sorry

  /-
   toFun :=
  invFun:= fun X ↦ (P.map (eqToHom (congrArg (fun x ↦ Opposite.op x) X.2))).obj X.1.unop.fiber.unop
  left_inv := by intro X ; simp ; aesop
  right_inv := by
    intro X
    apply Subtype.ext
    simp
    obtain ⟨ I , X⟩ := X.1

    --aesop

    /-
    match _ , X with
      base
      -/
      -- apply Grothendieck.ext
  -/
