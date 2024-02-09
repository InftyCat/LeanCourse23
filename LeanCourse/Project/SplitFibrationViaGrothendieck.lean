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
import LeanCourse.Project.CartesianFunctors


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
-- lemma eqToHom

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
(f.unop ≫ g.unop ).fiber = eqToHom (by
  apply congrArg Opposite.op ; rw [← Functor.comp_obj ] ; aesop_cat : Opposite.op ((P.map (f.unop.base ≫g.unop.base)).obj Z.unop.fiber.unop) =  Opposite.op ((P.map g.unop.base).obj ((P.map f.unop.base).obj Z.unop.fiber.unop)))
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

def cleavageY {J I : ↑B}
  (u : J ⟶ I)
  (X : fiber I) : fiber J :=  sectionToFiber <| (P.map u.op).obj (fiberToSection X)
@[simps] def cleavageφ  {J I : ↑B}
  (u : J ⟶ I)
  (X : fiber I) : (cleavageY u X).1 ⟶ X.1 :=  by
      use eqToHom (congrArg Opposite.op X.2) ≫  u.op ≫  (eqToHom <| symm (congrArg Opposite.op (cleavageY u X).2))
      apply eqToHom
      aesop
/-
Remark :
The following seems obvious but my approach with the double unop using the mathlib turns out to be not practical.
-/
@[simps] def cleavage{J I : ↑B}
  (u : J ⟶ I)
  (X : fiber I) : cartesianLiftOfAlong (P:=(Grth P).hom) X u := by
  let Y:=cleavageY u X
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
    let u' : Y.1 ⟶ X.1 := cleavageφ u X
    use u'
    have this : u'.unop.base = eqToHom (congrArg Opposite.op X.2) ≫  u.op ≫  (eqToHom <| symm (congrArg Opposite.op Y.2)) := rfl
    have this : u'.unop.base.unop =  (eqToHom <| (Y.2)) ≫ u ≫  eqToHom (symm X.2):= by
      rw [congrArg (fun x ↦ x.unop) this] ; simp ; apply (_ ≫= ·  );
      rw [eqToHom_unop]

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
  let ψ : over_hom v Z Y := by use Λ ; simp ; aesop
  use ψ
  let ψmyφ : over_hom (v ≫ u) Z X := ψ >> myφ.φ
  have goal : (ψ.1 ≫ myφ.φ.1).unop= φ  := by

    · apply Grothendieck.ext ; swap

      · rw [Grthmap] at hφ
        trans ψmyφ.1.unop.base
        · rw [over_hom_comp_coe]
        · refine ((Opposite.unop_inj_iff _ _ ).1 ?_)

          refine ((IsIso.of_iso (eqToIso (X.2))).mono_of_iso).right_cancellation _ _ ?_
          rw [eqToIso.hom]
          calc
          _ = eqToHom (_ : (Grth P).hom.obj Z.1 = K) ≫ v ≫ u := ψmyφ.2
          _ = _ :=hφ.symm


      · have rem : (ψ.1 ≫ myφ.φ.1).unop.fiber = eqToHom (by sorry) ≫ φ.fiber := by
          trans  (myφ.φ.1.unop ≫ ψ.1.unop).fiber
          · rfl
          · rw [compInFiber'] ; sorry
        rw [rem, ← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
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
  apply Grothendieck.ext ; swap
  · exact (extOverHom ψ' ψ)
      -- ((IsIso.of_iso myφIso).mono_of_iso).right_cancellation
  · apply g.left_cancellation
    sorry

      --have hψ' : myφ.1.φ.unop.fiber ≫ ψ'

      --have goal : thisFunctor.map mφ ≫ ψ.1.unop.fiber = φ.fiber := by sorry

      --rw   [← Category.assoc , hψ' , goal]


lemma cancel {I : ↑ B} (X : P.obj (Opposite.op I)): fiberToSection (sectionToFiber X) = X := by unfold fiberToSection ; rw [eqToHom_refl,Functor.map_id] ; rfl
def Grothendieck_obj (P : PShCat B) : splitFibration B where
  P:= ⟨Grth P , fun u X ↦ by
    let cl := cleavage u X
    exact ⟨cl.1 , cl.2⟩
    ⟩
  c := ⟨ cleavage ⟩
  isSplit := by

    intro I X
    constructor
    · simp ;
      have : cleavageY (𝟙 _) X = X := by symm ; unfold cleavageY ; rw [((_) : (𝟙 I).op = 𝟙 _ ) , Functor.map_id] ; swap ; rfl ; sorry
      use (congrArg (fun x ↦ x.1) this)
      apply Quiver.Hom.unop_inj
      apply Grothendieck.ext ; swap
      · rw [eqToHom_unop]
        let Y := cleavageY (𝟙 _) X

        trans eqToHom (by sorry)
        · sorry
        · symm ; apply eqToHom_map (Grothendieck.forget (P ⋙ opFunctor))
      · sorry


    · intro J K u v ;
      have p : (P.map v.op).obj ((P.map u.op).obj (fiberToSection X)) = (P.map (u.op ≫ v.op)).obj (fiberToSection X) := by rw [← Functor.comp_obj,Functor.map_comp] ; rfl
      have p :  cleavageY v (cleavageY u X) = cleavageY (v ≫ u) X  := by
      --have p :  (v * (u * X)) = (v ≫ u) * X  := by
        unfold cleavageY ;
        rw [cancel , congrArg (sectionToFiber) p, ((_) : u.op ≫ v.op = (v ≫ u).op)] ; sorry
      have p := (congrArg (fun x ↦ x.1) p)
      use p
      apply Quiver.Hom.unop_inj
      apply Grothendieck.ext ; swap
      · exact (by sorry)
      · exact (by sorry)









def Grothendieck : PShCat B ⥤ splitFibration B where
  obj := fun P => Grothendieck_obj P
  map := by sorry
  map_comp := by sorry
  map_id := by sorry
def fiberComparisonFunctorObj {P : PShCat B} {I : Bᵒᵖ } (X : P.obj I) : (Grothendieck_obj P) ↓ I.unop :=  ⟨ ⟨ I , Opposite.op X⟩  , rfl⟩
def fiberComparisonFunctor_map_fib {P : PShCat B} {I : Bᵒᵖ }  {X Y : P.obj I} (f : X ⟶ Y) :
  (fiberComparisonFunctorObj X).1.unop.fiber.unop ⟶ (((P ⋙ opFunctor).map (𝟙 I)).obj (fiberComparisonFunctorObj Y).1.unop.fiber).unop := f ≫ eqToHom (by rw [Functor.map_id] ;rfl)
@[simps] def fiberComparisonFunctor (P : PShCat B) (I : Bᵒᵖ ) : P.obj I ⥤ (Grothendieck_obj P) ↓ I.unop where --≌
  obj := fun X ↦ fiberComparisonFunctorObj X
  map := fun f ↦ ⟨ ⟨ 𝟙 I , Opposite.op (fiberComparisonFunctor_map_fib f)⟩  , by aesop ⟩
  map_id := by sorry
  map_comp := by sorry
@[simp] def fiberComparisonFunctorInv_obj   {P : PShCat B} {I : Bᵒᵖ } (X :  (Grothendieck_obj P) ↓ I.unop) : P.obj I := (P.map ⟨  eqToHom X.2.symm⟩ ).obj X.1.unop.fiber.unop

def fiberComparisonFunctorInv_map   {P : PShCat B} {I : Bᵒᵖ } {X Y :  (Grothendieck_obj P) ↓ I.unop} (f : Y ⟶ X) : fiberComparisonFunctorInv_obj Y ⟶ fiberComparisonFunctorInv_obj X := by

    obtain ⟨ ⟨ ⟨ K ⟩ , ⟨ X ⟩ ⟩, hX⟩   := X
    obtain ⟨ ⟨ ⟨ J ⟩ , ⟨ Y ⟩ ⟩, hY⟩   := Y
    obtain ⟨ ⟨ ⟨ u ⟩ , ⟨ f ⟩  ⟩ , hf ⟩ := f
    simp at u
    simp at f

    have hf : u = _ :=  VerticalAsPath hf
    simp at hf

    simp
    apply ((P.map ⟨  eqToHom hY.symm⟩ ).map f ≫·)
    have : ∀ {K J I : Bᵒᵖ}{v : K ⟶ J} {u : J ⟶ I} {w : K ⟶ I} (comm : w = v ≫ u) , P.map v ⋙ P.map u = P.map w := fun comm => by symm ; rw [comm] ; apply P.map_comp
    apply eqToHom
    rw [← Functor.comp_obj]
    apply Functor.congr_obj -- (fun r => r.obj X)
    apply this
    apply Quiver.Hom.unop_inj
    simp
    rw [hf]
    symm
    calc
      _ = eqToHom (_) ≫ eqToHom (_) := by rfl
      _ = _ := by rw [eqToHom_trans] ; apply Quiver.Hom.unop_op ; exact hY.symm ; exact hY.trans hX.symm
    ---Remark : this was soo awful , I dont understand why '{ unop := x }.unop' does not compute to x



def fiberComparisonFunctorInv (P : PShCat B) (I : Bᵒᵖ ) : (Grothendieck_obj P) ↓ I.unop  ⥤ P.obj I where
  obj := fiberComparisonFunctorInv_obj
  map := fiberComparisonFunctorInv_map

  map_id := by sorry
  map_comp := by sorry
theorem fiberComparisonIsEquivalence {P : PShCat B} {I : Bᵒᵖ } : IsEquivalence (fiberComparisonFunctor P I) where
  inverse := fiberComparisonFunctorInv P I
  unitIso := by sorry
  counitIso := by sorry
  functor_unitIso_comp := by sorry




lemma cartMorphsAreIsosOnFiber {P : PShCat B} {X Y : totop P} {f : X ⟶ Y} (isCart : isCartesianMorphism (Grth P) f) : IsIso f.unop.fiber.unop  := by
    obtain ⟨  ⟨ u ⟩ , ⟨ f ⟩  ⟩  := f
    let lift := cleavage u ⟨ Y , rfl⟩

    have α := weakCartifCartesian (cartesianMorphismToCartLift' isCart) lift.1
    /-
    let  ⟨ ⟨ J ⟩ , ⟨ Y' ⟩ ⟩   := Y
    let  ⟨ ⟨ K ⟩ , ⟨ X' ⟩ ⟩   := X
    -/

    --simp at u
    simp at f
    constructor
    let mY := (cleavageY u ⟨ Y , rfl⟩ ).1
    have : (cleavageY u ⟨ Y , rfl⟩ ).1.unop.fiber.unop = (P.map ⟨ u ⟩).obj Y.unop.fiber.unop := by unfold cleavageY ; unfold sectionToFiber ; simp ; sorry
    let αc : mY  ⟶ X   := α.choose.1
    --have jo := VerticalAsPath (P:= (Grothendieck_obj P)) (X:=lift.Y) (Y:=(by sorry)) α.choose.2

    have jo : P.map αc.unop.base = 𝟙 _ := by sorry -- Remark: Somehow one should use here VerticalAsPath α.choose.2
    have obs : ((P ⋙ opFunctor).map αc.unop.base) = Functor.id _ := by sorry -- rw [Functor.comp_map,opFunctor_map] ; rw [jo] ;aesop
    let inv : (P.map ⟨ u ⟩).obj Y.unop.fiber.unop ⟶ X.unop.fiber.unop := eqToHom (this.symm) ≫ (αc.unop.fiber.unop) ≫ eqToHom (by rw [obs,Functor.id_obj]) -- : mY.unop.fiber.unop ⟶ X.unop.fiber.unop)
    use inv
    constructor
    ·sorry
    ·sorry
