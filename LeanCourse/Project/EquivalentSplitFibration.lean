import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence

import LeanCourse.Project.FiberedCategories
-- import LeanCourse.Project.Cleavage
-- import LeanCourse.Project.Split
--import LeanCourse.Project.PreSheavesOfCategories
-- import LeanCourse.Project.DiscreteFibration
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
set_option maxHeartbeats 2000000
set_option quotPrecheck false

universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories
variable {B : Cat.{v₁ , v₁}} {I J K : B}
variable {P : fibration B}


open Over
lemma someOverExt {I J : Bᵒᵖ} {u : I ⟶ J} : (Over.map u.unop).obj (Over.mk (𝟙 J.unop)) = Over.mk u.unop := by
  trans Over.mk (𝟙 J.unop ≫ u.unop)
  · rfl
  · apply congrArg _ ; apply Category.id_comp
def replaceTargetOfFiberMap {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) :
  ((((yoObj P).map (fundamentalFibration.map (f.unop.1.unop)).op).obj X.unop.fiber.unop).1).left.obj (Over.mk (𝟙 Y.unop.1.unop)) =
      X.unop.2.unop.1.left.obj (Over.mk f.unop.1.unop) := by
      obtain ⟨⟨ I⟩  , ⟨ X ⟩ ⟩:= X
      obtain ⟨⟨ J ⟩  , ⟨ Y ⟩ ⟩ := Y
      obtain ⟨⟨ u ⟩  , ⟨ α ⟩  ⟩ :=f
      simp ; apply congrArg (X.1.left.obj) ; exact someOverExt
def replaceTargetOfFiberMap' {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) :
  ((((yoObj P).map (fundamentalFibration.map (f.unop.1.unop)).op).obj X.unop.fiber.unop).1).left.obj (Over.mk (𝟙 Y.unop.1.unop)) ⟶
      X.unop.2.unop.1.left.obj (Over.mk f.unop.1.unop) :=  eqToHom (replaceTargetOfFiberMap f)

@[simp] def fiberMap {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) :
  Y.unop.2.unop.1.left.obj (Over.mk (𝟙 _)) ⟶ X.unop.2.unop.1.left.obj (Over.mk f.unop.1.unop)
  := f.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' f
lemma fiberMapVertical  {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) : P.1.hom.map (fiberMap f) = eqToHom (by rw [← comm Y.unop.fiber.unop , ← comm X.unop.fiber.unop] ; rfl) := by
  unfold fiberMap
  rw [Functor.map_comp]
  unfold replaceTargetOfFiberMap'
  rw [eqToHom_map]
  rw [VerticalAsPath (P:=P) <| (f.unop.fiber.unop.2) ⟨ mk (𝟙 Y.unop.base.unop) , rfl⟩ ,eqToHom_trans]



@[simp] def E_functor_map {X Y : (Sp.obj P).1.1.left} (f : Y ⟶ X) : ((E'_obj).obj Y.unop.fiber.unop).1 ⟶((E'_obj).obj X.unop.fiber.unop).1  :=
  fiberMap f ≫ X.unop.2.unop.1.left.map (Over.homMk f.unop.1.unop)




lemma compCartTransExt {P Q : fibration B} {F G H:  P ⟶ Q} (η: F ⟶ G) (ε : G ⟶ H) : (η ≫ ε).1 = η.1 ≫ ε.1 := rfl
@[simp] def toFiberIso {P : fibration B} {X Y : P[I]} (f : X.1 ≅ Y.1) (isVert : isVertical f.hom) : X ≅ Y where
  hom := (⟨ f.hom , isVert⟩)
  inv := by
    use f.inv ; unfold isVertical; unfold isVertical at isVert ;
    rw [← Functor.mapIso_hom P.1.hom f] at isVert ;
    exact ((Iso.eq_inv_comp (P.1.hom.mapIso f)).2 isVert).symm
  hom_inv_id := ( by apply Subtype.ext ; exact f.hom_inv_id )
  inv_hom_id := ( by apply Subtype.ext ; exact f.inv_hom_id )






lemma weird  {B : Cat} {X Y : B} {f : X ⟶ Y}: (map f).obj (mk (𝟙 X)) = mk f := by  unfold map ; unfold Comma.mapRight ;  aesop_cat
lemma E_functor_map_comp  {X' Y' Z' : (Sp.obj P).1.1.left} (g : Z' ⟶Y') (f : Y' ⟶ X') : E_functor_map (g ≫ f) = E_functor_map g ≫ E_functor_map f := by

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
    have hv' : v' = (Over.map u).map v'' ≫ eqToHom (someOverExt) := by

      apply OverMorphism.ext
      simp
      let m := g.unop.base.unop
      symm
      calc
        m ≫ (eqToHom someOverExt).left
          = m ≫ (Over.forget _).map (eqToHom someOverExt) := rfl
        _ = m ≫ eqToHom rfl := by rw [eqToHom_map] ;
        _ = m  ≫ 𝟙 _ := by rw [eqToHom_refl]
        _ = m := by apply Category.comp_id


    let u' : mk u ⟶ mk (𝟙 _ ) := homMk u
    let vu : mk (v ≫ u) ⟶mk (𝟙 _ ) := homMk (v ≫ u)
    let restFunctor := (((PSh_rest fundamentalFibration).obj (yo.obj P)))
    let a' := f.unop.2.unop
    have : ((restFunctor.map ⟨ v ⟩ ).map a').1 = ((CategoryTheory.whiskerLeft (fundamentalFibration.map v).1.1 a'.1) ) := by rfl ;
    let b' := g.unop.2.unop



    let a : Y.1.left ⟶ ((restFunctor.map ⟨ u ⟩ ).obj X).1.left := a'.1
    let α2 : Y.1.left.obj (mk v) ⟶X.1.left.obj (mk (v ≫  u))  := a.app (mk v)



    let h := g ≫ f
    let b : Z.1.left ⟶ ((restFunctor.map ⟨ v ⟩ ).obj Y).1.left := g.unop.2.unop.1
    let ab : Z.1.left ⟶ ((restFunctor.map ⟨ v ≫ u ⟩ ).obj X).1.left := h.unop.2.unop.1
    have ee' := (symm ( restFunctor.map_comp ⟨u⟩ ⟨v⟩))
    let compPath := congrArg (fun F ↦ (F.obj X).1.left ) ee'
    have mh : (map g.unop.base.unop).obj (mk (𝟙 Z'.unop.base.unop)) = mk g.unop.base.unop := by apply weird
    have ee :(((((restFunctor.map ⟨ u ⟩  ≫ restFunctor.map ⟨ v ⟩ ).obj X).1).left) ).obj
            (mk (𝟙 Z'.unop.base.unop)) =
          (X'.unop.fiber.unop.1).left.obj (mk h.unop.base.unop) :=(Functor.congr_obj compPath (mk (𝟙 _))).trans (replaceTargetOfFiberMap h)
    have eee : ((fundamentalFibration.op.map ⟨ u ⟩ ).unop.1).left.obj ((map g.unop.base.unop).obj (mk (𝟙 Z'.unop.base.unop))) =
        mk h.unop.base.unop := by rw [mh] ; rfl

    have complicated : ((restFunctor.map ⟨ v ⟩ ).map a').1.app (mk (𝟙 _)) ≫ eqToHom ee = eqToHom (replaceTargetOfFiberMap g) ≫ α2 := by
        rw [this]


        calc
          _ = a.app ((map v).obj (mk (𝟙 Z'.unop.base.unop)) ) ≫ X.1.left.map (eqToHom eee) := by apply (_≫=· ) ; symm ; apply eqToHom_map
          _ = a.app ((map v).obj (mk (𝟙 Z'.unop.base.unop)) ) ≫ ((restFunctor.map ⟨ u ⟩ ).obj X).1.left.map (eqToHom mh) := by apply (_≫=· ) ; rw [eqToHom_map,eqToHom_map]
          _ =  Y.1.left.map (eqToHom mh) ≫ a.app  (mk v ) := by symm ; rw [← a.2] ;
          _ = _ := by apply (·=≫_) ; apply eqToHom_map




    let vf : ((restFunctor.map ⟨ v ⟩ ).obj Y).1.left ⟶
      (((restFunctor.map ⟨ v ≫ u ⟩ ).obj X)).1.left :=
      ((restFunctor.map ⟨ v ⟩ ).map a').1 ≫ eqToHom compPath



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


def E_functor : (Sp.obj P).1.1.left ⥤ P.1.left where
  obj := fun X ↦ ((E'_obj).obj X.unop.fiber.unop).1
  map :=  E_functor_map

  map_comp := E_functor_map_comp
  map_id := fun X ↦ by
    simp only [Functor.id_obj, Functor.const_obj_obj, fundamentalFibration_obj,
      fundamentalFibrationObj, E'_obj_obj_coe, E_functor_map, Functor.op_obj, Opposite.unop_op,
      domainOver_left, fiberMap, Functor.comp_obj, opFunctor_obj, Functor.comp_map, opFunctor_map,
      domainOver_right, domainOver_hom, isVertical, forget_obj, Category.assoc]
    have : ((homMk (𝟙 X).unop.base.unop) : Over.mk (𝟙 _) ⟶ Over.mk (𝟙 _)) = 𝟙 _ := by rfl
    rw [this]



    let iX : Grothendieck.Hom X.unop X.unop := 𝟙 X.unop
    have p : ((psh.obj P ⋙ opFunctor).map iX.base).obj X.unop.fiber = X.unop.fiber := by
      simp ; rw [((_) : iX.base = 𝟙 _)] ; swap ; rfl ; rw [Functor.map_id] ; aesop
    have : (𝟙 X).unop.fiber = eqToHom p  := by rfl
    have : (𝟙 X).unop.fiber.unop.1 = eqToHom (by simp ; rw [((_) : (𝟙 X).unop.base = 𝟙 _)] ; swap ; rfl ; rw [Functor.map_id] ; aesop) := by
      rw [this]
      rw [eqToHom_unop]

      apply eqToHom_map forgetFibration

    calc
    _ = _ ≫ replaceTargetOfFiberMap' (𝟙 X) ≫ 𝟙 _ := by apply (_≫=· ) ; apply (_≫=·) ; apply Functor.map_id
    _ = ((𝟙 X).unop.fiber.unop.1).app (mk (𝟙 X.unop.base.unop)) ≫ replaceTargetOfFiberMap' (𝟙 X) := by rw [Category.comp_id]
    _ = eqToHom (by symm ; exact replaceTargetOfFiberMap (𝟙 X)) ≫ replaceTargetOfFiberMap' (𝟙 X) := by apply (· =≫_) ; rw [this,eqToHom_app]
    _ = _ := by unfold replaceTargetOfFiberMap' ; rw [eqToHom_trans,eqToHom_refl]





lemma E_functor_IsOverB :  E_functor ⋙ P.1.hom = (Sp.obj P).1.1.hom  := by
  apply Functor.ext ; swap
  · intro X ; simp ; exact ((E'_obj).obj X.unop.fiber.unop).2
  · intro X Y f ; simp ;
    trans P.1.hom.map (E_functor_map f )
    · rfl
    · unfold E_functor_map
      rw [Functor.map_comp,rwFuncComp'',fiberMapVertical,← Category.assoc , eqToHom_trans]
      let u := f.unop.base.unop

      have : ((fundamentalFibration.op.obj Y.unop.base).unop.1).hom.map (homMk u : (mk u ⟶ mk (𝟙 _))) = u := by rfl
      rw [this]
      have : ((Sp.obj P).P.1).hom.map f = u := by rfl
      rw [this]

      -- have helper : (↑P).hom.map ((↑Y.unop.fiber.unop).left.map (homMk f.unop.base.unop))




lemma anyPathIsAutomaticallyVertical {P : fibration B} {I : B} {X : P[I]} {Y : P.1.left} (p : X.1 = Y)  :
  isVertical (eqToHom p : X.1 ⟶ (⟨ Y , (congrArg (P.1.hom.obj) (symm p)).trans X.2⟩ : obj_over I).1) := by aesop_cat
def E (P : fibration B) : Sp.obj P ⥤c P := by
  use Over.homMk E_functor E_functor_IsOverB
  intro Y' X' φ hφ
  let ⟨ ⟨ I ⟩ , ⟨ X ⟩ ⟩ := X'
  let X : fundamentalFibration.obj I ⟶ P := by unfold psh at X ; exact X
  obtain ⟨ ⟨ J ⟩ , ⟨ Y ⟩ ⟩ := Y'

  let Y : fundamentalFibration.obj J ⟶ P := by unfold psh at Y ; exact Y
  have φIsIsoOnFibers := cartMorphsAreIsosOnFiber hφ
  --have this : E_functor_map φ = fiberMap φ ≫ X.unop.2.unop.1.left.map (Over.homMk φ.unop.1.unop) := rfl

  apply compCartesianMorphisms
  ·
    --have eq : fiberMap φ = φ.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' φ := by rfl -- f.1.app (mk (𝟙 _)) ≫ replaceTargetOfFiberMap' φ := by rfl
    --rw [eq]
    have iso1 := cartMorphsAreIsosOnFiber hφ
    have iso1 : IsIso φ.unop.fiber.unop.1 := forgetFibration.map_isIso φ.unop.fiber.unop

    have iso1 : IsIso (φ.unop.fiber.unop.1.app (Over.mk (𝟙 _))) := NatIso.isIso_app_of_isIso φ.unop.fiber.unop.1 _
    have iso2 : IsIso (replaceTargetOfFiberMap' φ):= instIsIsoEqToHom (replaceTargetOfFiberMap φ)

    have isoComp : IsIso (φ.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' φ) := IsIso.comp_isIso  ;
    let uX := (((yoObj P).map (fundamentalFibration.map (φ.unop.1.unop)).op).obj X)
    let t : ((Y / J).obj (⟨ mk (𝟙 _) ,rfl⟩ )).1 ⟶ ((uX / J).obj (⟨ mk (𝟙 _) ,rfl⟩ )).1 := rewrittenTrafo φ.unop.fiber.unop.1 ⟨ Over.mk (𝟙 _) , rfl⟩
    have tIsVerti : isVertical (X:= (Y / J).obj (⟨ mk (𝟙 _) ,rfl⟩ )) t  := by apply  φ.unop.fiber.unop.2 -- rewrittenTrafo (B:=B) (φ.unop.fiber.unop.1) ⟨ Over.mk (𝟙 _) , rfl⟩
    have rew : φ.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' φ = t ≫ eqToHom (replaceTargetOfFiberMap φ) := by apply (· =≫_) ; symm ; rfl

    let iso : (Y / J).obj (⟨ mk (𝟙 _) ,rfl⟩ ) ≅  (X / J).obj ⟨ mk φ.unop.base.unop , rfl ⟩  := by
      apply toFiberIso ; swap
      · exact asIso (φ.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' φ)
      · rw [asIso_hom]
        rw [rew]
        exact compPresVertical t (eqToHom (_)) tIsVerti (anyPathIsAutomaticallyVertical  (_))



    have this :iso.hom.1 = fiberMap φ := by rfl
    rw [← this]
    apply verticalIsosAreCart (P:=P)



  · apply  X.2
    apply automaticallyCart -- (Over.homMk φ.unop.base.unop)
    --have test : isCartesianMorphism fib.1 morph :=automaticallyCart isDisc motph
    --exact test

variable {P : fibration  B} {I : B} {X Y : ((psh.obj P).obj (Opposite.op I)).1}
def TriangleOnFibersCommutesObj (X : ((psh.obj P).obj (Opposite.op I)).1) :  (fiberComparisonFunctor (psh.obj P) (Opposite.op I) ⋙
  toFunctorOnFibers (E P) I).obj X =  E'_obj.obj X := by
    simp ; apply Subtype.ext ; aesop ;
def fcF := fiberComparisonFunctor (psh.obj P) (Opposite.op I)
def myFiberMapFiberUnop  (f : X ⟶ Y) : ((fcF.obj X).1).unop.fiber.unop ⟶  (((psh.obj P ⋙ opFunctor).map (𝟙 (Opposite.op I))).obj ((fcF.obj Y).1).unop.fiber).unop := fiberComparisonFunctor_map_fib f
def myFiberMapFiber  (f : X ⟶ Y) : ((psh.obj P ⋙ opFunctor).map (𝟙 (Opposite.op I))).obj ((fcF.obj Y).1).unop.fiber ⟶ ((fcF.obj X).1).unop.fiber := Opposite.op <| myFiberMapFiberUnop f
def myFiberMap (f : X ⟶ Y) : (fcF.obj X) ⟶ (fcF.obj Y) :=  ⟨ ⟨ 𝟙 (Opposite.op I) , myFiberMapFiber f⟩ , by aesop⟩
lemma helpPath : (((psh.obj P ⋙ opFunctor).map (𝟙 (Opposite.op I))).obj ((fcF.obj Y).1).unop.fiber).unop = Y :=  by rw [Functor.map_id] ;rfl
lemma helpLemma3 (f : X ⟶ Y): myFiberMapFiberUnop f ≫ eqToHom (helpPath) = f := by
        calc
        _ = (f ≫ eqToHom (_)) ≫ eqToHom (helpPath) := by apply (· =≫_) ; rfl
        _ = f ≫ eqToHom (_) := by rw [Category.assoc, eqToHom_trans]
        _ = f ≫ 𝟙 _  := by apply (_≫=·) ; rw [eqToHom_refl]
        _ = _ := by rw [Category.comp_id]


lemma firstPartOfProof (f : X ⟶ Y) : ((myFiberMap f).1.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' ((myFiberMap f).1)) ≫ Y.1.left.map (Over.homMk (𝟙 _))
        = eqToHom (congrArg FiberToTotalSpace.obj (TriangleOnFibersCommutesObj X)) ≫  rewrittenTrafo f.1 ⟨ Over.mk (𝟙 I ) , rfl ⟩ ≫ eqToHom (congrArg FiberToTotalSpace.obj (symm (TriangleOnFibersCommutesObj Y)))  := by
        have helpLemma3' : ∀ u , (myFiberMapFiberUnop f).1.app u ≫ eqToHom (_) = f.1.app u := fun u ↦ by symm ;  calc
          f.1.app u =  ((myFiberMapFiberUnop f) ≫ eqToHom helpPath).1.app u := by rw [helpLemma3 f]
          _ = (forgetFibration.map ((myFiberMapFiberUnop f) ≫ eqToHom helpPath)).app u := by rfl
          _ = (forgetFibration.map ((myFiberMapFiberUnop f)) ≫ forgetFibration.map (eqToHom helpPath)).app u := by rw [Functor.map_comp]
          _ = (forgetFibration.map ((myFiberMapFiberUnop f))).app u ≫ (forgetFibration.map (eqToHom helpPath)).app u := by rfl
          _ = (myFiberMapFiberUnop f).1.app u ≫ eqToHom (_) := by apply (_≫=· ) ; rw [eqToHom_map forgetFibration] ; apply eqToHom_app
        have obs: eqToHom (congrArg FiberToTotalSpace.obj (TriangleOnFibersCommutesObj X)) = 𝟙 _ := by apply eqToHom_refl
        have test : rewrittenTrafo f.1 ⟨ Over.mk (𝟙 I ) , rfl ⟩ = f.1.app (Over.mk (𝟙 _)) := by aesop
        have test2 : (myFiberMap f).1.unop.fiber.unop.1.app (Over.mk (𝟙 _)) = (myFiberMapFiber f).unop.1.app (Over.mk (𝟙 _))  := by rfl
        calc
        _ = ((myFiberMapFiber f).unop.1.app (Over.mk (𝟙 _)) ≫ eqToHom ( replaceTargetOfFiberMap ((myFiberMap f).1))) ≫ Y.1.left.map (𝟙 _) := eq_whisker_eq (test2 =≫ _) (congrArg Y.1.left.map (by rfl))
        _ = ((myFiberMapFiber f).unop.1.app (Over.mk (𝟙 _)) ≫ eqToHom ( replaceTargetOfFiberMap ((myFiberMap f).1))) ≫ (𝟙 _) := by apply (_≫=· ) ; apply Functor.map_id
        _ = (myFiberMapFiber f).unop.1.app (Over.mk (𝟙 _)) ≫ eqToHom ( replaceTargetOfFiberMap ((myFiberMap f).1)) := by apply Category.comp_id
        _ = (myFiberMapFiberUnop f).1.app (Over.mk (𝟙 _)) ≫ eqToHom ( replaceTargetOfFiberMap ((myFiberMap f).1)) := by apply (· =≫_) ; rfl
        _ = ((myFiberMapFiberUnop f).1.app (Over.mk (𝟙 _)) ≫ eqToHom (_) )≫ eqToHom (congrArg FiberToTotalSpace.obj (symm (TriangleOnFibersCommutesObj Y))) := by symm ; rw [Category.assoc] ; apply (_≫=·) ; rw [eqToHom_trans] ; rw [Functor.map_id] ; aesop_cat
        _ = f.1.app (Over.mk (𝟙 _)) ≫ eqToHom (congrArg FiberToTotalSpace.obj (symm (TriangleOnFibersCommutesObj Y))) := by apply (· =≫_) ; exact helpLemma3' (Over.mk (𝟙 _))
        _ = eqToHom (congrArg FiberToTotalSpace.obj (TriangleOnFibersCommutesObj X)) ≫ f.1.app (Over.mk (𝟙 _)) ≫ eqToHom (congrArg FiberToTotalSpace.obj (symm (TriangleOnFibersCommutesObj Y))) := by symm ; rw [obs , Category.id_comp ]
        _= _ := by apply (_≫=· ) ; apply (·=≫_) ; exact (test.symm)

theorem TriangleOnFibersCommutes  :
  fiberComparisonFunctor (psh.obj P) (Opposite.op I) ⋙
  toFunctorOnFibers (E P) I =
  E'_obj (P:=P) (I:=I) := by
-- (F:= fiberComparisonFunctor (psh.obj P) (Opposite.op I) ⋙ (toFunctorOnFibers (E P) I))
    apply Functor.ext   ; swap
    · intro X; exact TriangleOnFibersCommutesObj X
    · intro X Y f ; apply Subtype.ext ;
      have goal : (fcF.map f).1 = ⟨ 𝟙 (Opposite.op I) , Opposite.op (fiberComparisonFunctor_map_fib f)⟩ := by apply fiberComparisonFunctor_map_coe
      calc
      ((fcF ⋙ (E P / I)).map f).1
        = ((E P / I).map (fcF.map f)).1  := by rw [Functor.comp_map]
      _ = ((E P / I).map (fcF.map f)).1   := by rfl
       _ = (E P).1.left.map (fcF.map f).1 := by rfl
       _ = E_functor_map (fcF.map f).1 := by rfl
       _ = E_functor_map (myFiberMap f).1 := by apply congrArg E_functor_map ; exact (goal.symm)
       _ = fiberMap ((myFiberMap f).1) ≫ Y.1.left.map (Over.homMk (𝟙 _)) := by unfold E_functor_map ; rfl --; apply (_ ≫= ·) ; rw [Functor.map_id] , 𝟙
       _ = ((myFiberMap f).1.unop.fiber.unop.1.app (Over.mk (𝟙 _)) ≫ replaceTargetOfFiberMap' ((myFiberMap f).1)) ≫ Y.1.left.map (Over.homMk (𝟙 _)) := by rfl
       _ = eqToHom (congrArg FiberToTotalSpace.obj (TriangleOnFibersCommutesObj X)) ≫  rewrittenTrafo f.1 ⟨ Over.mk (𝟙 I ) , rfl ⟩ ≫ eqToHom (congrArg FiberToTotalSpace.obj (symm (TriangleOnFibersCommutesObj Y)))  := firstPartOfProof f
      _ = FiberToTotalSpace.map (eqToHom (TriangleOnFibersCommutesObj X)) ≫  FiberToTotalSpace.map (E'_obj.map f) ≫ FiberToTotalSpace.map (eqToHom (symm (TriangleOnFibersCommutesObj Y)))  := by rw [← eqToHom_map FiberToTotalSpace] ; apply (_≫=· ) ; apply (eq_whisker_eq) ; rfl ; symm ; apply eqToHom_map FiberToTotalSpace
      _ = FiberToTotalSpace.map (eqToHom (TriangleOnFibersCommutesObj X) ≫  E'_obj.map f ≫ eqToHom (symm (TriangleOnFibersCommutesObj Y))) := by symm ; rw [Functor.map_comp , Functor.map_comp]

theorem EisEquiv {P : fibration B} : isEquivalenceInBicategory (E P) := by
  apply equivalenceOfFibrationsCheckOnFibers ;
  intro I ;
  let X :=  psh.obj P
  apply IsEquivalence.cancelCompLeft (fiberComparisonFunctor X (Opposite.op I)) _
  · exact fiberComparisonIsEquivalence
  · rw [TriangleOnFibersCommutes] ; exact equivOnFibers
-/
