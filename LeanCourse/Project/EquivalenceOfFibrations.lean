import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition
import LeanCourse.Project.CartesianFunctors
import LeanCourse.Project.FibrationBicategory
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

variable {B : Cat.{v₁ , u₁}} {I J K : B}


variable {P Q : fibration B}{F : P ⟶ Q}

--notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A

theorem Faithfulness : (∀ (I : B) ,  IsEquivalence (F / I) ) → (∀ Y X : P.1.left , Function.Injective (F.1.left.map : (Y ⟶ X) → (F.1.left.obj Y ⟶ F.1.left.obj X))) := by

      intro ass
      intro Y X

      let F' := F.1.left
      intro ρ ρ' hρ
      let f := F'.map ρ
      let u := P.1.hom.map ρ
      let I := P.1.hom.obj X
      let J := P.1.hom.obj Y
      let Xf : obj_over I := ⟨X , rfl⟩
      let Yf : obj_over J := ⟨Y , rfl⟩
      obtain ⟨⟨ Y' , φ⟩  , hφ⟩   := P.2 u Xf
      have isCart : isCartesianMorphism P.1 φ.1 := cartLiftToCartMor ⟨_ , hφ⟩

      have goal : isWeakCartesian (P:=Q.1.hom) (morphismToLift (F'.map φ.1)) := weakCartifCartesian ⟨_ , F.2 _ isCart⟩
      have p : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj Y'.1) := by rw [← comm F, ← comm F] ; symm ; exact Y'.2





      let J' := Q.1.hom.obj (F'.obj Y'.1)

      let ρ1 : over_hom (u) Yf Xf := by use ρ ; rw [eqToHom_refl,eqToHom_refl, Category.comp_id,Category.id_comp]
      let ρ1' : over_hom (u) Yf Xf := by use ρ' ; rw [rwFuncComp' F , eqToHom_refl,eqToHom_refl, Category.comp_id,Category.id_comp,← hρ, ← rwFuncComp' F]

      obtain ⟨ ν , hν ⟩ := (weakCartifCartesian ⟨ _ , hφ⟩ ⟨ _ , ρ1 ⟩  )
      obtain ⟨ ν' , hν' ⟩ := (weakCartifCartesian ⟨ _ , hφ⟩ ⟨ _ , ρ1' ⟩  )
      have t : ρ = ν.1 ≫ φ.1 := by rw [hν.1 ]
      have t' : ρ' = ν'.1 ≫ φ.1 := by rw [hν'.1 ]
      let Fφ := F'.map φ.1
      rw [t,t']
      have this : (morphismToLift (P:=Q.1.hom) Fφ).φ.1 = Fφ := rfl

      let f1 : over_hom (P:=Q.1.hom) (Q.1.hom.map (Fφ)) ⟨ F'.obj Y , p⟩  ⟨ F'.obj X , rfl⟩  := by
        use f ;
        have this := (mappingOverHom F ρ1).2
        have this' := (mappingOverHom F φ).2
        rw [eqToHom_refl,Category.comp_id]
        apply ((IsIso.of_iso (eqToIso (symm (comm F)))).mono_of_iso).right_cancellation
        rw [eqToIso.hom,Category.assoc, rwFuncComp F]
        rw [rwFuncComp F,← Category.assoc, eqToHom_trans]

        have this : P.1.hom.map φ.1 = _ := by
          trans P.1.hom.map φ.1 ≫ eqToHom (rfl)
          · aesop -- Remark: I dont understand why this code fails: rw [eqToHom_refl ,Category.comp_id]
          · exact φ.2
        have this2 : P.1.hom.map ρ = _ := by
          trans P.1.hom.map ρ ≫ eqToHom (rfl)
          · rw [eqToHom_refl ,Category.comp_id]
          · exact ρ1.2
        rw [this,← Category.assoc ,eqToHom_trans,this2,← Category.assoc,eqToHom_trans]


      let fLift : liftOfAlong ⟨ F'.obj X , rfl⟩ (Q.1.hom.map Fφ) := ⟨ ⟨ F'.obj Y , p ⟩ , f1⟩

      apply (·=≫ φ.1)
      congr
      apply (F / J).map_injective

      apply liftFromCartesiannessIsUnique (weakCartifCartesian (cartFunctorPresCartLifts ⟨ _ , hφ⟩ ))
      have rem1 : ((F / J).map ν).1 ≫ (morphismToLift <| F'.map φ.1).φ.1 = fLift.φ.1 := by

          rw [this]

          unfold toFunctorOnFibers;rw [← F'.map_comp] ; rw [hν.1]

      have rem2 : ((F / J).map ν').1 ≫ (morphismToLift <| F'.map φ.1).φ.1 = fLift.φ.1 := by
          rw [this]
          unfold toFunctorOnFibers;rw [← F'.map_comp] ; rw [hν'.1] ; exact hρ.symm
      exact (rem1.trans (rem2.symm))


theorem Fullness {F : P ⟶ Q}: (∀ (I : B) ,  IsEquivalence (F / I) ) → (∀ Y X : P.1.left , Function.Surjective (F.1.left.map : (Y ⟶ X) → (F.1.left.obj Y ⟶ F.1.left.obj X))) := by

      intro ass
      intro Y X

      let F' := F.1.left
      intro f
      let u := Q.1.hom.map f
      let I := Q.1.hom.obj (F'.obj X)
      let J := Q.1.hom.obj (F'.obj Y)
      let Xf : obj_over I := ⟨X , comm F⟩
      let Yf : obj_over J := ⟨Y , comm F⟩
      obtain ⟨⟨ Y' , φ⟩  , hφ⟩   := P.2 u Xf
      have isCart : isCartesianMorphism P.1 φ.1 := cartLiftToCartMor ⟨_ , hφ⟩

      have goal : isWeakCartesian (P:=Q.1.hom) (morphismToLift (F'.map φ.1)) := weakCartifCartesian ⟨_ , F.2 _ isCart⟩
      have p : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj Y'.1) := by
        calc
              _ = P.1.hom.obj Y' := symm (Y'.2)
             _ = _ := comm F

      let Fφ : over_hom (P:=Q.1.hom) (((Q.1).hom.map (F'.map φ.1))) ⟨ F'.obj Y , p ⟩ ⟨ F'.obj X , rfl⟩  := by
        use f
        rw [← Functor.comp_map]
        have rwr : (F' ⋙ Q.1.hom).map φ.1 = _ := Functor.congr_hom (Over.w F.1) φ.1
        rw [rwr]
        rw [φ.2]
        rw [←Category.assoc,eqToHom_trans]
        rw [←Category.assoc,eqToHom_trans]
        aesop

      obtain ⟨ g , hg⟩  := goal ⟨ _ , Fφ⟩

      let J' := Q.1.hom.obj (F'.obj Y'.1)
      let Y1 : obj_over J' := ⟨ Y  , (comm F).trans p⟩
      let Y1' : obj_over (P:=P.1.hom) J' := ⟨ Y'.1 , comm F⟩
      have p1 : (F / J').obj  Y1 = ⟨ F'.obj Y ,p⟩ := rfl
      have p2 : (F / J').obj Y1'  = ⟨F'.obj Y'.1 , rfl⟩ := rfl

      let pre_g  : Y1 ⟶ Y1' := (Equivalence.fullOfEquivalence (F / J')).preimage (eqToHom p1 ≫ g ≫ eqToHom (symm p2))  --: Yf ⟶ Y'
      have pre_gh : F.1.left.map pre_g.1 = (eqToHom p1).1 ≫ g.1 ≫ (eqToHom (symm p2)).1 := by
        calc
        F.1.left.map pre_g.1
          = ((F / J').map pre_g).1 := rfl
        _ = (eqToHom p1 ≫ g ≫ eqToHom (symm p2)).1 := by rw [(Equivalence.fullOfEquivalence (F / J')).witness (eqToHom p1 ≫ g ≫ eqToHom (symm p2)) ]
        _ = FiberToTotalSpace.map (eqToHom p1 ≫ g ≫ eqToHom (symm p2)) := by rfl
        _ = FiberToTotalSpace.map (eqToHom p1) ≫ FiberToTotalSpace.map g ≫ FiberToTotalSpace.map (eqToHom (symm p2)) := by rw [FiberToTotalSpace.map_comp , FiberToTotalSpace.map_comp ]
        _ = _ := by rfl


      let pre_f : Y ⟶ X := pre_g.1 ≫ φ.1
      use pre_f
      rw [Functor.map_comp]
      rw [pre_gh]
      let hg : g.1 ≫ F'.map φ.1 = f := hg.left
      rw [← hg]
      symm
      trans (g.1 ≫ F.1.left.map φ.1)
      · rfl
      · apply (· =≫ F.1.left.map φ.1)
        rw [eqToHom_refl, eqToHom_refl] ; symm ;
        calc
        _ = FiberToTotalSpace.map (𝟙 _) ≫ FiberToTotalSpace.map g ≫ FiberToTotalSpace.map (𝟙 _) := by rfl
        _ = 𝟙 _ ≫ FiberToTotalSpace.map g ≫ FiberToTotalSpace.map (𝟙 _) := by apply (· =≫_) ; rw [FiberToTotalSpace.map_id]
        _ = FiberToTotalSpace.map g ≫ FiberToTotalSpace.map (𝟙 _) :=by apply Category.id_comp
        _ = FiberToTotalSpace.map g  ≫ 𝟙 _ := by apply (FiberToTotalSpace.map g ≫= · ) ; rw [FiberToTotalSpace.map_id]
        _ = FiberToTotalSpace.map g := by apply Category.comp_id
        _ = g.1 := by rfl
       -- (F.1.left.map φ.1) -- aesop







def VertEssImg {P Q : fibration B} (F : P ⟶ Q): Set Q.1.left :=  fun X =>
  ∃ Y : obj_over (P:=P.1.hom) (Q.1.hom.obj X) , Nonempty ((F / (Q.1.hom.obj X)).obj Y ≅ ⟨ X , rfl⟩ )

class VertEssSurj  {P Q : fibration B} (F : P ⟶ Q) : Prop where
  mem_isVertEssSurj : ∀ (X : Q.1.left ) , X ∈ VertEssImg F
open VertEssSurj

noncomputable def objPreimage  {P Q : fibration B} (F : P ⟶ Q) [VertEssSurj F]  (Y : Q.1.left) : obj_over (P:=P.1.hom) (Q.1.hom.obj Y) :=
   (mem_isVertEssSurj (F:=F) Y).choose




/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `X`. -/

noncomputable def objObjPreimageIso   {P Q : fibration B} (F : P ⟶ Q) [VertEssSurj F]  (X : Q.1.left):
  (F / (Q.1.hom.obj (X))).obj (objPreimage F X)  ≅ ⟨ X , rfl⟩  :=
  Classical.choice (mem_isVertEssSurj (F:=F) X).choose_spec
/-
instance EssSurjOfisVertEssSurj {P Q : fibration B} (F : P ⟶ Q) [VertEssSurj F] : EssSurj F.1.left := by
      constructor ; intro X ;
      obtain ⟨ Y , hY ⟩ := mem_isVertEssSurj (F:=F) X
      use Y.1
      let iso : F.1.left.obj Y.1 ≅ X   := FiberToTotalSpace.mapIso hY
      constructor
      exact iso
-/

open Equivalence
/-
Remark:
The following functions are partly stolen from mathlib Equivalence.
The problem why i cant use the methods directly is because the inverse of an equivalence on total categories does not have to lie over B
-/

variable {P Q : fibration B} (F : P ⟶ Q)  [Full F.1.left] [Faithful F.1.left] [ VertEssSurj F]
@[simps]
private noncomputable def equivalenceInverse : Q.1.left ⥤ P.1.left
    where
  obj X :=  (objPreimage F X).1
  map {X Y} f := F.1.left.preimage ((objObjPreimageIso F X).hom.1 ≫ f ≫ ((objObjPreimageIso F Y).inv.1))
  map_id X := by
    apply F.1.left.map_injective;
    rw [Functor.image_preimage,Functor.map_id , Category.id_comp] ;
    trans ((objObjPreimageIso F X).hom ≫ (objObjPreimageIso F X).inv).1
    · rfl
    · rw [Iso.hom_inv_id] ; rfl

  map_comp {X Y Z} f g := by
    apply F.1.left.map_injective;
    rw [Functor.map_comp,Functor.image_preimage,Functor.image_preimage,Functor.image_preimage] ;
    symm
    calc
    ((objObjPreimageIso F X).hom.1 ≫ f ≫ (objObjPreimageIso F Y).inv.1) ≫ (objObjPreimageIso F Y).hom.1 ≫ g ≫ (objObjPreimageIso F Z).inv.1
      = (((objObjPreimageIso F X).hom.1 ≫ f) ≫ (objObjPreimageIso F Y).inv.1) ≫ (objObjPreimageIso F Y).hom.1 ≫ g ≫ (objObjPreimageIso F Z).inv.1 := by apply (· =≫_) ; rw [← Category.assoc]
    _ = ((objObjPreimageIso F X).hom.1 ≫ f) ≫ ((objObjPreimageIso F Y).inv.1 ≫ (objObjPreimageIso F Y).hom.1) ≫ (g ≫ (objObjPreimageIso F Z).inv.1) := by rw [exchangeLaw]
    _ = ((objObjPreimageIso F X).hom.1 ≫ f) ≫ ((objObjPreimageIso F Y).inv ≫ (objObjPreimageIso F Y).hom).1 ≫ (g ≫ (objObjPreimageIso F Z).inv.1) := by rfl
    _ = ((objObjPreimageIso F X).hom.1 ≫ f) ≫ 𝟙 _ ≫ (g ≫ (objObjPreimageIso F Z).inv.1) := by rw [Iso.inv_hom_id] ; rfl
    _ = ((objObjPreimageIso F X).hom.1 ≫ f) ≫ (g ≫ (objObjPreimageIso F Z).inv.1) := by rw [Category.id_comp]
    _ = (objObjPreimageIso F X).hom.1 ≫ (f ≫ g) ≫ (objObjPreimageIso F Z).inv.1 := by rw [← exchangeLaw]
/-
lemma compMap {X Y : Q.1.left} {f : X ⟶ Y} : (equivalenceInverse F ⋙ F.1.left).map f = (objObjPreimageIso F X).hom.1 ≫ f ≫ (objObjPreimageIso F Y).inv.1 := by
  rw [Functor.comp_map , Functor.mapIso_hom, Functor.mapIso_hom]
  unfold equivalenceInverse ; rw [Functor.image_preimage]
  -/
lemma VerticalAsPath {P : fibration B} {I} {X Y : P[I]} {f : X.1 ⟶ Y.1} (isV : isVertical f) : P.1.hom.map f = eqToHom (X.2.trans Y.2.symm) := by
  calc
  P.1.hom.map f = (P.1.hom.map f ≫ eqToHom (Y.2)) ≫ eqToHom Y.2.symm := by symm ; rw [Category.assoc, eqToHom_trans,eqToHom_refl,Category.comp_id]
  _ = eqToHom X.2 ≫ eqToHom Y.2.symm := by apply (· =≫_) ; exact isV
  _ = _ := by rw [eqToHom_trans]
private noncomputable def counit : (equivalenceInverse F) ⋙ F.1.left ≅ 𝟙 Q.1.left := by
  apply NatIso.ofComponents ;swap
  · intro X
    exact FiberToTotalSpace.mapIso (objObjPreimageIso F X)
  · intro X Y f ; rw [Functor.comp_map , Functor.mapIso_hom, Functor.mapIso_hom]
    unfold equivalenceInverse ; rw [Functor.image_preimage , (Category.assoc _ _ _).trans exchangeLaw]
    calc
    _ = _ ≫ FiberToTotalSpace.map ((objObjPreimageIso F Y).inv ≫ (objObjPreimageIso F Y).hom) := by apply (_≫=·) ; symm ; apply FiberToTotalSpace.map_comp
    _ = ((objObjPreimageIso F X).hom.1 ≫ f) := by rw [Iso.inv_hom_id , Functor.map_id , Category.comp_id]
    _ = _ := by aesop

private noncomputable def equivalenceOverInverse  : Q.1 ⟶ P.1 := by
  have overMorphism : (equivalenceInverse F) ⋙ P.1.hom = Q.1.hom :=  by
    apply Functor.ext ; swap ;
    · intro X ; unfold equivalenceInverse ; simp ;
      let pre := (mem_isVertEssSurj (F:=F) X).choose --obtain ⟨ pre , myIso ⟩
      trans (P.1.hom.obj (pre.1))
      · apply congrArg P.1.hom.obj ; simp ; rfl-- unfold objPreimage
      · exact pre.2

    · intro X Y f

      let f' := (equivalenceInverse F).map f
      have th1 : Q.1.hom.map ((objObjPreimageIso F X).hom.1)  = eqToHom (_) := VerticalAsPath (objObjPreimageIso F X).hom.2
      have th2 : Q.1.hom.map (objObjPreimageIso F Y).inv.1 = eqToHom (_) := VerticalAsPath (objObjPreimageIso F Y).inv.2
      have this : ((F.1).left).map f' = (objObjPreimageIso F X).hom.1 ≫ f ≫ (objObjPreimageIso F Y).inv.1 := by
        calc
        _ = F.1.left.map ((equivalenceInverse F).map f) := rfl
        _ = F.1.left.map (F.1.left.preimage ((objObjPreimageIso F X).hom.1 ≫ f ≫ ((objObjPreimageIso F Y).inv.1))) := rfl
        _ = _ := by rw [Functor.image_preimage F.1.left]

      calc _ = P.1.hom.map f' := by rw [Functor.comp_map (equivalenceInverse F) P.1.hom f]
        _ = eqToHom (comm F) ≫ Q.1.hom.map (F.1.left.map f') ≫ eqToHom ((comm F).symm) := rwFuncComp' F f'
        _ = eqToHom (comm F) ≫ Q.1.hom.map ((objObjPreimageIso F X).hom.1 ≫ f ≫ (objObjPreimageIso F Y).inv.1) ≫ eqToHom ((comm F).symm) := by rw [this]
        _ = eqToHom (comm F) ≫ (Q.1.hom.map ((objObjPreimageIso F X).hom.1) ≫ Q.1.hom.map f ≫ Q.1.hom.map (objObjPreimageIso F Y).inv.1) ≫ eqToHom ((comm F).symm) := by rw [Functor.map_comp,Functor.map_comp]
        _ = (eqToHom (comm F) ≫ eqToHom (_)) ≫ (Q.1.hom.map f ≫ Q.1.hom.map (objObjPreimageIso F Y).inv.1) ≫ eqToHom ((comm F).symm)  := by rw [exchangeLaw] ; rw [th1]
        _ = eqToHom (_) ≫ (Q.1.hom.map f ≫ Q.1.hom.map (objObjPreimageIso F Y).inv.1) ≫ eqToHom ((comm F).symm)  := by rw [eqToHom_trans]
        _ = eqToHom (_) ≫ Q.1.hom.map f ≫ Q.1.hom.map (objObjPreimageIso F Y).inv.1 ≫ eqToHom ((comm F).symm)  := by rw [Category.assoc]
        _ = eqToHom (_) ≫ Q.1.hom.map f ≫ eqToHom (_)  := by rw [th2 , eqToHom_trans]

  exact Over.homMk (equivalenceInverse F : Q.1.left ⟶ P.1.left) overMorphism


lemma counitIsVertical : ∀ {A : B} (T : obj_over (P :=Q.1.hom) A) ,
  isVertical (X:= objMappingBetweenFibers (equivalenceOverInverse F ≫ F.1) T) (X' := T) ((counit F).app T.1).hom := by
                        intro A T
                        unfold isVertical
                        let φ : ((F / (Q.1).hom.obj T.1).obj (objPreimage F T.1)) ⟶ ⟨ T.1 , rfl⟩  := (objObjPreimageIso F T.1).hom
                        have hφ' := (objObjPreimageIso F T.1).hom.2
                        have thisIsExactlyThegoal : isVertical φ.1 := hφ'
                        unfold isVertical at thisIsExactlyThegoal
                        have path := ((F / (Q.1).hom.obj T.1).obj (objPreimage F T.1)).2
                        have test : (Q.1).hom.map ((counit F).app T.1).hom  = eqToHom (path) := calc
                          _ = Q.1.hom.map φ.1 := rfl
                          _ = Q.1.hom.map φ.1 ≫ eqToHom (rfl) := by symm ; rw [eqToHom_refl, Category.comp_id]
                          _ = eqToHom (path ) := thisIsExactlyThegoal
                        rw [test]
                        rw [eqToHom_trans]
theorem functorCompositeIsCartesian  :
    ∀ {X Y : Q.1.1} (φ : X ⟶ Y) (_ : isCartesianMorphism Q.1 φ) ,
       isCartesianMorphism Q.1 ((equivalenceInverse F ⋙ F.1.left).map φ) := by
          intro X Y f hf
          have myfunc : (equivalenceInverse F ⋙ F.1.left).map f = (counit F).hom.app _ ≫ f ≫ (counit F).inv.app _  := by symm ; apply CategoryTheory.NatIso.naturality_2

          rw [myfunc] ;
          apply compCartesianMorphisms
          · apply verticalIsosAreCart -- Remark : I dont understand why this works

          · apply compCartesianMorphisms
            · exact hf
            · rw [← Iso.symm_hom, ← NatIso.app_hom] ;
              apply verticalIsosAreCart'' (P:=Q) (X:= objMappingBetweenFibers (equivalenceOverInverse F ≫ F.1) ⟨ Y,rfl⟩ ) (Y:= ⟨ Y, rfl⟩)  ((counit F).symm.app Y)
              rw [NatIso.app_hom , Iso.symm_hom, ← NatIso.app_inv (CategoryTheory.FiberedCategories.counit F) Y] ;
              apply isVertical_symm
              exact (counitIsVertical F ⟨ Y , rfl⟩ )
private noncomputable def equivalenceFibrationInverse: Q ⟶ P := ⟨ equivalenceOverInverse F  , by
  intro X Y f hf
  have goal : isCartesianMorphism Q.1 ((equivalenceInverse F ⋙ F.1.left).map f)  := functorCompositeIsCartesian F f hf
  rw [Functor.comp_map] at goal
  have goal : isCartesianMorphism P.1 ((equivalenceInverse F).map f) := FullyFaithfullCartFunctorReflectsCartMorph F (by assumption) (by assumption) _ _ _ goal
  assumption⟩
lemma preImageOfVerticalIsVertical {A : B}  {X Y : P [A]} (f : (F / A).obj X ⟶ (F / A).obj Y) : isVertical (F.1.left.preimage (f.1)) := by
  unfold isVertical
  --rw [swapPaths (rwFuncComp F _).symm]
  rw [rwFuncComp' F , Category.assoc ,Category.assoc , eqToHom_trans, Functor.image_preimage, f.2,eqToHom_trans]




noncomputable def ofFullyFaithfullyEssVertSurj  :
  isEquivalenceInBicategory F where
      inverse := equivalenceFibrationInverse F
      unitIso := by
                  apply CartTrafoOfComp ; swap
                  · exact (NatIso.ofComponents (fun X => (F.1.left.preimageIso <| FiberToTotalSpace.mapIso (objObjPreimageIso F (F.1.left.obj X))).symm)

                    fun {X} {Y} f => by
                      apply F.1.left.map_injective
                      simp
                      have fst : (F.1).left.map (((𝟙 P : P ⥤c P).1).left.map f) = F.1.left.map f := by rfl
                      rw [fst]
                      have goal := (counit F).inv.2 (F.1.left.map f)
                      calc
                      _ = (Functor.id Q.1.left).map (F.1.left.map f) ≫ (CategoryTheory.FiberedCategories.counit F).inv.app (F.1.left.obj Y) := by rfl
                      _ = (counit F).inv.app (F.1.left.obj X) ≫ (equivalenceInverse F ⋙ F.1.left).map (F.1.left.map f) := goal
                      _ = _ := by rfl

                  )

                  · intro A T ; unfold rewrittenTrafo ;
                    let F' := F.1.left
                    let T' : obj_over (P:=P.1.hom) A := ⟨ (objPreimage F (F'.obj T.1)).1 , by rw [(objPreimage F (F'.obj T.1)).2, ← comm F, T.2] ⟩
                    let morph : F.1.left.obj T.1 ⟶ F.1.left.obj T'.1 := (objObjPreimageIso F (F.1.left.obj T.1)).symm.hom.1
                    let m : (F / A).obj T ⟶ (F / A).obj T' := by
                      use morph
                      have this := (objObjPreimageIso F (F.1.left.obj T.1)).symm.hom.2
                      unfold isVertical ;
                      have this : (Q.1.hom.map morph ≫ eqToHom (comm F).symm) = eqToHom (by rw [T'.2 , ← comm F , T.2] ) := by
                        have t := VerticalAsPath this

                        calc
                          Q.1.hom.map morph ≫ eqToHom ( (comm F).symm) = eqToHom (_) ≫   eqToHom ( (comm F).symm) := by apply (· =≫_) ; exact t
                          _ = eqToHom (_) := by rw [eqToHom_trans]
                      calc
                      _ = (Q.1.hom.map morph ≫ eqToHom (comm F).symm) ≫ eqToHom (T'.2) := by symm ; rw [Category.assoc , eqToHom_trans]
                      _ = eqToHom (by rw [(comm F).symm , T'.2,T.2] ) ≫ eqToHom T'.2 := by rw [this]
                      _ = eqToHom ((by rw [← comm F, T.2] )) := by rw [eqToHom_trans]

                    have : isVertical (X:= T) (X':=T') ( F.1.left.preimage morph) := preImageOfVerticalIsVertical F m
                    exact this

      counitIso := by
                      apply CartTrafoOfComp ; swap
                      · exact counit F
                      · intro A T

                        --nfold NatIso.ofComponents
                        apply counitIsVertical


                        --simp

theorem equivalenceOfFibrationsCheckOnFibers : (∀ (I : B) ,  IsEquivalence (F / I) ) → isEquivalenceInBicategory F := fun ass ↦ by
  let F' := F.1.left
  have essSurj : VertEssSurj F :=  by
    constructor
    intro q
    let I := Q.1.hom.obj q
    -- specialize ass I
    obtain ⟨ p , ⟨ hp ⟩  ⟩  := (Equivalence.essSurj_of_equivalence (F / I)).mem_essImage ⟨ q , rfl⟩
    use p
    constructor
    apply hp

  have full : Full F' := by
    constructor
    swap
    ·  intro X Y f ; exact (Fullness ass _ _ f).choose

    ·  intro X Y f ; exact (Fullness ass _ _ f).choose_spec
  have faithfull : Faithful F' := ⟨  by apply Faithfulness ass ⟩

  apply ofFullyFaithfullyEssVertSurj
