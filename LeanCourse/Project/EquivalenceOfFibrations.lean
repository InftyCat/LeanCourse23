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
@[simp]
noncomputable def objPreimage  {P Q : fibration B} (F : P ⟶ Q) [VertEssSurj F]  (Y : Q.1.left) : obj_over (P:=P.1.hom) (Q.1.hom.obj Y) :=
   (mem_isVertEssSurj (F:=F) Y).choose




/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `X`. -/
@[simp]
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
  map_id X := by  sorry--  apply F.1.left.map_injective;
  map_comp {X Y Z} f g := by  sorry -- apply F.1.left.map_injective; simp ;
private noncomputable def counit : (equivalenceInverse F) ⋙ F.1.left ≅ 𝟙 Q.1.left :=
  NatIso.ofComponents (fun X ↦ FiberToTotalSpace.mapIso (objObjPreimageIso F X)) (by sorry)

  /-
  Surpringsingly we need first the following theorem to proceed: Do we?
  -/


private noncomputable def equivalenceOverInverse  : Q.1 ⟶ P.1 := by
  have overMorphism : (equivalenceInverse F) ⋙ P.1.hom = Q.1.hom :=  by
    apply Functor.ext ; swap ;
    · intro X ; unfold equivalenceInverse ; simp ;
      let pre := (mem_isVertEssSurj (F:=F) X).choose --obtain ⟨ pre , myIso ⟩
      trans (P.1.hom.obj (pre.1))
      · apply congrArg P.1.hom.obj ; simp ;-- unfold objPreimage
      · exact pre.2

    · sorry -- Remark: I will later give a more interesting proof of Over Naturality
  exact Over.homMk (equivalenceInverse F : Q.1.left ⟶ P.1.left)  overMorphism


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
noncomputable def ofFullyFaithfullyEssVertSurj  :
  isEquivalenceInBicategory F where
      inverse := equivalenceFibrationInverse F
      unitIso := by
                  apply CartTrafoOfComp ; swap
                  · exact (NatIso.ofComponents (fun X => (F.1.left.preimageIso <| FiberToTotalSpace.mapIso (objObjPreimageIso F (F.1.left.obj X))).symm)
                    fun f => by
                    apply F.1.left.map_injective
                    sorry)
                  · sorry
      counitIso := by
                      apply CartTrafoOfComp ; swap
                      · exact counit F
                      · intro A T
                        unfold rewrittenTrafo
                        rw [eqToHom_refl, eqToHom_refl]
                        rw [Category.comp_id, Category.id_comp]
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
  have faithfull : Faithful F' := by sorry

  apply ofFullyFaithfullyEssVertSurj
