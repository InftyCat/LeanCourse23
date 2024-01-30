import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition
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
notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A

variable {P Q : fibration B}(F : P ⟶ Q)
lemma comm  : ∀ {A} , P.1.hom.obj A =  Q.1.hom.obj (F.1.left.obj A) :=  fun {A} ↦ by rw [← Functor.comp_obj , ← Over.w F.1] ; apply Functor.congr_obj ; rfl

-- lemma over_comp_coe

lemma verticalIsosAreCart' {P : fibration B} {X Y : P [I]} (f : Y ≅ X) : isCartesian ⟨ Y ,  coercBack f.hom ⟩ := by
      intro J u L ;
      --let ψ := L.φ.1 ≫ (morphismToLift f.inv.1).φ.1

      let invLift := (coercBack f.inv)
      let t := over_comp (by rw [Category.comp_id ,Category.comp_id]) invLift L.φ
      -- let ψO : over_hom (P:=P.1) u L.Y Y  :=
      use t
      constructor
      · simp
        calc
        _ = L.φ.1 ≫ (f.inv ≫ f.hom).1 := by  apply (_≫=· ) ; rfl
        _ = L.φ.1 ≫ FiberToTotalSpace.map (𝟙 X) := by rw[f.inv_hom_id] ; rfl
        _ = L.φ.1 := by rw [Functor.map_id ] ; aesop


      · intro t' ht'
        apply Subtype.ext

        trans L.φ.1 ≫ f.inv.1
        · apply (Iso.eq_comp_inv (FiberToTotalSpace.mapIso f)).2
          exact ht'
        · {
            symm
            simp
          }




def cartLiftToCartMor {P : fibration B } {J I : B} {u : J ⟶ I} {X : obj_over (P:=P.1.hom) I}
  (L : cartesianLiftOfAlong X u) :  isCartesianMorphism P.1 L.φ.1 := fun v' K ↦ by
    let X' : obj_over (P.1.hom.obj X.1) := ⟨ X.1 , rfl⟩
    let L' : liftOfAlong X' (P.1.hom.map L.φ.1) := morphismToLift L.φ.1
    let Y' : obj_over (P.1.hom.obj L.Y.1):= L'.Y -- ⟨ L.Y.1 , rfl⟩
    let Y := L.Y
    let v : _ ⟶ J:=v' ≫ eqToHom Y.2
    let u' := u ≫ eqToHom (symm X.2)
    have trick : v' ≫ P.1.hom.map L.φ.1 = v ≫ u' := by
      rw [Category.assoc] ;
      apply (_≫=·) ;
      have goal := eq_whisker L.φ.2 (eqToHom (symm X.2))
      rw [← Category.assoc , ←goal ]
      rw [Category.assoc , eqToHom_trans , eqToHom_refl]
      sorry --aesop

    have trick : (v' ≫ P.1.hom.map L.φ.1) ≫eqToHom X.2 = v ≫ u := by rw [trick] ; sorry
    -- let iX : over_hom ()
    let μ : over_hom (v ≫ u) K.1 X := over_comp trick (⟨ 𝟙 _ , by sorry⟩ ) (K.φ)

    obtain ⟨ψ , hψ⟩   :=  L.2 _ ⟨  _ , μ⟩
    have p : (v' ≫ eqToHom Y.2) ≫ eqToHom (Y.2.symm) = v' := by calc
      _ = v' ≫ _ := by rw [Category.assoc]
      v' ≫ _ = v' ≫ (𝟙 _) := by apply (_≫= · ) ; rw [eqToHom_trans , eqToHom_refl]
      _ = v' := by rw [Category.comp_id v' ]

    let ψ' : over_hom v' K.Y Y' := over_comp p (⟨ 𝟙 _ , by sorry⟩ ) ψ
    use ψ'
    constructor
    -- rw [over_comp_coe]
    sorry
    sorry
lemma verticalIsosAreCart {P : fibration B} {X Y : P [I]} (f : Y ≅ X) : isCartesianMorphism P.1 (f.hom.1) := cartLiftToCartMor ⟨ _ , verticalIsosAreCart' f⟩
lemma isVertical_symm {P : Over B} {X X' : obj_over (P:=P.hom) I} (α : X.1 ≅ X'.1) (isVert : isVertical α.hom ) : isVertical α.inv := by
  unfold isVertical ; symm ;
  rw [(_ : α.inv = inv α.hom) , Functor.map_inv P.hom, (_ : inv (P.hom.map α.hom) = (P.hom.mapIso α).inv)] ;
  apply (Iso.eq_inv_comp (P.hom.mapIso α)).2 ; --  := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
  rw [← isVert]
  apply (· =≫_)
  rfl
  unfold Functor.mapIso
  simp
  rw [← Functor.map_inv P.hom α.hom ]
  apply congrArg P.hom.map
  aesop
  aesop



def CartTrafoOfComp {P Q : fibration B} {F G : P ⟶ Q} (η : F.1.left ≅ G.1.left) (ηhomIsVertical : ∀ {A : B} (T : obj_over (P :=P.1.hom) A) ,
  isVertical (X:=(F / A).obj T) (X':=(G / A).obj T) (rewrittenTrafo η.hom T)) : F ≅ G where
    hom := ⟨ η.hom , ηhomIsVertical⟩
    inv := by
      use η.inv
      intro A T
      exact isVertical_symm (X:=(F / A).obj T) (X':=(G / A).obj T)
        (Iso.mk (rewrittenTrafo η.hom T) (rewrittenTrafo η.inv T)) (ηhomIsVertical T)
    hom_inv_id := by apply Subtype.ext ; exact η.hom_inv_id
    inv_hom_id := by apply Subtype.ext ; exact η.inv_hom_id
lemma verticalIsosAreCart'' {P : fibration B} {X Y : P [I]} (f : Y.1 ≅ X.1) (hf :isVertical f.hom) : isCartesianMorphism P.1 f.hom := by
  let g : Y ≅ X := Iso.mk (⟨ f.hom , hf⟩ : Y ⟶ X) (⟨ f.inv , isVertical_symm f hf⟩ : X ⟶ Y) (by apply Subtype.ext ; apply Iso.hom_inv_id) (by apply Subtype.ext ; aesop)
  have this : isCartesianMorphism P.1 g.hom.1 := verticalIsosAreCart (I:=I) (P:=P) g
  have goal : f.hom = g.hom.1  := by rfl
  rw [goal]
  assumption

@[simp] noncomputable def cartesianLiftFromFibration (P : fibration B) {J I} (u : J ⟶ I) (X : P[I]) : cartesianLiftOfAlong X u := ⟨(P.2 u X).choose , (P.2 u X).choose_spec⟩
def morphismToLift' {P : Over B} {J : B} {Y : obj_over J} {X: P.left} (φ : Y.1 ⟶ X) : liftOfAlong ⟨ X , rfl⟩  (eqToHom Y.2.symm ≫ P.hom.map φ) where
  Y := Y
  φ := by use φ; simp


def cartesianMorphismToCartLift' {P : Over B }{ X Y : P.1}  {φ : Y ⟶ X} (hφ : isCartesianMorphism  P φ) :
  cartesianLiftOfAlong ⟨ X , rfl⟩  (P.hom.map φ ) where
  Y := ⟨ Y , rfl⟩
  φ := ⟨ φ  , by aesop⟩
  isCart := by sorry --apply compPresCartesian -- sorry --hφ
def cartesianMorphismToCartLift {P : Over B} {J : B} (Y : obj_over I) {φ : Y.1 ⟶ X} (hφ : isCartesianMorphism  P φ) : cartesianLiftOfAlong ⟨ X , rfl⟩ (eqToHom Y.2.symm ≫ P.hom.map φ) where
  Y := Y
  φ := ⟨ φ , by aesop⟩
  isCart := by sorry


lemma eq_whisker_eq {C : Cat} {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (p : f = f') ( q : g = g') : f ≫ g = f' ≫ g' := by
  rw [p]
  rw [q]
lemma mapIso_preimageIso {C D : Cat} (F : C ⥤ D) [Full F] [Faithful F] {X Y : C} (f : F.obj X ≅ F.obj Y) : F.mapIso (F.preimageIso f) = f := by aesop
theorem FullyFaithfullCartFunctorReflectsCartMorph ( full :  Full F.1.left) (faithful : Faithful F.1.left) :
  (∀ (Y X : P.1.left) (f : Y ⟶X) (hf : isCartesianMorphism Q.1 (F.1.left.map f)) , isCartesianMorphism P.1 f) := fun Y X f hf ↦ by
    let F':= F.1.left
    let u := P.1.hom.map f
    let Xf : obj_over (P:=P.1.hom) _ := ⟨ X , rfl⟩

    let u' := u ≫ eqToHom ((comm F))
    let L' : cartesianLiftOfAlong ⟨X , rfl⟩ u := cartesianLiftFromFibration P (P.1.hom.map f) ⟨X , rfl⟩

    let hFf: isCartesianMorphism Q.1 (F'.map L'.φ.1) := F.2 L'.φ.1 (cartLiftToCartMor L') --

    --let hFf : isCartesianMorphism Q.1 (F'.map f) := F.2 f (cartLiftToCartMor L') --

    let cartLift : cartesianLiftOfAlong (P:=Q.1.hom) ⟨ F'.obj X , rfl⟩   (Q.1.hom.map (F'.map L'.φ.1) )  :=
        cartesianMorphismToCartLift' (P:=Q.1) hFf

    have EqObj : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj L'.Y.1) :=comm F ▸ (symm L'.Y.2).trans (comm F)
    let ident :=  eqToHom (EqObj)
    have eqMor : Q.1.hom.map (F'.map f) = ident ≫ Q.1.hom.map (F'.map L'.φ.1) := by sorry
    let cartComparMap : cartesianLiftOfAlong (P:=Q.1.hom) cartLift.Y  ident := cartesianLiftFromFibration Q  _ _
    let cartCompos : cartesianLiftOfAlong ⟨F'.obj X , rfl⟩ (Q.1.hom.map (F'.map f)) := by
      exact ⟨ _ , compPresCartesian' (P:=Q.1) cartLift cartComparMap (eqMor.symm) ⟩

    let fAsLift : cartesianLiftOfAlong ⟨F'.obj X , rfl⟩ (Q.1.hom.map (F'.map f)) := cartesianMorphismToCartLift' hf
    obtain ⟨ α , hα ⟩  := cartesianLiftIsUnique cartCompos fAsLift
    --let preα
    /-
    have αisCart : isCartesianMorphism Q.1 α.hom.1 := by apply verticalIsosAreCart (P:=Q)
    have hα : α.hom.1 ≫ cartCompos.φ.1 = fAsLift.φ.1 := hα.1
    -/
    have this : cartCompos.Y.1 = F'.obj L'.Y := by
        trans cartComparMap.Y.1
        · rfl
        ·
    let myIso : Y ≅ L'.Y := by
      apply Functor.preimageIso F' ;
      exact  (FiberToTotalSpace.mapIso α).trans (eqToIso this)
    have hmyIso: F'.map myIso.hom = α.hom.1 ≫ eqToHom this := by calc
      F'.map myIso.hom = (F'.mapIso myIso).hom := by rw [← F'.mapIso_hom]
      _ = ((FiberToTotalSpace.mapIso α).trans (eqToIso this)).hom := by congr ; apply mapIso_preimageIso F'
      _ = FiberToTotalSpace.map α.hom ≫ eqToHom this := by rfl



    have : isCartesianMorphism P.1 myIso.hom := by sorry
    have hf : f = myIso.hom ≫ L'.φ.1 := by
      apply F'.map_injective ;
      rw [Functor.map_comp] ;
      trans fAsLift.φ.1
      · rfl
      · rw [← hα.1] ;
        apply eq_whisker_eq hmyIso
        sorry

    rw [hf]
    apply compCartesianMorphisms
    exact this
    exact cartLiftToCartMor L'


    /-



    Remark
    The problem why this is very difficult for me is the following: I have to cartesianLifts along maps which coincide up to an identification of the source.
    Hence I cant directly apply that cartesianLiftsAre unique to conclude, that the two lifts coincide up to canonical isomorphism in the source.
    So I have to composewith a cartesian lift along the identification. But now its hard to deduce the isomorphism between the correct sources.
    And even after that, we will have to show that isomorphism are cartesian to conclude.

      -/
