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


variable {P Q : fibration B}(F : P ⟶ Q)
lemma comm  : ∀ {A} , P.1.hom.obj A =  Q.1.hom.obj (F.1.left.obj A) :=  fun {A} ↦ by rw [← Functor.comp_obj , ← Over.w F.1] ; apply Functor.congr_obj ; rfl
@[simps] def over_hom_comp {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {X : P[I]} {Y:P[J]}{Z:P[K]}
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom (v ≫ u) Z X := (transLift ⟨ _ , φ ⟩ ⟨_ , ψ⟩ ).φ
@[simps] def over_comp    {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {w : K ⟶ I} {X : P[I]} {Y:P[J]}{Z:P[K]}
  (comm : v ≫ u = w)
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom w Z X
  := transport comm (over_hom_comp φ ψ)
-- lemma over_comp_coe


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

@[simp] noncomputable def cartesianLiftFromFibration (P : fibration B) {J I} (u : J ⟶ I) (X : P[I]) : cartesianLiftOfAlong X u := ⟨(P.2 u X).choose , (P.2 u X).choose_spec⟩
/-
def mappingOverHom {P Q : fibration B} (F : P ⟶ Q ) {J I} {u : J ⟶ I} {Y : P [J]} {X : P[I]} (φ : over_hom u Y X) :  over_hom u ((F / J).obj Y) ((F / I).obj X) := by
  use F.1.left.map φ.1
  let hφ := φ.2
  calc
      (Q.1).hom.map ((F.1).left.map φ.1) ≫ eqToHom (_ : Q.1.hom.obj ((F / I).obj X).1 = I)
    =  ((Q.1).hom.map ((F.1).left.map φ.1) ≫ eqToHom (symm (comm F))) ≫ eqToHom X.2 := by rw [Category.assoc] ; apply (_ ≫= · ) ; symm ; apply eqToHom_trans
  _ = (eqToHom (symm (comm F)) ≫ P.1.hom.map (φ.1)) ≫ eqToHom X.2 := by {
    have veryweird : (F.1.left ⋙ Q.1.hom).map φ.1 = (F.1.left ≫  Q.1.hom).map φ.1 := rfl
    apply (· =≫ _) ; rw [← Functor.comp_map , veryweird  ,  Functor.congr_hom (Over.w F.1) φ.1 , Category.assoc ,Category.assoc ,  eqToHom_trans , eqToHom_refl] ; aesop
  }
  _ = eqToHom (_) ≫ eqToHom (_) ≫ u := by rw [Category.assoc] ; apply (_≫= · ) ; apply φ.2
  _ = eqToHom (_ : (Q).1.hom.obj ((F / J).obj Y).1 = J) ≫ u := by rw [← Category.assoc] ; apply (· =≫ u) ; apply eqToHom_trans
  -- have this : u = Q.1.hom.map (F.1.left.map φ.1) := by sorry
  -/
/-
def cartesianMorphismToCartLift {P : Over B } {I : B} (X : obj_over (P:=P.hom) I) { Y : P.1}  {φ : Y ⟶ X.1} (hφ : isCartesianMorphism  P φ) :
  cartesianLiftOfAlong X (P.hom.map φ ≫ eqToHom X.2) where
  Y := ⟨ Y , rfl⟩
  φ := ⟨ φ  , by aesop⟩
  isCart := by sorry --apply compPresCartesian -- sorry --hφ
-/
--not necessary:
def cartesianMorphismToCartLift' {P : Over B }{ X Y : P.1}  {φ : Y ⟶ X} (hφ : isCartesianMorphism  P φ) :
  cartesianLiftOfAlong ⟨ X , rfl⟩  (P.hom.map φ ) where
  Y := ⟨ Y , rfl⟩
  φ := ⟨ φ  , by aesop⟩
  isCart := by sorry --apply compPresCartesian -- sorry --hφ

/-
def cartFunctorPresCartLifts {I : B} {X : obj_over (P:=P.1.hom) I} {u : J ⟶I } (L : cartesianLiftOfAlong X u) : cartesianLiftOfAlong ( (F / I).obj X) u := by
  let Fφ := mappingOverHom F L.φ
  let FXf :=  (F / I).obj X
  let Ff : isCartesianMorphism Q.1 (F.1.left.map L.φ.1) := F.2 L.φ.1 (cartLiftToCartMor L) --
  let FL' : cartesianLiftOfAlong (P:=Q.1.hom) FXf u  := by
      use ⟨ _ ,Fφ⟩
      let cartLift : cartesianLiftOfAlong _ (Q.1.hom.map  (F.1.left.map L.φ.1) ≫ eqToHom (_)) := cartesianMorphismToCartLift Q.1 Ff
      sorry
      --, by apply cartesianMorphismToCartLift ; sorry ⟩
  sorry
-/
@[simps] instance FiberToTotalSpace {P : Over B} {I : B} : obj_over (P:=P.hom) I ⥤ P.left where
  obj := fun X ↦ X.1
  map := fun f ↦ f.1
theorem FullyFaithfullCartFunctorReflectsCartMorph ( full :  Full F.1.left) (faithful : Faithful F.1.left) :
  (∀ (Y X : P.1.left) (f : Y ⟶X) (hf : isCartesianMorphism Q.1 (F.1.left.map f)) , isCartesianMorphism P.1 f) := fun Y X f hf ↦ by
    let F':= F.1.left
    let u := P.1.hom.map f
    let Xf : obj_over (P:=P.1.hom) _ := ⟨ X , rfl⟩

    let u' := u ≫ eqToHom ((comm F))
    let L' : cartesianLiftOfAlong ⟨X , rfl⟩ u := cartesianLiftFromFibration P (P.1.hom.map f) ⟨X , rfl⟩

    let hFf: isCartesianMorphism Q.1 (F'.map L'.φ.1) := F.2 L'.φ.1 (cartLiftToCartMor L') --

    --let hFf : isCartesianMorphism Q.1 (F'.map f) := F.2 f (cartLiftToCartMor L') --

    let cartLift : cartesianLiftOfAlong  ⟨ F'.obj X , rfl⟩   (Q.1.hom.map (F'.map L'.φ.1) )  :=
        cartesianMorphismToCartLift' hFf

    have EqObj : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj L'.Y.1) :=comm F ▸ (symm L'.Y.2).trans (comm F)
    let ident :=  eqToHom (EqObj)
    have eqMor : Q.1.hom.map (F'.map f) = ident ≫ Q.1.hom.map (F'.map L'.φ.1) := by sorry
    let cartComparMap : cartesianLiftOfAlong ⟨ F'.obj L'.Y.1 , rfl⟩  ident := cartesianLiftFromFibration Q  _ _
    let cartCompos : cartesianLiftOfAlong ⟨F'.obj X , rfl⟩ (Q.1.hom.map (F'.map f)) := by rw [eqMor] ; exact ⟨ _ , compPresCartesian cartLift cartComparMap ⟩

    let fAsLift : cartesianLiftOfAlong ⟨F'.obj X , rfl⟩ (Q.1.hom.map (F'.map f)) := cartesianMorphismToCartLift' hf
    obtain ⟨ α , hα ⟩  := cartesianLiftIsUnique cartCompos fAsLift
    sorry

    /-
    let myIso : Y ≅ L'.Y.1 := by
      apply Functor.preimageIso F' ;
      let iso := Functor.mapIso FiberToTotalSpace α ;
      have this : cartCompos.Y.1 = cartComparMap.Y.1 := by simp ;  --F'.obj L'.Y.1 :=




    The problem why this is very difficult for me is the following: I have to cartesianLifts along maps which coincide up to an identification of the source.
    Hence I cant directly apply that cartesianLiftsAre unique to conclude, that the two lifts coincide up to canonical isomorphism in the source.
    So I have to composewith a cartesian lift along the identification. But now its hard to deduce the isomorphism between the correct sources.
    And even after that, we will have to show that isomorphism are cartesian to conclude.

      -/
