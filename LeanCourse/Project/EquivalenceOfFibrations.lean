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


variable {P Q : fibration B}{F : P ⟶ Q}
--notation (priority := high) P "[" A "]" => obj_over (P:=P.1.hom) A
instance FiberToTotalSpace {P : fibration B} {I : B} : P [ I ] ⥤ P.1.left where
  obj := fun X ↦ X.1
  map := fun f ↦ f.1
lemma comm {P Q : fibration B} (F : P ⟶ Q ) : ∀ {A} , P.1.hom.obj A =  Q.1.hom.obj (F.1.left.obj A) :=  fun {A} ↦ by rw [← Functor.comp_obj , ← Over.w F.1] ; apply Functor.congr_obj ; rfl
def over_hom_comp {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {X : P[I]} {Y:P[J]}{Z:P[K]} (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom (v ≫ u) Z X := (transLift ⟨ _ , φ ⟩ ⟨_ , ψ⟩ ).φ
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

def cartesianMorphismToCartLift (P : Over B ) {I : B} {X : obj_over (P:=P.hom) I} { Y : P.1}  {φ : Y ⟶ X.1} (hφ : isCartesianMorphism  P φ) : cartesianLiftOfAlong X (P.hom.map φ ≫ eqToHom X.2) where
  Y := ⟨ Y , rfl⟩
  φ := ⟨ φ  , by aesop⟩
  isCart := by sorry --apply compPresCartesian -- sorry --hφ
def weakCartMorphism {P : Over B} {X Y : P.left} (φ: Y ⟶ X) :=
  ∀ {Y' : obj_over (P:=P.hom) (P.hom.obj Y)} (f : over_hom (P.hom.map φ) Y' ⟨ X , rfl⟩ )  ,
  ∃! f' : Y' ⟶ ⟨ Y , rfl⟩  , f'.1 ≫ φ =f.1


 theorem postCompCartesianMorphism {P : fibration B} { Y Z : P.1.left} {φ: Y ⟶ Z } (hφ:  isCartesianMorphism P.1 φ)  : Function.Bijective (fun (f : Y ⟶ Y) ↦ f ≫ φ):= by sorry
--lemma cartLiftVsCartMorph (P : fibration B) { I : B} {X :  P [ I ]}{Y : P.1.left} (φ: Y ⟶ X.1) : isCartesianMorphism φ ↔ isCartesian ()
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
      have goal : weakCartMorphism (P:=Q.1) (F'.map φ.1) := by sorry
      have p : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj Y'.1) := by
        calc
              _ = P.1.hom.obj Y' := symm (Y'.2)
             _ = _ := comm F
      let Fφ1 : over_hom u ((F / J).obj  Y') ((F / I).obj Xf) := mappingOverHom F (u:=u) φ
      let helpMorp : over_hom (eqToHom (symm p)) (⟨ F'.obj Y , p⟩ ) Y' := by sorry

      let Fφ : over_hom (P:=Q.1.hom) (((Q.1).hom.map (F'.map φ.1))) ⟨ F'.obj Y , p ⟩ ⟨ F'.obj X , rfl⟩  := by
        use f

/-
      obtain ⟨ g     , hg⟩  := goal (Y':=⟨ F'.obj Y , p ⟩ ) Fφ

      let J' := Q.1.hom.obj (F'.obj Y'.1)
      let Y1 : obj_over J' := ⟨ Y  , (comm F).trans p⟩
      let Y1' : obj_over (P:=P.1.hom) J' := ⟨ Y'.1 , comm F⟩
      have p1 : (F / J').obj  Y1 = ⟨ F'.obj Y ,p⟩ := rfl
      have p2 : (F / J').obj Y1'  = ⟨F'.obj Y'.1 , rfl⟩ := rfl

      let pre_g  : Y1 ⟶ Y1' := (Equivalence.fullOfEquivalence (F / J')).preimage (eqToHom p1 ≫ g ≫ eqToHom (symm p2))  --: Yf ⟶ Y'
      let pre_gh : F.1.left.map pre_g.1 = (eqToHom p1).1 ≫ g.1 ≫ (eqToHom (symm p2)).1 := by calc
        F.1.left.map pre_g.1
          = ((F / J').map pre_g).1 := rfl
        _ = (eqToHom p1 ≫ g ≫ eqToHom (symm p2)).1 := by rw [(Equivalence.fullOfEquivalence (F / J')).witness (eqToHom p1 ≫ g ≫ eqToHom (symm p2)) ]
        _ = _ := by aesop
      let pre_f : Y ⟶ X := pre_g.1 ≫ φ.1
      use pre_f
      rw [Functor.map_comp]
      rw [pre_gh]
      let hg : g.1 ≫ F'.map φ.1 = f := hg.left
      rw [← hg]
      symm
      trans (g.1 ≫ F.1.left.map φ.1)
      · rfl
      · exact eq_whisker (by rw [eqToHom_refl] ; aesop) (F.1.left.map φ.1)




      --let L : cartesianLiftOfAlong ((F / _).obj ⟨ X , rfl⟩) u := (cartesianMorphismToCartLift Q.1 (F.2 φ.1 (by sorry))) --⟨ ⟨  _ , mappingOverHom F u φ⟩  , F.2 (by sorry)⟩
      /-
      have weakCart : isWeakCartesian ⟨ _ , mappingOverHom F φ⟩  := by
        exact weakCartifCartesian L
      let m : ⟨ Y , comm F⟩  ⟶ Y' := by
        let ψ:=  (weakCart ⟨ ⟨ F'.obj Y , by aesop⟩   , by sorry ⟩).choose --obtain ⟨ m' , hm'⟩
        let hψ :=(weakCart ⟨ ⟨ F'.obj Y , by aesop⟩   , by sorry ⟩).choose_spec --obtain ⟨ m' , hm'⟩
/-
theorem equivalenceOfFibrationsCheckOnFibers : (∀ (I : B) ,  IsEquivalence (F / I) ) → IsEquivalence F.1.left := fun ass ↦ by
  let F' := F.1.left
  have essSurj : EssSurj F' :=  by
    constructor
    intro q
    let I := Q.1.hom.obj q
    -- specialize ass I
    obtain ⟨ p , ⟨ hp ⟩ ⟩  := (Equivalence.essSurj_of_equivalence (F / I)).mem_essImage ⟨ q , rfl⟩
    use p.1
    constructor
    apply FiberToTotalSpace.mapIso hp
  have fullyFaithfull : ∀ Y X : P.1.left , Function.Bijective (F'.map : (Y ⟶ X) → (F'.obj Y ⟶ F'.obj X))   := fun Y X ↦ by
    constructor
    · sorry
    · Fullness ass
  have full : Full F' := by sorry
  have faithfull : Faithful F' := by sorry

  apply Equivalence.ofFullyFaithfullyEssSurj
-/
