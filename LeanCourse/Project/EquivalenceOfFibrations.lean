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
@[simps] def over_hom_comp {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {X : P[I]} {Y:P[J]}{Z:P[K]}
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom (v ≫ u) Z X := (transLift ⟨ _ , φ ⟩ ⟨_ , ψ⟩ ).φ
@[simps] def over_comp    {K J I : B} {P : fibration B} {u : J ⟶I } {v : K ⟶J } {w : K ⟶ I} {X : P[I]} {Y:P[J]}{Z:P[K]}
  (comm : v ≫ u = w)
  (φ: over_hom u Y X) (ψ : over_hom v Z Y) : over_hom w Z X
  := transport comm (over_hom_comp φ ψ)
-- lemma over_comp_coe

/-
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
      aesop

    have trick : (v' ≫ P.1.hom.map L.φ.1) ≫eqToHom X.2 = v ≫ u := by rw [trick] ; aesop
    -- let iX : over_hom ()
    let μ : over_hom (v ≫ u) K.1 X := over_comp trick (⟨ 𝟙 _ , by aesop⟩ ) (K.φ)

    obtain ⟨ψ , hψ⟩   :=  L.2 _ ⟨  _ , μ⟩
    have p : (v' ≫ eqToHom Y.2) ≫ eqToHom (Y.2.symm) = v' := by aesop

    let ψ' : over_hom v' K.Y Y' := over_comp p (⟨ 𝟙 _ , by aesop⟩ ) ψ
    use ψ'
    constructor
    -- rw [over_comp_coe]

    sorry
-/

theorem Fullness {F : P ⟶ Q}: (∀ (I : B) ,  IsEquivalence (F / I) ) → (∀ Y X : P.1.left , Function.Surjective (F.1.left.map : (Y ⟶ X) → (F.1.left.obj Y ⟶ F.1.left.obj X))) := by
      sorry
      /-
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
      have pre_gh : F.1.left.map pre_g.1 = (eqToHom p1).1 ≫ g.1 ≫ (eqToHom (symm p2)).1 := by calc
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

  -/
/-
 have fullyFaithfull : ∀ Y X : P.1.left , Function.Bijective (F'.map : (Y ⟶ X) → (F'.obj Y ⟶ F'.obj X))   := fun Y X ↦ by
    constructor
    · sorry
    · exact
-/

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

  have full : Full F' := by
    constructor
    swap
    ·  intro X Y f ; exact (Fullness ass _ _ f).choose

    ·  intro X Y f ; exact (Fullness ass _ _ f).choose_spec
  have faithfull : Faithful F' := by sorry

  apply Equivalence.ofFullyFaithfullyEssSurj
