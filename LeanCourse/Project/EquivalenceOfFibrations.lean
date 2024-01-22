import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.CartesianComposition
import LeanCourse.Project.CartesianFunctors
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
        sorry -- aesop
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
      · exact eq_whisker (by rw [eqToHom_refl, eqToHom_refl , FiberToTotalSpace.map_id , FiberToTotalSpace.map_id, Category.comp_id , Category.id_comp]) (F.1.left.map φ.1) -- aesop



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
