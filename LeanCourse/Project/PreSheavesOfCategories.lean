import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
import Mathlib.CategoryTheory.EqToHom

set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 1500000
set_option quotPrecheck false
open Opposite
open Iso

universe v₁ u₁ t₁ s₁  --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].



namespace FiberedCategories
--attribute[ext] Functor




variable {B : Cat.{v₁ , u₁}} {I J K : B}
noncomputable def presheafOfCategories_obj (F : splitFibration B) : Bᵒᵖ  ⥤ Cat where
  obj := fun I ↦ F ↓ I.unop
  map := fun u ↦ reindexing (Quiver.Hom.unop u)
  map_comp := fun {K J I} v u ↦ by sorry
  map_id := fun I ↦ by simp ; sorry
notation F "$" => presheafOfCategories_obj F
@[simp] noncomputable def re {F : splitFibration B} (u : J ⟶ I) : F ↓ I ⟶ F ↓ J := reindexing u
def fibb {F G : splitFibration B} (α : F ⥤cs G) (I : B) : F ↓ I ⟶ G ↓ I := (α.1) / I
scoped notation:70 α " / " I => fibb α I
noncomputable def appNat{F G : splitFibration B} {α : F ⥤cs G} {u : J ⟶ I} (X : F ↓ I) :
  ((α / I) ≫ re u).obj X ≅ (re u ≫ (α / J)).obj X := eqToIso (Subtype.ext (α.2 u X).choose)

instance  {F G : splitFibration B}  : CoeOut (F ⥤cs G) (F.1.1.1 ⥤ G.1.1.1) where
  coe := fun α ↦  α.1.1.1
notation α "%"  => α.1.1.1
def m {F G : splitFibration B} (α : F ⥤cs G) (I : B) {X Y : F ↓ I } (f : X ⟶ Y) := ((α / I).map f).1
-- @[simp] lemma si {P : splitFibration B} {X : P.1.1.1} : forget.obj X = X.1 := rfl
-- def test {Y : (F ↓ I )}
--variable {Y : F ↓ I }
--#check CategoryTheory.Functor.mapIso forget (appNat Y)
noncomputable def undAppNat {F G : splitFibration B} {α : F ⥤cs G} {u : J ⟶ I} (X : F ↓ I) :
  (((α / I) ≫ re u).obj X).1 ≅ ((re u ≫ (α / J)).obj X).1 := CategoryTheory.Functor.mapIso forget (appNat X)


lemma appNatInvIsEq{F G : splitFibration B} {α : F ⥤cs G} {u : J ⟶ I} (X : F ↓ I) :
  isIdentity (𝕏:=(G ↓ J) ) (Y:=((α / I) ≫ re u).obj X) ((appNat X).inv) := by use symm (Subtype.ext (α.2 u X).choose) ; rfl


lemma natHelper {F G : splitFibration B} (α : F ⥤cs G) (u : J ⟶ I)
{X Y: ↑(F ↓ I)}
 (f : X ⟶ Y)
 : ((appNat X).hom ≫ (α / J).map ((re u).map f) ≫ (appNat Y).inv).1 ≫ Cart u ((α / I).obj Y) =
   Cart u ((α / I).obj X) ≫ ((α / I).map f).1 := by
      have obs3' : ∀ {Z : ↑(F ↓ I) } ,  (appNat Z).hom.1 = eqToHom ((α.2 u Z).choose) := fun {Z} ↦ by
        rw [appNat , eqToIso.hom] ;
        trans FiberToTotalSpace.map ((appNat Z).hom) ;
        ·  rfl ;
        · unfold appNat; rw [eqToIso.hom , eqToHom_map FiberToTotalSpace]
      have obs1 : (appNat Y).inv.1 ≫ (Cart u ((α / I).obj Y)) = (α%).map (Cart u Y)  := by
        let myiso : (((α / I) ≫ re u).obj Y ).1 ≅ ((re u ≫ (α / J)).obj Y ).1 := undAppNat Y
        have myIsoInv : myiso.inv = (appNat Y).inv.1 := rfl
        have this : myiso.hom = (appNat Y).hom.1 := rfl
        rw [← myIsoInv]
        apply (inv_comp_eq myiso).2
        symm
        rw [this, obs3' (Z:=Y)]
        exact (α.2 u Y).choose_spec
      have orig : CommSq ((re u).map f).1 (Cart u X) (Cart u Y) f.1 := ⟨ (u ⋆ f).choose_spec.1 ⟩
      have obs2 : m α  J ((re u).map f) ≫ (α %).map (Cart u Y) = (α %).map (Cart u X) ≫ m α I f  :=
         (CategoryTheory.Functor.map_commSq (α %) orig).w

      have obs3 : (appNat X).hom.1 ≫  (α %).map (Cart u X) = Cart u ((α / I).obj X) := by rw [eq_whisker obs3' _] ; exact (α.2 u X).choose_spec
      calc
            ((appNat X).hom ≫ (α / J).map ((re u).map f)       ≫ (appNat Y).inv).1 ≫ Cart u ((α / I).obj Y)
          = FiberToTotalSpace.map ((appNat X).hom ≫ (α / J).map ((re u).map f)       ≫ (appNat Y).inv) ≫ Cart u ((α / I).obj Y) := rfl
        _ = (FiberToTotalSpace.map (appNat X).hom ≫ FiberToTotalSpace.map ((α / J).map ((re u).map f))       ≫ FiberToTotalSpace.map ((appNat Y).inv)) ≫ Cart u ((α / I).obj Y) := by apply (· =≫ Cart u ((α / I).obj Y)  ) ; rw [← FiberToTotalSpace.map_comp,← FiberToTotalSpace.map_comp ]
        _ = FiberToTotalSpace.map (appNat X).hom ≫ FiberToTotalSpace.map ((α / J).map ((re u).map f))       ≫ FiberToTotalSpace.map ((appNat Y).inv) ≫ Cart u ((α / I).obj Y) := by rw [Category.assoc] ; apply (_≫=·) ; rw [Category.assoc]
        _ = ((appNat X).hom.1 ≫ m α J ((re u).map f) ≫ (appNat Y).inv.1) ≫ Cart u ((α / I).obj Y)   := by unfold m ; aesop
        _ = (((appNat X).hom.1 ≫ m α J ((re u).map f)) ≫ (appNat Y).inv.1) ≫ Cart u ((α / I).obj Y)   := by apply (· =≫ _) ; rw [← Category.assoc]
        _ = ((appNat X).hom.1 ≫ m α J ((re u).map f)) ≫ (appNat Y).inv.1 ≫ Cart u ((α / I).obj Y)   := by rw [Category.assoc]
        _ = ((appNat X).hom.1 ≫ m α J ((re u).map f)) ≫ (α%).map (Cart u Y)               := whisker_eq _ obs1
        _ = (appNat X).hom.1 ≫  m α J ((re u).map f) ≫ (α%).map (Cart u Y)                  := by rw [Category.assoc]
        _ = (appNat X).hom.1 ≫ (α %).map (Cart u X) ≫ m α I f                               := whisker_eq _ obs2
        _ = ((appNat X).hom.1 ≫ (α %).map (Cart u X)) ≫ m α I f                               :=  by rw [← Category.assoc]
        _ = Cart u ((α / I).obj X) ≫ m α I f                                               :=  (eq_whisker obs3 (m α I f))
        _ = Cart u ((α / I).obj X) ≫ ((α / I).map f).1 := rfl

noncomputable def Naturality {F G : splitFibration B} (α : F ⥤cs G) (u : J ⟶ I) :
  (α / I) ≫ re u  ≅ re u ≫ (α / J) :=
    NatIso.ofComponents appNat
    (by
      intro X Y f
      apply (Iso.eq_comp_inv (appNat Y)).1
      let αf := (α / I).map f
      symm
      apply (u ⋆ αf ).choose_spec.2
      simp
      exact natHelper α u f)



def presheafOfCategories_map {F G : splitFibration B} (α : F ⥤cs G) :  F $ ⟶ G $ where
  app := fun I ↦ α.1 / Opposite.unop I

  naturality := fun {I J} u ↦ extFunctor (Naturality α u.unop).inv (by
      intro X
      have this : (appNat X).inv = ((Naturality α u.unop).inv.app X) := by aesop
      rw [← this]
      exact appNatInvIsEq X
    )



    -- let η : F$.map u ≫ ((α.1) / _ ) ≅ ((α.1)/ I.unop) ≫G$.map u := by sorry

 --{s₁ t₁} --.{max s₁ v₁ , max t₁ u₁}
/- def PSh : Cat ᵒᵖ ⥤ Cat where
  obj := fun B ↦ PShCat (unop B)
  map := sorry
  map_id := sorry
  map_comp := sorry
-- instance : Category (PSh B)  := Functor.category (C:= B ᵒᵖ) (D:= Cat)
-/
noncomputable def presheafOfCategories : splitFibration B ⥤ PShCat B  where
  obj := presheafOfCategories_obj
  map := presheafOfCategories_map
