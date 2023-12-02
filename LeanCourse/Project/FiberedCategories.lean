
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Over
set_option autoImplicit true

namespace CategoryTheory

open Opposite

universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].
variable {𝕏 : Type u₁} {B : Type u₁} [Category.{v₁} B] [Category.{v₁} 𝕏] {P : 𝕏 ⥤ B}
namespace FiberedCategories

def comp {X Y Z : B}  : (X ⟶ Y) → (Y ⟶ Z ) → (X ⟶ Z) := fun f g => f ≫ g

def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := f ≫ CategoryTheory.eqToHom h -- by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := CategoryTheory.eqToHom h ≫ f -- by rw [h]  ; exact f




def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
instance : CoeOut (obj_over (P:=P) A) 𝕏 := ⟨fun α ↦ α.1⟩
def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') :=
  {α : X.1 ⟶ X' //
   P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2 ≫ u }


instance : Category (obj_over ( P:= P) A) where
  Hom ( X X' : obj_over A) := over_hom (𝟙 A) X X' -- { α : verticalOver A // α.X = X ∧ α.X' = X' }
  id (X : obj_over A) := ⟨ 𝟙 X.1 , by
    rw [@Functor.map_id]
    aesop_cat
    ⟩
  comp {X} {Y} {Z} f g := ⟨  f.1 ≫ g.1 , by
    rw [@Functor.map_comp]
    rw [Category.assoc]
    rw [g.2]
    rw [← Category.assoc]
    rw [f.2]
    aesop_cat
     ⟩
     --check axioms

structure liftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I)  where
  Y : obj_over (P:=P) J
  φ : over_hom u Y X
instance : CoeDep (liftOfAlong (P:=P) X u) L (L.Y.1 ⟶ X) where
  coe := L.φ.1
variable {J I : B} {u : J ⟶ I}

def morphismToLift {X Y : 𝕏} (φ : Y ⟶ X) : liftOfAlong ⟨ X , rfl⟩  (P.map φ) where
  Y := ⟨ Y , rfl⟩
  φ := by use φ; simp



def isCartesian  {X : obj_over (P:=P) I} (τ: liftOfAlong X u):=
  ∀ {K : B} (v : K ⟶ J) (L: liftOfAlong X (v ≫u )) ,
    ∃! ψ : over_hom v L.Y τ.Y , ψ.1 ≫ τ.φ.1 = L

def isWeakCartesian {X : obj_over (P:=P) I} (τ: liftOfAlong X u):= ∀ (L : liftOfAlong X u) ,
  ∃! ψ : L.Y ⟶ τ.Y , ψ.1 ≫ τ.φ.1 = L


structure cartesianLiftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I) extends liftOfAlong X u where
 isCart : isCartesian (P:=P) L

instance : CoeOut (cartesianLiftOfAlong (P:=P) A u) (liftOfAlong (P:=P) A u) := ⟨fun α ↦ α.1⟩

def transLift {K J I : B} {v : K ⟶ J } {u : J ⟶ I} {X : obj_over I}
  (α : liftOfAlong X u)
  (β : liftOfAlong (α.Y) v )
  : liftOfAlong ( P:=P) X (v ≫ u ) where
  Y := β.Y
  φ := ⟨ β.φ.1 ≫ α , by rw [@Functor.map_comp, Category.assoc , α.φ.2 , ← Category.assoc , β.φ.2] ; aesop_cat ⟩

def weakCartifCartesian {J I : B} {u : J ⟶ I} {X : obj_over (P:=P) I} (τ: cartesianLiftOfAlong X u) : isWeakCartesian τ.1 := by
  intro L
  --obtain ⟨ τ , isCart ⟩:= τ
  let τ' : liftOfAlong X (𝟙 J ≫ u) := transLift L (⟨ L.Y , 𝟙 (L.Y)  ⟩  )
  obtain ⟨ψ, hψ ⟩:= τ.isCart (𝟙 J) τ'
  have LeqPsiTau : ψ.1 ≫ τ.φ.1 = L.φ.1 := by
    rw [hψ.1]
    apply Category.id_comp
  -- have ρ : L.Y ⟶ τ'.Y := 𝟙 (L.Y)
  use ψ
  simp
  simp at hψ
  constructor
  exact LeqPsiTau
  intro ψ' hψ'
  apply hψ.2
  rw [← hψ.1, hψ' , ← LeqPsiTau]

theorem cartesianLiftIsUnique {J I : B} {u : J ⟶ I} {X : obj_over (P:=P) I} (L  L' : cartesianLiftOfAlong X u) :
  ∃! α : L'.1.Y ≅ L.1.Y , α.hom.1 ≫ L.1.φ.1 = L'.1.φ.1 := by
    obtain ⟨ α , hα  ⟩ := weakCartifCartesian (X:=X) L L'
    obtain ⟨ β , hβ  ⟩ := weakCartifCartesian (X:=X) L' L

    obtain ⟨ρ , hρ⟩ := weakCartifCartesian (X:=X) L' L'.1
    obtain ⟨ ⟨ Y , φ ⟩ , _⟩   := L
    obtain ⟨ ⟨ Z , ψ⟩ , _⟩  := L'
    simp at α
    simp at β
    simp at hβ
    simp at hα
    simp at hρ
    have this : (α ≫β  ).1 = α.1 ≫ β.1 := by rfl

    have abh : (α ≫ β).1 ≫ ψ.1 = ψ.1  := by rw [this , Category.assoc , hβ.1 , hα.1]
    have abh : α ≫β = 𝟙 _ := by
      let hρ := hρ.2
      trans ρ
      apply hρ
      exact abh
      symm
      apply hρ
      have this : (𝟙 _) ≫ ψ.1 = ψ.1 := by rw [Category.id_comp]
      exact this
    have bah : (β ≫α  ).1 ≫ φ.1 = φ.1  := by sorry
    have bah : β ≫ α= 𝟙 _ := by sorry

      -- trans ((𝟙 (L'.1).Y) ≫ (L'.1).φ )

    let myiso : Z ≅ Y  := ⟨ α , β , abh, bah ⟩

    -- have h : myiso.hom = α := by sorry
    use myiso
    constructor
    · simp
      exact hα.1
    · intro α'  hα'
      ext
      apply hα.2
      exact hα'
variable  {B : Cat.{v₁ , u₁}}



instance : CoeDep (Over B) F (F.1 ⥤ B) where
  coe := F.hom

def fibration (B : Cat.{v₁ , u₁}) := { P : Over B  //
  ∀ {J I : B} (u : J ⟶ I) (X : obj_over I) ,
    ∃ φ:  liftOfAlong (P:=P.hom) X u , isCartesian φ }


-- variable {𝕏 : Type u₂} {B : Type u₁} [Category.{v₁} B] [Category.{v₂} 𝕏] {P : 𝕏 ⥤ B}
instance : CoeOut (fibration B) (Over B) := ⟨ fun α ↦ α.1⟩

instance : CoeDep (fibration B) F (F.1.1 ⥤ B) where
  coe := F.1
def isCartesianMorphism (P : Over B ) {X Y : P.1}  (φ : Y ⟶ X) : Prop :=
  isCartesian (P:=P.hom) (morphismToLift φ)
def cartesianFunctor
  (P Q : fibration B) := {F : P.1 ⟶ Q.1 //
    ∀ {X Y : P.1.1} (φ : X ⟶ Y) (_ : isCartesianMorphism P.1 φ) ,
       isCartesianMorphism Q.1 (F.left.map φ)  }
scoped infixr:80 " ⥤c   " => cartesianFunctor -- type as \gg
instance {P Q : fibration B} : CoeOut (P ⥤c Q) (P.1.1 ⥤ Q.1.1) := ⟨fun α ↦ α.1.left⟩
def overFunctorPreservesFibers {P Q : fibration B} (F : P ⥤c Q) (A : B) :
  Functor (obj_over (P := P.1.hom) A) (obj_over (P := Q.1.hom) A) where
    obj := fun X ↦ by
      use (F : P.1.1 ⥤ Q.1.1).obj X.1
      trans (P.1.hom).obj X
      · let FQ : P.1.1 ⟶ B := F.1.1 ≫ Q.1.hom
        trans FQ.obj X.1 ; rfl ;
        have this : FQ = P.1.hom := F.1.3 ;
        rw [this]
      · exact X.2
    map := fun {X Y} (f : X ⟶ Y) ↦ by
      use (F.1.left).map f.1
      simp
      let FQ : P.1.1 ⟶ B := F.1.1 ≫ Q.1.hom
      have this : FQ = P.1.hom := F.1.3 ;
      trans (FQ.map f.1 ≫ eqToHom _)




    map_id := by sorry
    map_comp := by sorry



def cartesianNaturalTrafo {P Q : fibration B}
  (F G : P ⥤c Q)
  (η : undFuncMor F.1 ⟶ G) := ∀ {X : P.1.1} , η.app X


end FiberedCategories
