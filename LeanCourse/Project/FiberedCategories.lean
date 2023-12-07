
--import Mathlib.CategoryTheory.Functor.Currying
--import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 500000
universe v₁ u₁ --v₂ u₁ u₂
-- morphism levels before object levels. See note [CategoryTheory universes].
variable {𝕏 : Type u₁} {B : Type u₁} [Category.{v₁} B] [Category.{v₁} 𝕏] {P : 𝕏 ⥤ B}
namespace FiberedCategories


def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := f ≫ CategoryTheory.eqToHom h -- by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := CategoryTheory.eqToHom h ≫ f -- by rw [h]  ; exact f




def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
instance : CoeOut (obj_over (P:=P) A) 𝕏 := ⟨fun α ↦ α.1⟩
@[simp] def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') :=
  {α : X.1 ⟶ X' //
   P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2 ≫ u }

@[simp] def compPresVertical {X Y Z : obj_over (P:=P) A} (f : X.1 ⟶Y.1 ) (g : Y.1 ⟶ Z.1) (p : isVertical f) (q : isVertical g) :
  isVertical (f ≫ g ) := by
    rw [isVertical, @Functor.map_comp]
    rw [Category.assoc]
    rw [q]
    rw [p]
def idIsVertical (X : obj_over (P:=P) A) : isVertical (𝟙 X.1 ) := by simp

instance : Category (obj_over ( P:= P) A) where
  Hom ( X X' : obj_over A) := { α : X.1 ⟶ X'.1 // isVertical (X:=X) (X':=X') α } -- over_hom (𝟙 A) X X' -- { α : verticalOver A // α.X = X ∧ α.X' = X' }
  id (X : obj_over A) := ⟨ 𝟙 X.1 , idIsVertical _ ⟩
  comp {X} {Y} {Z} f g := ⟨  f.1 ≫ g.1 , compPresVertical f.1 g.1 f.2 g.2
     ⟩


     -- axioms are automatically checked :D
@[simp] lemma compInFib {X Y Z : obj_over (P:=P) A} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl
@[simp] lemma idInFib {X : obj_over (P:=P) A} : (𝟙 X : X ⟶ X).1 = 𝟙 X.1 := rfl
@[simp] def coerc { X X' : obj_over A} (f : over_hom (P:=P) (𝟙 A) X X') : X ⟶ X' := ⟨ f.1 , by rw [isVertical, f.2] ; aesop ⟩
@[simp] def coercBack {X X' : obj_over A} (f : X ⟶ X') : over_hom (P:=P) (𝟙 A) X X' := ⟨ f.1 , by rw [f.2] ; aesop⟩
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
  let τ' : liftOfAlong X (𝟙 J ≫ u) := transLift L (⟨ L.Y , by apply coercBack ; exact 𝟙 _  ⟩  )
  obtain ⟨ψ, hψ ⟩:= τ.isCart (𝟙 J) τ'
  have LeqPsiTau : ψ.1 ≫ τ.φ.1 = L.φ.1 := by
    rw [hψ.1]
    apply Category.id_comp
  -- have ρ : L.Y ⟶ τ'.Y := 𝟙 (L.Y)
  use (coerc ψ)
  simp
  simp at hψ
  constructor
  exact LeqPsiTau
  intro ψ' hψ'
  have this : coercBack ψ' = ψ := by
    apply hψ.2
    rw [← hψ.1 ]
    rw [coercBack]
    simp
    rw [hψ' , ← LeqPsiTau]
  apply Subtype.ext
  simp
  rw [← this]
  simp

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

    have h : myiso.hom = α := rfl

    use myiso
    constructor
    · simp
      exact hα.1
    · intro α'  hα'
      ext
      rw [h]
      --simp at hα'
      apply hα.2
      exact hα'
      --have goa := hα.2 hα'

variable  {B : Cat.{v₁ , u₁}}
@[ext , simp] lemma extFib {X Y : obj_over (P:=P) A } (f g : X ⟶ Y) (_ : f.1 = g.1) : f = g := by apply Subtype.ext ; assumption



instance : CoeDep (Over B) F (F.1 ⥤ B) where
  coe := F.hom

def fibration (B : Cat.{v₁ , u₁}) := { P : Over B  //
  ∀ {J I : B} (u : J ⟶ I) (X : obj_over I) ,
    ∃ φ:  liftOfAlong (P:=P.hom) X u , isCartesian φ }

def cartesianLift {P : Over B} {J I : B} (u : J ⟶ I) (X : obj_over (P:=P.hom) I) := { φ  : liftOfAlong (P:=P.hom) X u // isCartesian φ }
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

scoped infixr:80 " ⥤c   " => cartesianFunctor
@[ext] lemma extCartFunctor {P Q : fibration B} (F G : P ⥤c Q) (p : F.1 = G.1) : F = G := Subtype.ext p
instance {P Q : fibration B} : CoeOut (P ⥤c Q) (P.1.1 ⥤ Q.1.1) := ⟨fun α ↦ α.1.left⟩
def objMappingBetweenFibers {P Q : fibration B} (F : P ⥤c Q) (A : B) : obj_over (P:=P.1.hom) A → obj_over (P:=Q.1.hom) A := by
  intro X
  use (F : P.1.1 ⥤ Q.1.1).obj X.1

  trans (F.1.1 ≫ Q.1.hom).obj X.1 ; rfl ;
  have this : F.1.1 ≫ Q.1.hom = P.1.hom := F.1.3 ;
  rw [this]
  exact X.2

variable {P Q : fibration B} {F G : P ⥤c Q}
def isIdentity  {𝕏 : Type u₁} [Category.{v₁} 𝕏] {X Y : 𝕏} (f : X ⟶ Y) : Prop := ∃ (p : X = Y) , f = eqToHom p
def isDiscrete (P : fibration B) := ∀ {A : B} {X Y : obj_over (P:=P.1.hom) A} (f : X ⟶ Y) , isIdentity f.1
def toFunctorOnFibers (F : P ⥤c Q) (A : B) :
  Functor (obj_over (P := P.1.hom) A) (obj_over (P := Q.1.hom) A) where
    obj := objMappingBetweenFibers F A

    map := fun {X Y} (f : X ⟶ Y) ↦ by
      use (F.1.left).map f.1
      simp
      let FQ : P.1.1 ⟶ B := F.1.1 ≫ Q.1.hom
      have this : FQ = P.1.hom := F.1.3 ;
      have myEq : (F.1.1 ≫ Q.1.hom).obj Y.1 = A := (objMappingBetweenFibers F A Y).2
      trans (FQ.map f.1 ≫ eqToHom myEq)
      rfl
      let myEq1 (Z : obj_over (P:=P) A) : FQ.obj Z.1 = P.1.hom.obj Z.1 := by rw [this]
      have myNat : FQ ⟶ P.1.hom := eqToHom F.1.3
      have this {Y : obj_over A} : eqToHom (myEq1 Y) = myNat.app Y.1 := by sorry
      have EqEq : myEq = _root_.trans (myEq1 Y) Y.2 := rfl
      have EqHom : eqToHom myEq = eqToHom (myEq1 Y) ≫ eqToHom Y.2 := by rw [EqEq] ; rw [eqToHom_trans]
      rw [EqHom, ← Category.assoc , this ,  myNat.naturality , Category.assoc , f.2 ]
      rw [← this  , eqToHom_trans]
    map_id := by sorry
    map_comp := by sorry

scoped infixr:80 " / " => toFunctorOnFibers

@[simp] lemma check {A : B} (F : P ⥤c Q) (X : obj_over A) : ((F / A).obj X).1 = F.1.left.obj X.1 := rfl


@[simp] def rewrittenTrafo (η : F.1.left ⟶G ) {A : B} (T : obj_over (P:=P.1.hom) A) : ↑((F / A).obj T).1 ⟶ ↑((G / A).obj T).1 :=
 eqToHom (symm $ check F T)  ≫  (η.app T.1) ≫  eqToHom (check G _)
-- def
/- def whiskerRewrittenTrafo (η : F.1.left ⟶G ) {A : B} (T : obj_over (P:=P.1.hom) A) : (P.1 ⟶ P.1) :=
  (by sorry) ≫ whiskerLeft Q.1 η ≫ (by sorry)
 def rewTrafoDef  (η : F.1.left ⟶G ) {A : B} (T : obj_over (P:=P.1.hom) A) : eqToHom (check F T) ≫rewrittenTrafo η T =  (η.app T.1) ≫  eqToHom (check G _) := by rw [rewrittenTrafo] ; aesop
 -/
def cartesianNatTrans {P Q : fibration B}
  (F G : P ⥤c Q)
  := { η : F.1.left ⟶ G // ∀ {A : B} (T : obj_over (P :=P.1.hom) A) ,
  isVertical (X:=(F / A).obj T) (X':=(G / A).obj T) (rewrittenTrafo η T) }

scoped infixr:80 " =>c " => cartesianNatTrans
@[simp] def cartesianIdTrans : (F : P ⥤c Q) →  F =>c F := fun F ↦ ⟨  𝟙 F.1.1 , fun {A} T ↦by
  have this : rewrittenTrafo (𝟙 F.1.1) T = 𝟙 ((F / A).obj T).1 := by simp ; aesop
  rw [this]
  exact idIsVertical _
   ⟩
  --def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
  @[simp] def compCartTrans {F G H: P ⥤c Q} (η: F =>c G) (ε : G =>c H) : F =>c H := ⟨
     η.1 ≫ ε.1  ,
    fun T ↦ by
      have toProve : rewrittenTrafo (η.1 ≫ ε.1) T = rewrittenTrafo η.1 T ≫ rewrittenTrafo ε.1 T := by simp ; aesop
      rw [toProve]
      apply compPresVertical
      exact η.2 T
      exact ε.2 T

    ⟩
@[ext ,simp] lemma extCartTrafo {P Q : fibration B} {F G : P ⥤c Q} (η ε : F =>c G ) (p : η.1 = ε.1) : η = ε  := Subtype.ext p

--def cartNatTrans := ∀ (A : B) , F / A ⟶ G / A
-- @[simp] lemma ci {P Q : fibration B} {F G : P ⥤c Q} (η : F =>c G) : compCartTrans η (cartesianIdTrans G)  = η := by ext ; aesop
instance : Category (P ⥤c Q) where
  Hom := fun F G ↦ F =>c G
  id := cartesianIdTrans
  comp := compCartTrans
  -- comp_id := ci


--def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
def trafoOnFibers (η : F =>c G) (A : B) : F / A ⟶ G / A where
  app := by
    obtain  ⟨ η : F.1.left ⟶ G , isCart ⟩ := η
    intro X
    use rewrittenTrafo η X ;
    exact (isCart X)

  naturality := by sorry
/- instance : Bicategory (fibration B) where
  Hom := fun P Q ↦ P ⥤c Q
  id := fun P ↦ by use 𝟙 P.1 ; sorry
  comp := fun {P Q R} F G ↦ ⟨ F.1 ≫ G.1 , by sorry ⟩


  whiskerLeft := by sorry
  whiskerRight := by sorry
  associator := by sorry
  leftUnitor := by sorry
  rightUnitor := by sorry
-/

end FiberedCategories
