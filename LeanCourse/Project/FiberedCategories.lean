import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
set_option autoImplicit true

namespace CategoryTheory

--open Opposite
set_option maxHeartbeats 500000
universe v₁ u₁ s₁ t₁--v₂ u₁ u₂

variable {𝕏 : Type u₁} {B : Type u₁} [Category.{v₁} B] [Category.{v₁} 𝕏] {P : 𝕏 ⥤ B}
namespace FiberedCategories


def substCod {X Y Z : B} (h : Y = Z) (f : X ⟶ Y) : (X ⟶ Z) := f ≫ CategoryTheory.eqToHom h -- by rw [← h]  ; exact f
def substDom {X Y Z : B} (h : X = Y) (f : Y ⟶ Z) : (X ⟶ Z) := CategoryTheory.eqToHom h ≫ f -- by rw [h]  ; exact f




def obj_over (A : B) := {X : 𝕏 // P.obj X = A}
instance : CoeOut (obj_over (P:=P) A) 𝕏 := ⟨fun α ↦ α.1⟩
@[simp] def isVertical {X X' : obj_over (P:=P) A} (α : X.1 ⟶ X') := P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2
def over_hom {A A' : B} (u : A ⟶ A') (X : obj_over (P:=P) A) (X' : obj_over (P:=P) A') := {
  α : X.1 ⟶ X' //
  P.map α ≫ CategoryTheory.eqToHom X'.2  = CategoryTheory.eqToHom X.2 ≫ u
}

@[simp] lemma compPresVertical {X Y Z : obj_over (P:=P) A} (f : X.1 ⟶Y.1 ) (g : Y.1 ⟶ Z.1) (p : isVertical f) (q : isVertical g) :
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
def forget : (obj_over (P:=P) A) ⥤ 𝕏 where
  obj := fun X ↦ X.1
  map := fun f ↦ f.1



@[simp] lemma compInFib {X Y Z : obj_over (P:=P) A} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl
@[simp] lemma idInFib {X : obj_over (P:=P) A} : (𝟙 X : X ⟶ X).1 = 𝟙 X.1 := rfl
@[simps] def coerc { X X' : obj_over A} (f : over_hom (P:=P) (𝟙 A) X X') : X ⟶ X' := ⟨ f.1 , by rw [isVertical, f.2] ; aesop ⟩
@[simps] def coercBack {X X' : obj_over A} (f : X ⟶ X') : over_hom (P:=P) (𝟙 A) X X' := ⟨ f.1 , by rw [f.2] ; aesop⟩

@[ext] structure liftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I)  where
  Y : obj_over (P:=P) J
  φ : over_hom u Y X

instance : CoeDep (liftOfAlong (P:=P) X u) L (L.Y.1 ⟶ X) where
  coe := L.φ.1
variable {J I : B} {u : J ⟶ I}

@[simps] def morphismToLift {X Y : 𝕏} (φ : Y ⟶ X) : liftOfAlong ⟨ X , rfl⟩  (P.map φ) where
  Y := ⟨ Y , rfl⟩
  φ := by use φ; simp

lemma morphismToLift_coe {X Y : 𝕏} (φ : Y ⟶ X) : (morphismToLift (P:=P) φ).φ.1 = φ := rfl

def isCartesian  {X : obj_over (P:=P) I} (τ: liftOfAlong X u):=
  ∀ {K : B} (v : K ⟶ J) (L: liftOfAlong X (v ≫u )) ,
    ∃! ψ : over_hom v L.Y τ.Y , ψ.1 ≫ τ.φ.1 = L

def isWeakCartesian {X : obj_over (P:=P) I} (τ: liftOfAlong X u):= ∀ (L : liftOfAlong X u) ,
  ∃! ψ : L.Y ⟶ τ.Y , ψ.1 ≫ τ.φ.1 = L


structure cartesianLiftOfAlong {J I : B} ( X : obj_over (P:=P) I) (u : J ⟶ I) extends liftOfAlong (P:=P) X u where
   isCart : isCartesian (P:=P) toliftOfAlong

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
    rw [coercBack_coe]

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
    obtain ⟨σ , hσ⟩ := weakCartifCartesian (X:=X) L L.1
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
    have bah : (β ≫α  ).1 ≫ φ.1 = φ.1  := by calc
      _ = (β.1 ≫ α.1) ≫ φ.1 := by rfl
      _ = β.1 ≫ α.1 ≫ φ.1 := by rw [Category.assoc]
      _ = β.1 ≫ ψ.1 := by rw [hα.1 ]
      _ = φ.1 := hβ.1

    have bah : β ≫ α= 𝟙 _ := by
      trans σ
      apply hσ.2
      exact bah
      symm
      apply hσ.2
      have this : (𝟙 _) ≫ φ.1 = φ.1 := by rw [Category.id_comp]
      exact this
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
def isFibration {B : Cat.{v₁ , u₁}} (P : Over B ) : Prop :=  ∀ {J I : B} (u : J ⟶ I) (X : obj_over (P:=P.hom) I) , ∃ φ:  liftOfAlong (P:=P.hom) X u , isCartesian φ
def fibration (B : Cat.{v₁ , u₁}) := { P : Over B  // isFibration P}

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

def objMappingBetweenFibers {P Q : fibration B} (F : P.1 ⟶ Q.1) {A : B} : obj_over (P:=P.1.hom) A → obj_over (P:=Q.1.hom) A := by
  intro X
  use (F.left : P.1.left ⥤ Q.1.left).obj X.1

  trans (F.left ≫ Q.1.hom).obj X.1 ; rfl ;
  have this : F.left ≫ Q.1.hom = P.1.hom := F.3 ;
  rw [this]
  exact X.2

variable {P Q : fibration B} {F G : P ⥤c Q}
def isIdentity  {𝕏 : Type u₁} [Category.{v₁} 𝕏] {X Y : 𝕏} (f : X ⟶ Y) : Prop := ∃ (p : X = Y) , f = eqToHom p

def toFunctorOnFibers (F : P ⥤c Q) (A : B) :
  Functor (obj_over (P := P.1.hom) A) (obj_over (P := Q.1.hom) A) where
    obj := objMappingBetweenFibers F.1

    map := fun {X Y} (f : X ⟶ Y) ↦ by
      use (F.1.left).map f.1
      simp
      let FQ : P.1.1 ⟶ B := F.1.1 ≫ Q.1.hom
      have this : FQ = P.1.hom := F.1.3 ;
      have myEq : (F.1.1 ≫ Q.1.hom).obj Y.1 = A := (objMappingBetweenFibers F.1 Y).2
      trans (FQ.map f.1 ≫ eqToHom myEq)
      rfl
      let myEq1 (Z : obj_over (P:=P) A) : FQ.obj Z.1 = P.1.hom.obj Z.1 := by rw [this]
      let myNat : FQ ⟶ P.1.hom := eqToHom F.1.3
      have this {Y : obj_over A} : eqToHom (myEq1 Y) = myNat.app Y.1 := (eqToHom_app F.1.3 Y.1).symm
      have EqEq : myEq = (myEq1 Y).trans Y.2 := rfl
      have EqHom : eqToHom myEq = eqToHom (myEq1 Y) ≫ eqToHom Y.2 := by rw [EqEq] ; rw [eqToHom_trans]
      rw [EqHom, ← Category.assoc , this ,  myNat.naturality , Category.assoc , f.2 ]
      rw [← this  , eqToHom_trans]
    map_id := fun X ↦ by apply Subtype.ext ; aesop
    map_comp := fun f g ↦ by apply Subtype.ext ; aesop

scoped infixr:70 " / " => toFunctorOnFibers


@[simp] def rewrittenTrafo (η : F.1.left ⟶G ) {A : B} (T : obj_over (P:=P.1.hom) A) : ↑((F / A).obj T).1 ⟶ ↑((G / A).obj T).1 :=
 (η.app T.1  : ↑((F / A).obj T).1 ⟶ ↑((G / A).obj T).1)

def cartesianNatTrans {P Q : fibration B}
  (F G : P ⥤c Q)
  := { η : F.1.left ⟶ G // ∀ {A : B} (T : obj_over (P :=P.1.hom) A) ,
  isVertical (X:=(F / A).obj T) (X':=(G / A).obj T) (η.app T.1  ) }

scoped infixr:80 " =>c " => cartesianNatTrans
@[simp] def cartesianIdTrans : (F : P ⥤c Q) →  F =>c F := fun F ↦ ⟨  𝟙 F.1.1 , fun {A} T ↦ idIsVertical _⟩


  @[simp] def compCartTrans {F G H: P ⥤c Q} (η: F =>c G) (ε : G =>c H) : F =>c H := ⟨
     η.1 ≫ ε.1  ,
    fun T ↦ compPresVertical _ _ (η.2 T) (ε.2 T)⟩
@[ext ,simp] lemma extCartTrafo {P Q : fibration B} {F G : P ⥤c Q} (η ε : F =>c G ) (p : η.1 = ε.1) : η = ε  := Subtype.ext p

def trafoOnFibers (η : F =>c G) (A : B) : F / A ⟶ G / A where
  app := by
    intro X
    use rewrittenTrafo η.1 X ;
    exact (η.2 X)

  naturality := fun {X} {Y} f ↦ by
    apply Subtype.ext
    have nat := η.1.naturality f.1
    calc
    ((F / A).map f ≫ ⟨ rewrittenTrafo η.1 Y , _⟩ ).1 = F.1.left.map f.1 ≫ rewrittenTrafo η.1 Y := by rfl
    _ = rewrittenTrafo η.1 X ≫ G.1.left.map f.1 := by
      exact nat
    _  =_ := by rfl
instance : Category (fibration B) where
  Hom := fun P Q ↦ P ⥤c Q
  id := fun P ↦ by use 𝟙 P.1 ; intro φ hφ ; simp
  comp := fun {P Q R} F G ↦ ⟨ F.1 ≫ G.1 , fun {X} {Y} φ hφ ↦ G.2 _ (F.2 _ hφ)⟩


instance {P Q : fibration B} : Category (P ⟶ Q) where
  Hom := fun F G ↦ F =>c G
  id := cartesianIdTrans
  comp := compCartTrans
  -- comp_id := ci

def forgetFibration {P Q : fibration B} : (⟨ P ⟶ Q , instCategoryHomFibrationToQuiverToCategoryStructInstCategoryFibration ⟩ : Cat)  ⥤ (P.1.left ⥤ Q.1.left)  where
  obj := fun F ↦ F.1.left
  map := fun f ↦ f.1
@[simps] instance FiberToTotalSpace {B : Cat} {P : Over B} {I : B} : obj_over (P:=P.hom) I ⥤ P.left where
  obj := fun X ↦ X.1
  map := fun f ↦ f.1

def extFunctor {C D : Cat} {F G : C ⥤ D}
  (η : F ⟶ G)
 (isLevelwiseIdent : ∀ X : C , isIdentity (η.app X) ) : F = G :=
  CategoryTheory.Functor.ext (fun X ↦ ((isLevelwiseIdent X).choose))
  (fun {X} {Y} f ↦ by
  let nat := η.naturality f
  rw[← Category.assoc]
  apply (CategoryTheory.Iso.eq_comp_inv (eqToIso _)).2
  have this : ∀ X , η.app X = eqToHom _ := fun X ↦ (isLevelwiseIdent X).choose_spec
  rw [← this X]
  rw [← nat]
  rw[ this Y]
  rfl
  exact ((isLevelwiseIdent Y).choose)
  )
def PShCat (B : Cat.{v₁ , u₁} )  : Cat:= Bundled.of (B ᵒᵖ ⥤ Cat.{s₁ , t₁})
@[simp] lemma simptest {P Q R: fibration B} {F : P ⥤c Q} {G : Q ⥤c R} : (F ≫ G).1 = F.1 ≫ G.1 := rfl
@[simp] lemma compCheck {A : B} (F : P ⥤c Q) (G : Q ⥤c R) (X : obj_over A) : (G/A).obj ((F / A).obj X) = ((F ≫ G) / A).obj X := rfl

end FiberedCategories
