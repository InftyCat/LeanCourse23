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
lemma rwFuncComp  {M N  : P.1.left} (morph : M ⟶ N):
  (Q.1).hom.map ((F.1).left.map morph) ≫ eqToHom (by rw [← comm F]) = eqToHom (by rw [comm F] ) ≫ P.1.hom.map morph := by
          have veryweird : (F.1.left ⋙ Q.1.hom).map morph = (F.1.left ≫  Q.1.hom).map morph := rfl
          rw [← Functor.comp_map ,veryweird , Functor.congr_hom (Over.w F.1 : F.1.left ⋙ Q.1.hom = _) morph , Category.assoc ,Category.assoc , eqToHom_trans , eqToHom_refl , Category.comp_id ]
-- lemma over_comp_coe

lemma rwFuncComp'  {M N  : P.1.left} (F : P ⟶ Q) (morph : M ⟶ N):
  P.1.hom.map morph = eqToHom (by symm ; rw [comm F] ) ≫ (Q.1).hom.map ((F.1).left.map morph) ≫ eqToHom (by rw [← comm F])  := by
  symm ; rw [rwFuncComp F morph,← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp] ;
lemma rwFuncComp''  {M N  : P.1.left} (F : P ⟶ Q) (morph : M ⟶ N):
  (Q.1).hom.map ((F.1).left.map morph) = eqToHom (by symm ; rw [comm F] ) ≫ P.1.hom.map morph  ≫ eqToHom (by rw [← comm F])  := by
  rw [rwFuncComp' F morph,← Category.assoc,← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp,Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id] ;

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
      aesop


    have trick : (v' ≫ P.1.hom.map L.φ.1) ≫eqToHom X.2 = v ≫ u := by rw [trick,Category.assoc] ; apply (_≫=·) ; rw [Category.assoc , eqToHom_trans,eqToHom_refl , Category.comp_id]
    -- let iX : over_hom ()
    let μ : over_hom (v ≫ u) K.1 X := over_comp trick (⟨ 𝟙 _ , by rw [Functor.map_id , Category.id_comp,eqToHom_trans]⟩ ) (K.φ)

    obtain ⟨ψ , hψ⟩   :=  L.2 _ ⟨  _ , μ⟩
    have p : (v' ≫ eqToHom Y.2) ≫ eqToHom (Y.2.symm) = v' := by calc
      _ = v' ≫ _ := by rw [Category.assoc]
      v' ≫ _ = v' ≫ (𝟙 _) := by apply (_≫= · ) ; rw [eqToHom_trans , eqToHom_refl]
      _ = v' := by rw [Category.comp_id v' ]

    let compOverHom : over_hom (eqToHom L.Y.2.symm) Y Y' := (⟨ 𝟙 _ , by rw [Functor.map_id , Category.id_comp,eqToHom_trans]⟩ )
    let compOverHomInv : over_hom (eqToHom L.Y.2) Y' Y := (⟨ 𝟙 _ , by rw [Functor.map_id , Category.id_comp,eqToHom_trans]⟩ )
    let ψ' : over_hom v' K.Y Y' := over_comp p compOverHom ψ
    use ψ'
    constructor

    simp
    rw [hψ.1,over_comp_coe,Category.comp_id]
    intro y hy
    let y' : over_hom v K.Y Y := over_hom_comp compOverHomInv y
    have this : y' = ψ := by
      refine hψ.2 y' ?_
      simp
      exact hy



    apply Subtype.ext
    rw [over_comp_coe p compOverHom ψ , ← this , over_hom_comp_coe,Category.assoc,Category.comp_id,Category.comp_id]










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
lemma verticalIsosAreCart'' {P : fibration B} (Y X : P [I]) (f : Y.1 ≅ X.1) (hf :isVertical f.hom) : isCartesianMorphism P.1 f.hom := by
  let g : Y ≅ X := Iso.mk (⟨ f.hom , hf⟩ : Y ⟶ X) (⟨ f.inv , isVertical_symm f hf⟩ : X ⟶ Y) (by apply Subtype.ext ; apply Iso.hom_inv_id) (by apply Subtype.ext ; aesop)
  have this : isCartesianMorphism P.1 g.hom.1 := verticalIsosAreCart (I:=I) (P:=P) g
  have goal : f.hom = g.hom.1  := by rfl
  rw [goal]
  assumption

@[simp] noncomputable def cartesianLiftFromFibration (P : fibration B) {J I} (u : J ⟶ I) (X : P[I]) : cartesianLiftOfAlong X u := ⟨(P.2 u X).choose , (P.2 u X).choose_spec⟩
def morphismToLift' {P : Over B} {J : B} (Y : obj_over J) {X: P.left} (φ : Y.1 ⟶ X)

  {w : J ⟶ P.hom.obj X} (comm : w = eqToHom Y.2.symm ≫ P.hom.map φ): liftOfAlong (P:=P.hom)  ⟨ X , rfl⟩ w :=
transportLift (comm.symm) ⟨ Y , by use φ; rw [← Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id,eqToHom_refl,Category.id_comp]⟩
lemma exchangeLaw {C : Cat} {X Y Z W  V : C} {f : X ⟶ Y} {g : Y ⟶Z } {h : Z ⟶ V} {i : V ⟶ W} :
  f ≫ (g ≫ h) ≫ i = (f ≫ g)  ≫ (h ≫ i) := by
  rw [Category.assoc , Category.assoc]
def cartesianMorphismToCartLiftGeneral {P : Over B} {I J : B} {X : obj_over I} (Y : obj_over J) {φ : Y.1 ⟶ X.1} (hφ : isCartesianMorphism  P φ)
  {u : J ⟶ I} (comm : u = eqToHom Y.2.symm ≫ P.hom.map φ ≫ eqToHom X.2) : cartesianLiftOfAlong (P:=P.hom) X u  where
  Y := Y
  φ := ⟨ φ  , by rw [comm,← Category.assoc,eqToHom_trans,eqToHom_refl, Category.id_comp] ⟩
  isCart := by

    intro K v L
    let X' : obj_over (P.hom.obj X.1) := ⟨X.1 , rfl⟩
    let Y' : obj_over (P.hom.obj Y.1) := ⟨Y.1 , rfl⟩
    let ident := eqToHom X.2.symm
    let comp : over_hom ident  X X':= by use 𝟙 X.1 ; aesop
    let compY :over_hom (eqToHom Y.2) Y' Y := by use 𝟙 Y.1 ; aesop
    let L' : liftOfAlong X' ((v ≫ eqToHom (_)) ≫ P.hom.map φ) := ⟨ _ , over_comp (by rw [Category.assoc,comm, Category.assoc ,exchangeLaw , eqToHom_trans,eqToHom_refl,Category.comp_id, Category.assoc]) comp L.φ⟩
    obtain ⟨ ψ , hψ⟩  := hφ (v ≫ eqToHom ( Y.2.symm)) L'
    let ψ' : over_hom v L'.Y Y := over_comp (by rw [Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id]) compY ψ
    use ψ'
    have liftφCoinc : L'.φ.1 = L.φ.1 := by rw [over_comp_coe,Category.comp_id]
    constructor ; swap
    · intro y hy
      apply Subtype.ext
      let compYInv : over_hom (eqToHom Y.2.symm) Y Y' := by use 𝟙 Y.1 ; aesop
      let y' : over_hom (v ≫ eqToHom Y.2.symm) L'.Y Y' := over_hom_comp compYInv y
      have hy' : y'.1 ≫ φ = L'.φ.1 := by rw [over_hom_comp_coe , Category.comp_id , liftφCoinc , hy]

      have : y' = ψ := by
        apply hψ.2 y' hy'
      calc
      y.1 = y'.1 := by rw [over_hom_comp_coe, Category.comp_id]
      _ = ψ.1 := congrArg (fun x ↦ x.1) this
      _ = ψ'.1 := by rw [over_comp_coe, Category.comp_id]

    · simp
      have this : ψ.1 ≫ φ = _ := hψ.1
      rw[this]
      exact liftφCoinc


def cartesianMorphismToCartLift {P : Over B} {J : B} {X : P.left} (Y : obj_over J) {φ : Y.1 ⟶ X} (hφ : isCartesianMorphism  P φ)
  {w : J ⟶ P.hom.obj X} (comm : w = eqToHom Y.2.symm ≫ P.hom.map φ)
  :
   cartesianLiftOfAlong (P:=P.hom) ⟨ X , rfl⟩ w := by apply cartesianMorphismToCartLiftGeneral (P:=P) (X:=⟨ X , rfl⟩ ) Y hφ ; rw [comm,eqToHom_refl,Category.comp_id] ;



def cartesianMorphismToCartLift' {P : Over B }{ X Y : P.1}  {φ : Y ⟶ X} (hφ : isCartesianMorphism  P φ) :
  cartesianLiftOfAlong ⟨ X , rfl⟩  (P.hom.map φ ) := cartesianMorphismToCartLift ⟨ Y , rfl⟩ hφ (by rw [eqToHom_refl,Category.id_comp])


def cartesianMorphismToCartLift'' {P : Over B } {I : B} {X : obj_over (P:=P.hom) I} { Y : P.1}  {φ : Y ⟶ X.1}
  {v : P.hom.obj Y ⟶ I} (comm : v = (P.hom.map φ ≫ eqToHom X.2))
(hφ : isCartesianMorphism  P φ) :
  cartesianLiftOfAlong X v := by apply cartesianMorphismToCartLiftGeneral (P:=P) (Y:=⟨ Y , rfl⟩ ) hφ  ; rw [eqToHom_refl , Category.id_comp] ; exact comm

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

    have EqObj : Q.1.hom.obj (F'.obj Y) = Q.1.hom.obj (F'.obj L'.Y.1) :=comm F ▸ (symm L'.Y.2).trans (comm F)
    let ident :=  eqToHom (EqObj)

    have eqMor : Q.1.hom.map (F'.map f) = ident ≫ Q.1.hom.map (F'.map L'.φ.1) := by {
        have rw := rwFuncComp F L'.φ.1
        have rw' := rwFuncComp F f
        apply (CategoryTheory.Iso.cancel_iso_hom_right _ _ (eqToIso ((comm F).symm))).1
        rw [eqToIso.hom]

        rw [rw',Category.assoc,rw]
        rw [← Category.assoc , eqToHom_trans]
        have this := L'.φ.2
        have this := symm (eqToHom (EqObj.trans (comm F).symm) ≫= L'.φ.2)

        rw [← Category.assoc,eqToHom_trans] at this
        rw [this,← Category.assoc] ;
        calc
          _ ≫ eqToHom (rfl : P.1.hom.obj (⟨ X , rfl⟩ : obj_over (P:=P.1.hom) _).1 = (P.1).hom.obj X)
          = _ := by aesop
    }

    let cartLift : cartesianLiftOfAlong (P:=Q.1.hom) ⟨ F'.obj X , rfl⟩   (Q.1.hom.map (F'.map f))  :=
        cartesianMorphismToCartLift (P:=Q.1) ⟨ F'.obj L'.Y.1 , EqObj.symm ⟩ hFf eqMor


    let fAsLift : cartesianLiftOfAlong ⟨F'.obj X , rfl⟩ (Q.1.hom.map (F'.map f)) := cartesianMorphismToCartLift' hf
    obtain ⟨ α , hα ⟩  := cartesianLiftIsUnique cartLift fAsLift
    let myIso : Y ≅ L'.Y := by
      apply Functor.preimageIso F' ;
      exact  FiberToTotalSpace.mapIso α
    have hmyIso: F'.map myIso.hom = α.hom.1 := by calc
      F'.map myIso.hom = (F'.mapIso myIso).hom := by rw [← F'.mapIso_hom]
      _ = ((FiberToTotalSpace.mapIso α)).hom := by rw [mapIso_preimageIso F']
      _ = FiberToTotalSpace.map α.hom := by rfl



    have this : isCartesianMorphism P.1 myIso.hom := by
      apply verticalIsosAreCart'' (P:=P) ⟨ Y , rfl ⟩ L'.Y myIso
      unfold isVertical

      have l := rwFuncComp F myIso.hom
      have l := l =≫ eqToHom (comm F)
      have t := α.hom.2
      unfold isVertical at t
      have h : Q.1.hom.map α.hom.1 = eqToHom (EqObj) := by calc
        _ = (Q.1.hom.map α.hom.1 ≫ eqToHom EqObj.symm) ≫ eqToHom (EqObj) := by rw[Category.assoc , eqToHom_trans,eqToHom_refl, Category.comp_id]
        _ = eqToHom (by rfl)≫ eqToHom (EqObj) := by apply (· =≫_) ; exact α.hom.2
        _ = eqToHom (EqObj) := by rw [eqToHom_refl,Category.id_comp]
      rw [hmyIso, h ,  eqToHom_trans, Category.assoc] at l
      have l := symm (swapPaths l)
      rw [Category.assoc , eqToHom_trans, eqToHom_refl, Category.comp_id] at l
      rw [l]
      rw [eqToHom_trans, eqToHom_trans]

    have hf : f = myIso.hom ≫ L'.φ.1 := by
      apply F'.map_injective ;
      rw [Functor.map_comp] ;
      trans fAsLift.φ.1
      · rfl
      · rw [← hα.1] ;
        symm
        apply eq_whisker_eq hmyIso
        rfl

    rw [hf]
    apply compCartesianMorphisms
    exact this
    exact cartLiftToCartMor L'


lemma liftFromCartesiannessIsUnique  {P : fibration B} {J I : B} {X  : P[I]} {Y : P [J]} {u : J ⟶ I}
  {C : liftOfAlong X u} (isw : isWeakCartesian C) {f f' : Y ⟶ C.Y} (p : f.1 ≫ C.φ.1 = f'.1 ≫ C.φ.1) : f = f' := by
    let lift : liftOfAlong X u := ⟨ Y , over_comp  (by rw [Category.id_comp]) C.φ (coercBack f) ⟩
    exact ExistsUnique.unique (isw lift ) rfl p.symm
lemma liftFromCartesiannessIsUnique'  {P : fibration B} {J I : B} {X  : P[I]} {Y : P [K]} {u : J ⟶ I} {v : K ⟶ J}
  (C : cartesianLiftOfAlong X u) {f f' : over_hom v Y C.Y} (p : f.1 ≫ C.φ.1 = f'.1 ≫ C.φ.1) : f = f' := by
    let lift : liftOfAlong X (v ≫ u) := ⟨ Y , over_hom_comp C.φ (f) ⟩
    exact ExistsUnique.unique (C.2 v lift ) rfl p.symm

@[simps] def mappingOverHom {P Q : fibration B} (F : P ⟶ Q ) {J I} {u : J ⟶ I} {Y : P [J]} {X : P[I]} (φ : over_hom u Y X) :  over_hom u ((F / J).obj Y) ((F / I).obj X) := by
  use F.1.left.map φ.1
  let hφ := φ.2

  calc
      (Q.1).hom.map ((F.1).left.map φ.1) ≫ eqToHom (_ : Q.1.hom.obj ((F / I).obj X).1 = I)
      =  ((Q.1).hom.map ((F.1).left.map φ.1) ≫ eqToHom (symm (comm F))) ≫ eqToHom X.2 := by rw [Category.assoc] ; apply (_ ≫= · ) ; symm ; apply eqToHom_trans
    _ = (eqToHom (symm (comm F)) ≫ P.1.hom.map (φ.1)) ≫ eqToHom X.2 := by rw [rwFuncComp F φ.1]
    _ = eqToHom (_) ≫ eqToHom (_) ≫ u := by rw [Category.assoc] ; apply (_≫= · ) ; apply φ.2
    _ = eqToHom (_ : (Q).1.hom.obj ((F / J).obj Y).1 = J) ≫ u := by  rw [← Category.assoc] ; apply (· =≫ u) ; apply eqToHom_trans


def cartFunctorPresCartLifts {I : B} {F : P ⟶ Q} {X : obj_over (P:=P.1.hom) I} {u : J ⟶I } (L : cartesianLiftOfAlong X u) : cartesianLiftOfAlong ( (F / I).obj X) u := by
    let Fφ := mappingOverHom F L.φ
    let FXf :=  (F / I).obj X
    let Ff : isCartesianMorphism Q.1 (F.1.left.map L.φ.1) := F.2 L.φ.1 (cartLiftToCartMor L) --
    apply cartesianMorphismToCartLiftGeneral ((F / J).obj L.Y) Ff
    symm
    rw [rwFuncComp'' F L.φ.1]
    rw [exchangeLaw,eqToHom_trans,Category.assoc,eqToHom_trans]
    rw [L.φ.2, ← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
