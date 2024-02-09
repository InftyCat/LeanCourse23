import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
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
variable {B : Cat.{v₁ , v₁}} {I J K : B}

instance : Category (Over I) := commaCategory
def isSingleton (X : Type _) : Prop := ∃ x : X , ∀ y : X , x = y
def isSingletonImpIsProp {X : Type _} (s : isSingleton X) (y y' : X) :  y = y' := by
  trans s.choose
  · symm ; exact s.choose_spec y
  · exact s.choose_spec y'
-- def isDiscreteFibration (P : fibration B) := weakDiscreteOverB P.1
def isDiscreteOverB (P : Over B) : Prop := ∀ {J I} (u : J ⟶ I ) (X : obj_over (P:=P.hom) I),
 isSingleton (liftOfAlong X u )
def uniqueLiftFromDiscreteness {P : Over B} (q : isDiscreteOverB P)
  {J I : B} {u : J⟶ I} {X : obj_over (P:=P.hom) I} {r s : liftOfAlong X u} : r = s := isSingletonImpIsProp (q u X) r s
lemma discreteIsCartesian  {P : Over B} (disc : isDiscreteOverB P) : isFibration P := fun {J I} u X ↦ by

  let φ : liftOfAlong X u  := (disc u X).choose
  use φ
  intro K v Z
  simp at K
  let ψ := (disc v (φ.1)).choose
  let tLift := transLift φ ψ
  have this : Z = tLift :=  uniqueLiftFromDiscreteness disc
  rw [this]
  use ψ.φ
  constructor
  rfl
  intro y _
  let ψ' : liftOfAlong φ.Y v := ⟨ _ , y⟩
  have goal : ψ' = ψ := uniqueLiftFromDiscreteness disc
  trans ψ'.φ
  rfl
  congr


def weakDiscreteOverB (P : Over B) := ∀ {D : B} {X Y : obj_over (P:=P.hom) D} (f : X ⟶ Y) , isIdentity f.1
lemma discImpWeakDisc {P : Over B} (q : isDiscreteOverB P) : (weakDiscreteOverB P) := fun {D} {X} {Y} f ↦ by
  let lift : liftOfAlong Y (𝟙 D) := ⟨ X , coercBack f ⟩
  let idLift : liftOfAlong Y (𝟙 D) := ⟨ Y , coercBack (𝟙 _)⟩
  have this : idLift = lift := uniqueLiftFromDiscreteness q
  obtain ⟨ p , hp⟩ := extInv _ _ this.symm
  use p
  calc
  f.1 = lift.φ.1 := rfl
  _ = eqToHom p ≫ idLift.φ.1 := hp.symm
  _ = eqToHom p ≫ 𝟙 _ := by rfl
  _ = eqToHom p := by rw [Category.comp_id]

def Ov (I : B) : Cat := ⟨  Over I , commaCategory  ⟩
@[simps] def domainOver (I : B) : Over B where
  left := Ov I
  right := default
  hom := Over.forget I
@[simp] lemma idDomainOver (I : B) : (domainOver I).left = Ov I := rfl
@[simp] def domainLift {A : B} (u : J ⟶ I) (X : obj_over I) : liftOfAlong (B:=B) (P:=(domainOver A).hom) X u := by
      let a := u ≫ eqToHom (symm X.2)
      use ⟨ Over.mk (a ≫ X.1.hom) , rfl⟩
      exact ⟨ Over.homMk a , by rw [eqToHom_refl , Category.id_comp ] ; apply (comp_eqToHom_iff _ _ _).2 ; aesop⟩


lemma OverMorExt  {X Y : (domainOver A).left} {f g : X ⟶ Y} (p : (domainOver A).hom.map f = (domainOver A).hom.map g) : f = g := by apply Over.OverMorphism.ext ; exact p

lemma domainIsDiscrete (A : B) : isDiscreteOverB (domainOver A) := fun {J I} u v ↦ by

  use (domainLift u v)
  intro L
  obtain ⟨ w , u'⟩ := L
  have this := u'.2
  simp at this

  apply liftOfAlong_ext ; swap
  --apply Subtype.ext

  simp
  let u1 := Over.w u'.1

  have goal : u ≫ eqToHom (v.2.symm) ≫ v.1.hom = eqToHom (w.2.symm) ≫  w.1.hom := by
    rw [← u1]
    symm ;
    rw [← Category.assoc, swapPaths this, Category.assoc]


  have goal1 : Over.mk (u ≫ eqToHom (_ : I = (domainOver A).hom.obj v.1) ≫v.1.hom) = w.1 := by
    congr

    · exact w.2.symm
    · have path : HEq (u ≫ eqToHom (_ : I = (domainOver A).hom.obj v.1) ≫ (v.1).hom) w.1.hom := by
        rw [goal] ; apply (Functor.conj_eqToHom_iff_heq (eqToHom w.2.symm ≫ w.1.hom) (w.1.hom) (w.2.symm) rfl).1
        rw [eqToHom_refl, Category.comp_id]
      exact path

  exact goal1

  apply OverMorExt
  rw [Functor.map_comp, eqToHom_map]
  simp
  exact (swapPaths this).symm


@[simp] def fundamentalFibrationObj (A : B) : fibration B := ⟨ domainOver A , discreteIsCartesian (domainIsDiscrete A)⟩

lemma automaticallyCart {A : B} {X Y : Ov A} (f : X ⟶ Y) : isCartesianMorphism (domainOver A) f := by
  intro k v L
    --obtain ⟨ l , vFf ⟩ :=

  obtain ⟨ l' , hl'⟩   := domainIsDiscrete A v ⟨ X , rfl⟩

  let u := (domainOver A).hom.map f
  let f' : over_hom u ⟨ X , rfl⟩ ⟨ Y , rfl⟩ := ⟨ f , by rw [eqToHom_refl, eqToHom_refl , Category.comp_id, Category.id_comp] ⟩
  --let P : fibration B := ⟨ domainOver A , discreteIsCartesian (domainIsDiscrete A)⟩

  let L' : over_hom (v ≫ (domainOver A).hom.map f) l'.Y ⟨ Y , rfl⟩  := over_hom_comp (P:=domainOver A) f' l'.φ

  let L' : liftOfAlong (P:=(domainOver A).hom) ⟨ Y , rfl⟩ (v ≫ u)   := ⟨ l'.Y , L'⟩
  have this : L' = L := by apply isSingletonImpIsProp (domainIsDiscrete A (v ≫ (domainOver A).hom.map f) ⟨ Y , rfl⟩ )
  rw [← this]
  use l'.φ
  constructor
  · rw [over_hom_comp_coe] ; rfl
  · intro y _ ; symm ;
    have t : l' = ⟨ _ , y⟩ := hl' ⟨ _ , y⟩
    have t2 : l' = ⟨ L'.Y , l'.φ⟩  := by rfl
    aesop

@[simp] def fundamentalFibrationMap {J I : B} (u : J ⟶ I) : fundamentalFibrationObj J ⥤c fundamentalFibrationObj I
  := ⟨ Over.homMk (Over.map u) , fun {X} {Y} φ hφ ↦ automaticallyCart _⟩
@[simp] lemma idFibration (F : fibration B) : (𝟙 F : F ⥤c F).1 = 𝟙 F.1 := rfl
@[simp] lemma fundamentalFibrationUnderlying ( A : B) : (fundamentalFibrationObj A).1 = domainOver (A) := rfl
open Over
open Comma
lemma fundamentalFibration_map_id {K : B} : fundamentalFibrationMap (𝟙 K) = 𝟙 (fundamentalFibrationObj K) := by
    ext
    rw [fundamentalFibrationMap]
    simp

    have p : ∀ {X } , (map (𝟙 K)).obj X = (Functor.id (Ov K)).obj X := by unfold map ; unfold mapRight ; aesop
    apply Functor.ext ; swap
    · intro X ;
      trans X -- ((Functor.id (Ov K)).obj X)
      · exact p
      · rfl
    · intro X Y f ;
      apply OverMorphism.ext ;
      rw [map_map_left]
      let forg := Over.forget (Ov K)
      symm
      rw [← forget_map , Functor.map_comp,Functor.map_comp,eqToHom_map,eqToHom_map,eqToHom_refl,eqToHom_refl,forget_map,Category.comp_id,Category.id_comp]
      rfl

lemma fundamentalFibration_map_comp {K J I : B} (v : K ⟶ J ) ( u : J ⟶ I) :
  fundamentalFibrationMap (v ≫u)  = fundamentalFibrationMap v ≫  fundamentalFibrationMap u := by
    ext

    simp
    apply Functor.ext ; swap
    · intro X

      unfold map
      unfold mapRight

      simp


    · intro X Y f
      apply OverMorphism.ext
      rw [map_map_left]
      let forg := Over.forget (Ov K)
      --have : (((map v : Over K ⟶ Over J) ≫ map u).map f).left = ((map v ⋙ map u).map f).left := rfl
      symm
      rw [← forget_map,Functor.map_comp,Functor.map_comp,eqToHom_map,eqToHom_map,eqToHom_refl,eqToHom_refl,forget_map,Category.comp_id,Category.id_comp]
      trans ((map v ⋙ map u).map f).left
      · rfl
      · rw [Functor.comp_map (map v) (map u) f,map_map_left,map_map_left]

@[simps] def fundamentalFibration : B ⥤ fibration B where
  obj := fundamentalFibrationObj --fun A ↦ discreteIsCartesian (domainIsDiscrete A) -- --
  map := fundamentalFibrationMap --fun u ↦ ⟨ Over.homMk (Over.map u) , fun {X} {Y} φ hφ ↦ automaticallyCart _⟩--
  map_comp := fun v u ↦ fundamentalFibration_map_comp v u
  map_id := fun X ↦ fundamentalFibration_map_id
