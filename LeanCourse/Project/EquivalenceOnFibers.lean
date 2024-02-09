import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Equivalence
import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
-- import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.FibrationBicategory
import LeanCourse.Project.CounitOnFibers
import LeanCourse.Project.CartesianFunctors
--import LeanCourse.Project.PreSheavesOfCategories
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

 variable {B : Cat.{v₁ , v₁}} {I : B}
 variable {P : fibration B}
 local notation "E" => E'_obj (P:=P) (I:=I)
 notation u  "°" X => cartesianLiftFromFibration P u X

noncomputable def fufi {X : P [I]} {uv u : ((fundamentalFibration.obj I).1).left.1} (v : uv ⟶ u) :
  ∃! φ : over_hom v.left (uv.hom ° X).Y (u.hom ° X).Y , φ.1 ≫ (u.hom ° X).φ.1 = ((uv.hom) ° X).1 :=
   ((u.hom ° X).2 v.left (transportLift (by aesop) ((uv.hom) ° X).1))

noncomputable def functorOnFibers (X : P [I]) : (fundamentalFibration.obj I).1.left ⥤ P.1.left where
  obj := fun u  ↦ (u.hom ° X).Y.1
  map := fun v ↦ (fufi v).choose.1
  map_id := by
    intro u ;
    symm
    have : ⟨ 𝟙 (u.hom ° X).Y.1 , _⟩ = (fufi (𝟙 u)).choose  := (fufi (𝟙 u)).choose_spec.2 ⟨ 𝟙 _ , by simp ; rw [Over.id_left,Category.comp_id] ⟩ (by simp)
    exact congrArg (fun x ↦ x.1) this

  map_comp := fun {uvw} {uv} {u} w v ↦ by

    let owc : over_hom (w ≫ v).left (uvw.hom ° X).Y (u.hom ° X).Y  := over_comp (P:=P.1)  (by aesop) (fufi v).choose (fufi w).choose --

    have : owc = (fufi (w ≫ v)).choose := by
      apply (fufi (w ≫ v)).choose_spec.2
      rw [over_comp_coe,Category.assoc,(fufi v).choose_spec.1,(fufi w).choose_spec.1]
    symm
    exact congrArg (fun x ↦ x.1) this


@[simps!] noncomputable def OverMorphOnFibers (X : P [I]) : (fundamentalFibration.obj I).1 ⟶ P.1 := by
  apply Over.homMk
  swap
  exact functorOnFibers X
  apply extFunctor ; swap
  · constructor ; swap
    · intro u
      exact eqToHom (u.hom ° X).Y.2

    · intro uv u v
      simp
      exact (fufi (P:=P) v).choose.2
  · intro u ; use (u.hom ° X).Y.2



--def fOnFund (X : fundamentalFibration.obj I ⟶ P) (u: ((fundamentalFibration.obj I).1).left.1) : P [u.left] :=
notation "⟪ " v "  ⟫" => (morphismToLift (P:=(fundamentalFibration.obj I).1.hom) v).φ
notation X " § " u   =>  (toFunctorOnFibers X _).obj ⟨ u , rfl⟩  -- ⟨  (X.1.left.obj u) , ((comm X).symm) ⟩
def morph {u: ((fundamentalFibration.obj I).1).left.1} : u ⟶ Over.mk (𝟙 _) := Over.homMk u.hom
def cLift (X : fundamentalFibration.obj I ⟶ P) (u: ((fundamentalFibration.obj I).1).left.1) : cartesianLiftOfAlong (E_obj_obj X) u.hom :=
  by

  apply cartesianMorphismToCartLiftGeneral (X § u)
  exact X.2 morph (automaticallyCart <| morph)
  rw [rwFuncComp,← Category.assoc , eqToHom_trans,eqToHom_refl,Category.id_comp] ; rfl
@[simp] lemma cLift_coe   {X : fundamentalFibration.obj I ⟶ P} {u: ((fundamentalFibration.obj I).1).left.1} : (cLift X u).φ.1 = X.1.left.map (Over.homMk u.hom : u ⟶ Over.mk (𝟙 _)) := rfl
--lemma funcFib {K J I : B} {X : P[I]} {Y : P[J]} {Z : P[K]} (v : K ⟶ J) {u : J ⟶ I} (α : over_hom v Z Y) {β : over_hom u Y X} : (α >> β )
noncomputable def equivOnFibersFull {X Y : fundamentalFibration.obj I ⟶ P}  (f: E'_obj.obj X ⟶ E'_obj.obj Y) (u: ((fundamentalFibration.obj I).1).left.1)
  : ∃! ψ : (X § u) ⟶ (Y § u) ,   ψ.1 ≫ (cLift Y u).φ.1 = (cLift X u).φ.1 ≫ f.1
    := weakCartifCartesian (cLift Y u) ⟨ _ , ((cLift X u).φ >[ by rw [Category.comp_id]]> coercBack f)⟩
lemma cLiftNat {X Y : fundamentalFibration.obj I ⟶ P} {f : E_obj_obj X ⟶ E_obj_obj Y} {uv u : ((fundamentalFibration.obj I).1).left.1}{ v : uv ⟶ u}
  : (X.1.left.map v ≫ (equivOnFibersFull f u).choose.1) ≫ (cLift Y u).φ.1
    =  (equivOnFibersFull f uv).choose.1 ≫ Y.1.left.map (morphismToLift v).φ.1 ≫ (cLift Y u).toliftOfAlong.φ.1 := by
      calc
      _ = X.1.left.map v ≫ X.1.left.map morph ≫ f.1 := by rw [Category.assoc] ; apply (_≫=· ) ; rw [(equivOnFibersFull f u).choose_spec.1 ] ; rfl
      _ = X.1.left.map (morph) ≫ f.1 := by rw [← Category.assoc , ← X.1.left.map_comp, ((_) : v ≫ morph = morph (u:=uv))] ; apply Over.OverMorphism.ext ; exact Over.w v
      _ = (cLift X uv).φ.1 ≫ f.1 := rfl
      _ = _ := by rw [← (equivOnFibersFull f uv).choose_spec.1]
      _ = _ := by apply (_≫=· ) ; rw [cLift_coe , cLift_coe , ← Y.1.left.map_comp, morphismToLift_coe] ; apply congrArg Y.1.left.map ; apply Over.OverMorphism.ext ; exact (Over.w v).symm

/-
def cartesianNatTrans {P Q : fibration B}
  (F G : P ⥤c Q)
  := { η : F.1.left ⟶ G // ∀ {A : B} (T : obj_over (P :=P.1.hom) A) ,

  isVertical (X:=(F / A).obj T) (X':=(G / A).obj T) (η.app T.1  ) }
  -/


@[simps] def mkCartesianNatTrans  (F G : P ⥤c Q) (η : F.1.left ⟶ G.1.left)
  (ass : ∀ X : P.1.left , isVertical (X:= F § X) (X':=G § X) (η.app X)) : F =>c G := by
  use η ;
  intro A T
  unfold isVertical
  rw [VerticalAsPath (ass T.1) , eqToHom_trans]
noncomputable instance : Full E := by
    constructor ; swap
    · intro X Y f
      apply mkCartesianNatTrans ; swap

      · apply NatTrans.mk ; swap
        · exact fun u => (equivOnFibersFull f u).choose.1
        · intro uv u v ;


          have : (mappingOverHom X ⟪ v ⟫  >[ by rw [Category.comp_id, Category.id_comp]]> coercBack (equivOnFibersFull f u).choose)
            = (coercBack (equivOnFibersFull f uv).choose >> mappingOverHom Y ⟪ v ⟫) := by

            apply liftFromCartesiannessIsUnique' (cLift Y u)
            calc
            _ = (X.1.left.map v ≫ (equivOnFibersFull f u).choose.1) ≫ (cLift Y u).φ.1 := by rfl
            _ =  (equivOnFibersFull f uv).choose.1 ≫ Y.1.left.map (morphismToLift v).φ.1 ≫ (cLift Y u).toliftOfAlong.φ.1 := cLiftNat
            _ = (coercBack (equivOnFibersFull f uv).choose >>mappingOverHom Y (morphismToLift v).φ).1 ≫ (cLift Y u).φ.1 := by symm ; rw [over_hom_comp_coe (mappingOverHom Y (morphismToLift v).φ) (coercBack (equivOnFibersFull f uv).choose),← Category.assoc] ; apply (·=≫_) ; rfl

          exact congrArg (fun x ↦ x.1) this
      · intro u
        exact (equivOnFibersFull f u).choose.2
    · intro X Y f ;
      apply Subtype.ext
      rw [E'_obj_map_coe]
      rw [mkCartesianNatTrans_coe]
      symm
      congr
      apply (equivOnFibersFull f (Over.mk <| 𝟙 I)).choose_spec.2 f
      simp only [cLift_coe]
      have hh : (Over.homMk (Over.mk (𝟙 I)).hom : Over.mk (𝟙 _ ) ⟶ Over.mk (𝟙 _)) = 𝟙 _ := by aesop
      have help : ∀ Y : fundamentalFibration.obj I ⟶ P  , Y.1.left.map (Over.homMk (Over.mk (𝟙 I)).hom : Over.mk (𝟙 _ ) ⟶ Over.mk (𝟙 _)) = 𝟙 (E'_obj.obj Y).1 := fun Y ↦ by
        rw [hh , Functor.map_id] ; rfl
      rw [help , help]
      rw [Category.comp_id f.1, Category.id_comp f.1]

lemma comm' {P Q : fibration B} (F : P.1 ⟶ Q.1)  : ∀ {A} , P.1.hom.obj A =  Q.1.hom.obj (F.left.obj A) :=  fun {A} ↦ by rw [← Functor.comp_obj , ← Over.w F] ; apply Functor.congr_obj ; rfl

lemma twoOutOfThreeCart {P : fibration B} {K J I} {v : K ⟶ J} {u : J ⟶ I} {w : K ⟶ I} {X : P[I]} {Y : P[J]}{ Z : P [K]} (comm : w = v ≫ u) {h : over_hom w Z X}
   {g : over_hom u Y X}  (hg  : isCartesian ⟨ _, g⟩  )  (hh : isCartesian ⟨ _, h⟩ ) {f : over_hom v Z Y} (hf : f.1 ≫ g.1 = h.1) : isCartesian ⟨ _ , f⟩ := by
    intro K w L ;
    have : ∃! ψ : over_hom w L.Y Z , ψ.1 ≫ h.1 = (L.φ >[ by rw [ Category.assoc] ]> g).1 := by apply hh _ ⟨ _ , (L.φ >[ by rw [comm , Category.assoc] ]> g) ⟩ ;
    let ⟨ ψ , hψ⟩ := this
    use ψ
    constructor
    · have : (ψ >> f) = L.φ := by
        apply liftFromCartesiannessIsUnique' ⟨ _ , hg⟩
        simp
        rw [hf]

        exact hψ.1

      exact congrArg (fun x ↦ x.1) this


    · intro ψ' hψ'
      apply liftFromCartesiannessIsUnique' ⟨ _ , hh⟩
      simp
      rw [hψ.1,← hf,← Category.assoc , hψ',over_comp_coe]

lemma fufiIsCart {X : P [I]} {uv u : ((fundamentalFibration.obj I).1).left.1} (v : uv ⟶ u) : isCartesian (P:=P.1.hom) ⟨ (uv.hom ° X).Y , (fufi (X:=X) v).choose⟩  := by
  apply twoOutOfThreeCart ; swap
  · exact  (u.hom ° X).2
  · exact symm (Over.w v)
  · exact  (uv.hom ° X).2
  exact (fufi (X:=X) v).choose_spec.1


  --(uv.hom ° X).2



instance : EssSurj E := by
    constructor
    intro X
    let F : fundamentalFibration.obj I ⥤c P := by
      use OverMorphOnFibers X
      intro uv u v _
      exact cartLiftToCartMor (P:=P) ⟨  _ , fufiIsCart (P:=P) (X:=X) v⟩
    use F
    constructor
    exact (cartesianLiftIsUnique (P:=P.1.hom) (idCartLift) (𝟙 _ ° X)).choose



instance : Faithful E := by
  constructor
  intro X Y f f' hf

  apply Subtype.ext
  apply NatTrans.ext
  ext u
  have : (⟨ f.1.app u , f.2 ⟨ u , rfl⟩ ⟩ : (X § u) ⟶ (Y § u)) =  ⟨ f'.1.app u , f'.2 ⟨ u , rfl⟩ ⟩ := by
    apply liftFromCartesiannessIsUnique (weakCartifCartesian <| cLift Y u)
    rw [cLift_coe]
    calc
      f.1.app u  ≫ Y.1.left.map morph
          = X.1.left.map morph ≫ f.1.app (Over.mk (𝟙 _)) := by rw [← f.1.2 (morph (u:=u))]
        _ = X.1.left.map morph ≫ (E'_obj.map f).1 := by apply (_≫=·)  ; rfl
        _ =  X.1.left.map morph ≫ (E'_obj.map f').1 := by apply (_≫=·) ; rw[hf]
        _ =  X.1.left.map morph ≫ f'.1.app (Over.mk (𝟙 _)):= by apply (_≫=·) ; rfl
        _ =  _ := by rw [f'.1.2 (morph (u:=u))] ; rfl


  exact congrArg (fun x ↦ x.1) this




theorem equivOnFibers : IsEquivalence E := by
  apply Equivalence.ofFullyFaithfullyEssSurj
