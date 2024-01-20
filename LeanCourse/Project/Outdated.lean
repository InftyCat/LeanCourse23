/- BOTH NOT IMPORTANT
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
/-
def cartesianMorphismToCartLift (P : Over B ) {I : B} {X : obj_over (P:=P.hom) I} { Y : P.1}  {φ : Y ⟶ X.1} (hφ : isCartesianMorphism  P φ) : cartesianLiftOfAlong X (P.hom.map φ ≫ eqToHom X.2) where
  Y := ⟨ Y , rfl⟩
  φ := ⟨ φ  , by aesop⟩
  isCart := by sorry --apply compPresCartesian -- sorry --hφ
-/