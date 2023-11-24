import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N := by
  exact LinearMap.coprod f g



example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

instance exercise5_2 : Group {x : R // IsAUnit x} where
  mul := fun x y  ↦ ⟨ x * y , by
    obtain ⟨ x' ,hx⟩ := x.2
    obtain ⟨ y' , hy⟩ := y.2
    use x' * y' ; ring ; rw [mul_comm x' y' , mul_assoc , mul_assoc , ← mul_assoc x' x y] ; rw [hx] ; ring ; apply hy⟩
  mul_assoc := fun x y z ↦ Subtype.eq (mul_assoc x.1 y.1 z.1)

  one := ⟨ 1 , by use 1 ; ring ⟩
  one_mul := fun x ↦ Subtype.eq (one_mul x.1)
  mul_one := fun x ↦ Subtype.eq (mul_one x.1)
  inv := fun x ↦ by
    obtain hx := Exists.choose_spec x.2 ;
    use Exists.choose x.2
    use x
    rw [mul_comm]
    exact hx

  mul_left_inv := fun x ↦ by
    obtain hx := Exists.choose_spec x.2 ;
    apply Subtype.eq
    simp
    exact hx



-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := rfl

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have fp : ∀ {n : ℕ} ,  (p ∣  n !) → p > n → False := by
    have facprime : ∀ n : ℕ ,  (p ∣  n !) → p ≤ n := fun n => (Prime.dvd_factorial h2).1
    intro h1 h2 a
    exact lt_le_antisymm a (facprime h1 h2)

  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    have this : Nat.choose p i * i ! * (p - i)! = p !
      := by apply choose_mul_factorial_mul_factorial ; apply le_of_lt ; simp at hi ; exact hi.2
    have pdivpfac : p ∣ p ! := by use (p-1)! ; exact (mul_factorial_pred h3).symm
    have this : p ∣ (Nat.choose p i * i ! * (p - i)!) := by rw [this] ; exact pdivpfac
    simp at hi
    obtain a12|a3 := (Prime.dvd_mul (prime_iff.mp h2)).1  this
    obtain a1|a2 := (Prime.dvd_mul (prime_iff.mp h2)).1 a12
    · exact a1
    · exfalso
      exact fp a2 hi.2
    · exfalso
      apply fp a3
      apply Nat.sub_lt_left_of_lt_add
      apply le_of_lt
      exact hi.2
      apply (lt_add_iff_pos_left _).2 hi.1
  have h6prep : ∀ i ∈  Ioo 0 p , Nat.choose p i  = (0 : K) := by
    intro i hi
    exact (CharP.cast_eq_zero_iff K p (Nat.choose p i)).mpr (h5 i hi)

  -- have h6prep : {i : Ioo 0 p}  Nat.choose p i  = (0 : K) := by exact?
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 := by {
  calc
    _ =  ∑ i in Ioo 0 p, (x ^ i * y ^ (p - i)) * 0 := by sorry
    _ = 0 := by simp ;
     -- conv_lhs
      -- {
      -- apply_congr

      -- }
  }
  calc
    ∑ m in range (p + 1), x ^ m * y ^ (p - m) * ↑(Nat.choose p m) = (∑ m in range p, x ^ m * y ^ (p - m) * ↑(Nat.choose p m)) + x^p * y^(p - p) * Nat.choose p p := by exact sum_range_succ (fun x_1 ↦ x ^ x_1 * y ^ (p - x_1) * ↑(Nat.choose p x_1)) p ; simp
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * ↑(Nat.choose p m)) + x^p := by simp
    _ = (y^p + (∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i)) + x^p := by rw [h4] ; simp ;
    _ = x^p + y^p := by rw [h6] ; ring


/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  sorry
