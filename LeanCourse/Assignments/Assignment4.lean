import LeanCourse.Common

set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by {

      have gauss : ∀ n , (∑ i in range (n + 1), i : ℚ) = (n * (n + 1)) / 2 := by {
        intro n
        induction n
        case zero => simp
        case succ k ih =>
          rw [sum_range_succ, ih]
          push_cast
          ring
      }


      induction n
      case zero => simp
      case succ n ih =>
        rw [sum_range_succ , ih]

        rw [sum_range_succ _ (n+1)]

        rw [gauss]
        field_simp
        ring

    }



open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have helper : ∀ i , C i ⊆ A i := by
    intro i
    intro y hy
    rw [hC i] at hy
    simp at hy
    exact hy.1




  have my : ∀ {i j} , (Disjoint on C) i j → C i ∩ C j = ∅   := by
    exact fun {i j} a => Disjoint.inter_eq a





  constructor

  · intro i j hij
    apply disjoint_iff.2
    wlog h : i < j generalizing i j
    have hji : j < i := by exact Ne.lt_of_le (id (Ne.symm hij)) (not_lt.mp h)
    · have ji : j ≠ i := by exact id (Ne.symm hij)
      rw [inf_comm]
      apply this
      exact ji
      exact hji
    ext x
    constructor
    intro ⟨ hx , hy⟩
    rw [hC j] at hy
    rw [hC i] at hx

    simp at hy
    simp at hx

    exact (hy.2 i h (hx.1))
    exact fun a => a.elim



  have h := wf.wf.has_min
  ext el

  constructor

  · intro ⟨ x  , ⟨ i , hx⟩  , hx2⟩
    simp
    use i
    simp at hx
    rw [← hx] at hx2
    exact (helper i hx2)
  intro ⟨ x , ⟨  i , hi ⟩ , hx2 ⟩
  simp
  let s := { i : ι | el ∈ A i}
  obtain ⟨a , ha⟩  := h s (by use i ; simp at hi ; rw [← hi] at hx2 ; exact hx2 )
  use a
  rw [hC a]
  simp
  constructor
  · exact ha.1
  intro x hx hel
  apply ha.2
  exact hel
  exact hx























/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h
instance : Coe PosReal Real := ⟨fun x ↦ x.1⟩
lemma exercise4_3 : Group PosReal := {
  mul := fun x y ↦ ⟨ x * y , mul_pos x.2 y.2 ⟩
  mul_assoc := fun x y z ↦ by
    have this : x.1 * y * z = x.1 * (y * z) := mul_assoc x.1 y z ;
    apply PosReal.ext
    norm_cast


  one := ⟨  1 , Real.zero_lt_one ⟩
  one_mul := fun x ↦ PosReal.ext _ x (one_mul x.1)
  mul_one := fun x ↦ PosReal.ext _ x (mul_one x.1)
  inv := fun x ↦ ⟨ x.1 ⁻¹  , inv_pos.2 (x.2) ⟩
  mul_left_inv := fun x ↦ PosReal.ext _ _ (by apply inv_mul_cancel  ; apply lt_or_lt_iff_ne.1 ; right ; exact x.2)


}
lemma nice : ∀ {m} , m ≥ 2 → m > 0 := fun ha ↦ by  {
    calc
      _ ≥ 2 := ha
      2 > 0 := Nat.succ_pos 1
  }

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    constructor
    intro hn
    simp at hn
    push_neg at hn
    by_cases h0 : n = 0
    · left
      exact h0
    by_cases h1 : n = 1
    · right
      left
      exact h1

    have h : n ≥ 2 := by
      have this : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h0
      have this : n > 1 := by exact Ne.lt_of_le' h1 this

      exact this

    have this : ¬(2 ≤ n ∧ ∀ m, 2 ≤ m → m < n → ¬m ∣ n) := by
      intro pf
      apply hn
      apply prime_def_lt'.2 pf
    push_neg at this
    specialize this h
    obtain ⟨ m , hm ⟩ := this
    right
    right
    use m
    obtain ⟨ m' , hm'⟩ := hm.2.2
    use m'
    constructor
    · exact hm.1
    · constructor
      · have this : 1 * m < m' * m := by {
          rw [mul_comm m' m, ← hm']
          rw [one_mul]
          exact hm.2.1
        }
        have this : 1  < m' := by exact lt_of_mul_lt_mul_right' this
        exact this
      · exact hm'






    intro hp hq
    obtain no|n1|hab := hp
    rw [no] at hq
    simp at hq
    rw [n1] at hq
    simp at hq
    obtain ⟨ a , b , hab⟩ := hab

    apply (Nat.prime_def_lt'.1 hq  ).2
    exact hab.1
    calc
      a < a * 2 := (lt_mul_iff_one_lt_right (nice hab.1)).2 (one_lt_succ_succ 0)
      _ ≤ a * b := monotone_mul_left_of_nonneg (Nat.zero_le a) hab.2.1
      _ = n := by symm  ; exact hab.2.2

    use b
    exact hab.2.2



















open Int.ModEq
lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  have mono : ∀ {m n} , (m ≤ n) → 2^m ≤ 2^n := (Nat.pow_le_iff_le_right (Nat.AtLeastTwo.prop)).2
  have smono : ∀ {m n} , (m < n) → 2^m < 2^n := (Nat.pow_lt_iff_lt_right (Nat.AtLeastTwo.prop)).2

  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · simp at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [@pow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by apply Int.ModEq.sub_right ; apply Int.ModEq.pow ; exact Int.modEq_sub _ _
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rw[one_pow] ; simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := mono ha
  have h3 : 1 ≤ 2 ^ a := by rw [← pow_zero] ; apply mono  ; trans 2 ; exact Nat.zero_le 2 ; exact ha
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    apply smono
    calc
      a = a * 1 := symm (mul_one a)
      a * 1 < a * b := (mul_lt_mul_left (nice ha)).2 (by
        calc
          1 < 2 := Nat.one_lt_succ_succ 0
          2 ≤ b := hb)

  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by apply mono ; apply mul_nonneg ; trans 2 ; exact Nat.zero_le 2 ; exact ha ; trans 2 ; exact Nat.zero_le 2 ; exact hb ;
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  have this : 2 ^ a - 1 = 1 := by
    apply hn.2
    exact h5
    exact h'
  exact (h4 this)




/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/

lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
      by_contra x
      push_neg at x
      wlog h : a ≤ b generalizing a b
      · apply this b a hb ha ⟨ x.2 , x.1⟩
        simp at h
        exact Nat.le_of_lt h


      have h2 : a ≥ 2 * b + 1 := by

        obtain ⟨y  , hy⟩:=   x.2
        have hel : b * b < y * y := by
          rw [← Nat.pow_two] ;
          rw [← hy] ;
          exact (lt_add_iff_pos_right (b^2)).2 ha
        have this : b < y := by
          rw [@Nat.mul_self_lt_mul_self_iff] ;
          exact hel

        have this : b + 1 ≤ y := by exact this
        calc
          a = y * y - b ^ 2 := by exact (tsub_eq_of_eq_add_rev (id hy.symm)).symm
          _ ≥ (b + 1) * (b+1) - b^2 := by simp ; calc
              (b+1) * (b+1) ≤ y * y := Nat.mul_le_mul this this
              _ =  y * y - b^2 + b^2 := by symm ; rw [@tsub_add_cancel_iff_le] ; rw [Nat.pow_two] ; apply le_of_lt ; exact hel
          _ = 2 * b + 1 := by ring ; rw [Nat.add_sub_cancel]

      have this : 2 * b + 1 ≤ b := by trans a ; exact h2 ; exact h
      have this : b + 1 ≤ 0 := by
        rw  [Nat.two_mul] at this
        exact (Nat.add_le_add_iff_left b (b + 1) 0).mp this
      exact Nat.not_succ_le_zero b this
