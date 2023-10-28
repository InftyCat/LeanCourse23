import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
  by_contra h
  have this : ¬ p ∧ p := by
    constructor
    intro hp
    apply h
    left
    exact hp
    by_contra hp
    apply h
    right
    exact hp
  exact this.1 this.2












/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
      intro ε hε
      obtain ⟨ N , hN ⟩ := hs ε hε
      obtain ⟨ N', hN' ⟩ :=  hr N
      use N'
      intro n hn
      apply hN
      apply hN'
      exact hn



/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
    intro ε hε
    obtain ⟨ N₁ , hN₁ ⟩ := hs₁  ε hε
    obtain ⟨ N₃  , hN₃ ⟩ := hs₃  ε hε
    use max N₁ N₃
    intro n hn
    apply abs_lt.2
    constructor
    { calc
    -ε < (s₁ n - a) := by {
      have t1 : |s₁ n - a| < ε := by
        apply hN₁
        exact le_of_max_le_left hn

      exact (abs_lt.1 t1).1
    }
    _ ≤ s₂ n - a := by exact sub_le_sub_right (hs₁s₂ n) a
    }
    calc
    ε > (s₃  n - a) := by {
      have t2 : |s₃ n - a| < ε := by
        apply hN₃
        exact le_of_max_le_right hn

      exact (abs_lt.1 t2).2
    }
    _ ≥ s₂ n - a := by exact sub_le_sub_right (hs₂s₃ n) a





/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
  intro ε hε
  use ⌈ε⁻¹⌉₊
  intro n hn
  simp
  rw [abs_inv]

  apply (inv_lt _ _).2

  {calc
  ε⁻¹ ≤ ⌈ε⁻¹⌉₊ := le_ceil ε⁻¹
  _ ≤ n := cast_le.mpr hn
  _ < ↑n + 1 := lt_add_one _
  _ ≤ |↑n + 1| := le_abs_self _
  }
  {calc
  0 < 1 := Real.zero_lt_one
  1 ≤ ↑n + 1 := by sorry -- le_add_left _ _
  _ ≤ |↑n + 1| := le_abs_self _
  }
  {exact hε }




/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  apply exercise3_3
  exact use_me
  exact exercise3_4
  intro n


  apply (div_le_div_right _).2
  exact neg_one_le_sin ↑n
  exact cast_add_one_pos n
  intro n
  apply (div_le_div_right _).2
  exact sin_le_one ↑n
  exact cast_add_one_pos n





/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
    intro n
    by_contra h
    have this : u n > l := by exact not_le.mp h
    let ε := u n - l
    have hε : ε > 0 := by exact sub_pos.mpr this
    obtain ⟨ N , hN ⟩ := h1 ε hε
    specialize hN (max n N) (Nat.le_max_right n N)
    have this : u (max n N) - l < ε := (abs_lt.1 hN).2
    have this : ε < ε := by { calc
    ε = u n - l := by rfl
    _ ≤ u (max n N) - l := by {
        apply sub_le_sub
        apply h2
        exact Nat.le_max_left n N
        exact Eq.le rfl
      }
    _ < ε := this
    }
    exact LT.lt.false this










/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
    ext y
    constructor
    intro ⟨ hy1 , hy2 ⟩
    obtain ⟨ x , hx1 , hx2 ⟩ := hy1
    subst hx2
    apply mem_image_of_mem
    constructor
    exact hx1
    exact hy2

    intro ⟨x , hx1 , hx2⟩
    constructor
    use x
    exact ⟨ hx1.1 , hx2⟩
    rw [← hx2]
    exact hx1.2




lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
    ext x
    constructor
    intro hx
    simp
    by_contra contra

    have this : |x^2| < 2^2 := by
        rw [abs_pow x 2]
        have this : |x| * |x| < 2 * 2 := by
          apply strictMonoOn_mul_self
          simp
          simp
          exact zero_le_two

        rw [@sq_lt_sq]

    have this : |x^2| < |x^2|:= by {
      calc
      |x^2| < 2^2 := this
      _ = 4 := by ring
      _ ≤ |x^2| := by simp ; exact hx
    }
    exact LT.lt.false this
    intro hx
    simp
    have this : |x| ≥  2 := by {
      obtain hp|hq := hx
      have this : -x ≥ 2 := le_neg.mpr hp
      {calc
        2 ≤ -x := this
        _ ≤ |-x| := le_abs_self (-x)
        |-x| = |x| := abs_neg x
      }
      trans x
      exact le_abs_self x
      exact hq
    }
    calc
      4 = 2 * 2 := by ring
      _ ≤ |x| * |x| := by {
       apply mul_le_mul
       exact this
       exact this
       exact zero_le_two
       exact abs_nonneg x
      }
      _ = x^2 := by {
        have this : ∀ x : ℝ , x ≥ 0 → |x| * |x| = x^2 := by {
        intro x hx
        trans x * x
        exact abs_mul_abs_self x
        ring
        }
        by_cases q : x ≥ 0
        exact this x q


        have as : -x ≥0 := by
          apply neg_nonneg.mpr
          apply le_of_lt
          exact not_le.mp q


        calc
        |x| * |x| = |-x| * |-x| := by rw [@abs_neg]
        _ = (-x)^2 := this (-x) as
        _ = x^2 := by exact neg_sq x

      }
















/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ sorry
  let R : Set γ → Set α × Set β :=
    fun s ↦ sorry
  sorry
