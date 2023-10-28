import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  intro as
  obtain ⟨x , hx ⟩ := as
  obtain hp|hq := hx
  left
  use x
  right
  use x


  intro as
  obtain hp|hq := as
  obtain ⟨ x , hx ⟩ := hp
  use x
  left
  assumption

  obtain ⟨ x , hx ⟩ := hq
  use x
  right
  assumption








    }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
lemma ex : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  intro z
  obtain ⟨x , hx ⟩ := h z
  use f x
  exact hx
/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  exact exercise2_2
  intro hg
  intro z
  obtain ⟨y , hy⟩ := hg z
  obtain ⟨x , hx⟩ := hf y
  use x
  rw [ex , hx , hy]

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
  SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  intro y
  obtain ⟨x' , hx'⟩ := hf ((y - 1) / 2 )
  use x' / 3 - 4
  ring
  rw [hx']
  ring

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  exact mul_le_mul hn (Nat.le_refl (s n)) (Nat.zero_le ( s n)) (Nat.zero_le n)

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro l
  obtain ⟨ N₁ , hN₁ ⟩ := h₁ l
  obtain ⟨ N₂ , hN₂ ⟩ := h₂ l
  use max N₁ N₂
  intro n hn
  have pf :l * t₁ n ≤ s₁ n := hN₁ n ((useful_fact N₁ N₂ n).1 hn).1
  have qf :l * t₂ n ≤ s₂ n := hN₂ n ((useful_fact N₁ N₂ n).1 hn).2
  calc l * (t₁ n + t₂ n)
    = l * t₁ n + l * t₂ n := left_distrib _ _ _
  _  ≤ s₁ n + s₂ n := by exact Nat.add_le_add pf qf





/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/

lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use factorial
  constructor
  intro k
  use k - 1
  intro n hn
  exact mul_le_mul_right (n !) (le_add_of_sub_le hn)
  intro n
  induction n with
  | zero => exact one_ne_zero
  | succ i hi => exact Nat.mul_ne_zero (succ_ne_zero i) hi


}




/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact le_pred_of_lt hn
  · have : 1 ≤ n := by exact one_le_of_lt hn
    exact Nat.sub_add_cancel this

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)

  obtain ⟨ N , hN ⟩    := hs 2
  intro k
  use N + k
  induction k with
  | zero =>
    intro n hn
    exact Nat.zero_le (s n)
  | succ j hj =>
  intro n hn
  induction n with
  | zero => calc
    s zero ≥ zero := by exact Nat.zero_le (s zero)
    _ ≥ N + _ := hn
    _ ≥ succ j := by exact Nat.le_add_left _ N
  | succ i hi =>
      have this : s i ≥ j := by
        apply hj i
        exact lt_succ.mp hn
      have helper : i ≥ N  := by
        apply lt_succ.mp
        calc
        succ i ≥ N + succ j := hn
        _ = succ N + j := by
          symm
          exact succ_add _ _
        _ ≥ succ N := le_add_right (succ N) _
      calc
       s (succ i)
          ≥ 2 * s i := hN i helper
       _  ≥  s i + 1 := add_one_le_two_mul (h3s _)
       _  ≥ succ j := le_add_of_sub_le this


end Growth