import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

import LeanCourse.Project.FiberedCategories
import LeanCourse.Project.Cleavage
import LeanCourse.Project.Split
import LeanCourse.Project.PreSheavesOfCategories
import LeanCourse.Project.DiscreteFibration

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
lemma splitFromDiscrete {P : fibration} (q : isDiscrete P) : splitFibration B := by sorry
def Sp (P : fibration B) : splitFibration B := by sorry
