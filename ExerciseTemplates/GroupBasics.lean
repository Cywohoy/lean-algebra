import AlgebraBook.Groups.Definition
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.GroupBasics
variable {A B C : Type} {m n : Nat}
variable (G : Group A)
local infixl:70 (priority := high) " * " => G.op
local notation "e" => G.id
local postfix:max (priority := high) "⁻¹" => G.inv
theorem exercise_right_identity_unique
    (u : A)
    (hu : ∀ a : A, a * u = a) :
    u = e := by
  sorry

theorem exercise_inverse_identity : e⁻¹ = e := by
  sorry

theorem exercise_inverse_inverse_group
    (a : A) :
    (a⁻¹)⁻¹ = a := by
  sorry

theorem exercise_right_cancellation
    (a b c : A)
    (h : b * a = c * a) :
    b = c := by
  sorry

theorem exercise_solve_left_equation
    (a b x : A)
    (h : a * x = b) :
    x = a⁻¹ * b := by
  sorry

theorem exercise_left_axioms_two_sided
    (op : BinaryOp A) (u : A)
    (hassoc : Associative op)
    (hleft : IsLeftIdentity op u)
    (hinv : ∀ a : A, ∃ b : A, op b a = u) :
    IsIdentity op u ∧
      ∀ a b : A, op b a = u → op a b = u := by
  sorry

end Exercises.GroupBasics
