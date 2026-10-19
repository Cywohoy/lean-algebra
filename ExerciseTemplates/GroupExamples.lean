import AlgebraBook.Groups.Permutations
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Course
open scoped Course.Auto Classical
namespace Exercises.GroupExamples
variable {A B C : Type} {m n : Nat}

-- 2.3 역원과 곱의 계산

theorem exercise_op_reverse_identity (G : Group A) (a b : A)
    (h : G.op a b = G.id) :
    G.op b a = G.id := by
  sorry

theorem exercise_conjugate_identity (G : Group A) (a x : A)
    (h : G.op (G.op a x) (G.inv a) = G.id) :
    x = G.id := by
  sorry

theorem exercise_inverse_injective (G : Group A) (a b : A)
    (h : G.inv a = G.inv b) :
    a = b := by
  sorry

-- 2.4 거듭제곱

theorem exercise_power_identity (G : Group A) (n : Nat) :
    power G G.id n = G.id := by
  sorry

theorem exercise_square_identity_abelian (G : Group A)
    (h : ∀ a : A, G.op a a = G.id) :
    IsAbelian G := by
  sorry

theorem exercise_power_commuting_element
    (G : Group A) (a b : A)
    (hab : G.op a b = G.op b a)
    (n : Nat) :
    G.op (power G a n) b = G.op b (power G a n) := by
  sorry

theorem exercise_bool_power_even (n : Nat) :
    power twoElementGroup true (2 * n) = false := by
  sorry

theorem exercise_bool_power_odd (n : Nat) :
    power twoElementGroup true (2 * n + 1) = true := by
  sorry

theorem exercise_bool_inverse (b : Bool) :
    twoElementGroup.inv b = b := by
  sorry

theorem exercise_bool_cube (b : Bool) :
    power twoElementGroup b 3 = b := by
  sorry

-- 2.5 군의 곱

theorem exercise_product_abelian_factors
    (G : Group A) (H : Group B)
    (h : IsAbelian (productGroup G H)) :
    IsAbelian G ∧ IsAbelian H := by
  sorry

theorem exercise_product_power (G : Group A) (H : Group B)
    (a : A) (b : B) (n : Nat) :
    power (productGroup G H) (a, b) n =
      (power G a n, power H b n) := by
  sorry

-- 2.6 순열군

theorem exercise_transposition_square :
    power (permutationGroup (Fin 3)) transposition01 2 =
      permutationIdentity (Fin 3) := by
  sorry

theorem exercise_threeCycle_cube :
    power (permutationGroup (Fin 3)) threeCycle 3 =
      permutationIdentity (Fin 3) := by
  sorry

theorem exercise_threeCycle_inverse :
    (permutationGroup (Fin 3)).inv threeCycle =
      power (permutationGroup (Fin 3)) threeCycle 2 := by
  sorry

end Exercises.GroupExamples
