import AlgebraBook.Groups.Order
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.GroupOrder
variable {A B C : Type} {m n : Nat}

theorem exercise_groupOrder_equal
    (G : Group A) (H : Group B)
    (hG : IsFiniteGroup G)
    (hH : IsFiniteGroup H)
    (hAB : cardinal A = cardinal B) :
    groupOrder G hG = groupOrder H hH := by
  sorry

end Exercises.GroupOrder
