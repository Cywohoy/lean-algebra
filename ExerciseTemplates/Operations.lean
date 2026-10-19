import AlgebraBook.Operations
import AlgebraBook.Tactic.Auto

/-!
이항연산: 연습문제
각 sorry를 자신의 증명으로 바꾸어 완성하라.
-/

open Ample
open scoped Ample.Auto
open scoped Classical

namespace Exercises.Operations

variable {A : Type}

-- 문제 1: 첫 원소를 택하는 연산은 결합적이며 교환적이지 않다.
theorem exercise_leftProjection_associative :
    Associative (fun a _ : Nat => a) := by
  sorry

theorem exercise_leftProjection_not_commutative :
    ¬ Commutative (fun a _ : Nat => a) := by
  sorry

-- 문제 2: 좌항등원과 우항등원은 같다.
theorem exercise_left_right_identity_eq
    (op : BinaryOp A) (e u : A)
    (he : IsLeftIdentity op e)
    (hu : IsRightIdentity op u) :
    e = u := by
  sorry

-- 문제 3: b가 a의 역원이면 a도 b의 역원이다.
theorem exercise_inverse_symm
    (op : BinaryOp A) (e : A)
    (he : IsIdentity op e)
    (a b : A)
    (h : IsInverse op e he a b) :
    IsInverse op e he b a := by
  sorry

end Exercises.Operations
