import AlgebraBook.FiniteCardinality
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.FiniteCardinality

theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry

theorem exercise_finite_cardinal_transport {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry

theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
  sorry

theorem exercise_infinite_transport {A B : Type}
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  sorry

theorem exercise_cardinal_product {A B : Type} {m n : Nat}
    (hA : cardinal A = m)
    (hB : cardinal B = n) :
    cardinal (A × B) = m * n := by
  sorry

-- 문제 6: 두 원소 집합의 번호
-- 집합 \{2,3\}의 두 원소에 각각 번호 0, 1을 붙인다.
-- 아래 함수가 전단사임을 증명한 뒤 그 결과로 집합의 원소 수가 2임을 보이라.
def practiceIndexTwo (i : Fin 2) : Elem twoThree :=
  { val := i.val + 2
    property := by
      expand
      arith }

theorem exercise_indexTwo_bijective :
    Bijective practiceIndexTwo := by
  sorry

theorem exercise_twoThree_cardinal :
    cardinal (Elem twoThree) = 2 := by
  sorry

-- 문제 7: 색과 번호의 조합
-- (1) 두 성분을 바꾸는 함수를 사용하여 |A\times B|=|B\times A|임을 증명하라.
-- (2) 두 가지 색 중 하나와 세 가지 번호 중 하나를 고르는 방법이 모두 여섯 가지임을 보이라.
-- 색과 번호를 각각 Fin 2, Fin 3으로 나타낸다.
-- (3) 앞의 두 결과를 사용하여 번호와 색의 순서로 나열해도 조합의 수는 같음을 보이라.
theorem exercise_cardinal_swap (A B : Type) :
    cardinal (A × B) = cardinal (B × A) := by
  sorry

theorem exercise_two_by_three_cardinal :
    cardinal (Fin 2 × Fin 3) = 6 := by
  sorry

theorem exercise_three_by_two_cardinal :
    cardinal (Fin 3 × Fin 2) = 6 := by
  sorry

-- 문제 8: 같은 달에 태어난 두 사람
-- (1) n+1개의 번호를 n개의 번호로 보내는 함수에서는
-- 서로 다른 두 번호의 함수값이 같음을 증명하라.
-- (2) 열세 사람에게 태어난 달을 대응시키면 같은 달에 태어난 두 사람이 있음을 첫 결과로 보이라.
-- 사람과 달을 각각 Fin 13, Fin 12로 나타낸다.
theorem exercise_fin_collision (n : Nat)
    (f : Fin (n + 1) → Fin n) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  sorry

theorem exercise_birth_month_collision
    (month : Fin 13 → Fin 12) :
    ∃ i j, i ≠ j ∧ month i = month j := by
  sorry

-- 문제 9: 서로 다른 원소 수
-- (1) Fin 2와 Fin 3 사이에는 전단사가 존재하지 않음을 증명하라.
-- (2) 본문에서 센 집합 \{10,11,12\}의 원소 수가 4일 수 없음을 보이라.
-- 원소 수의 유일성에 관한 정리들을 사용하라.
theorem exercise_fin_two_three_not_same :
    ¬ SameCardinality (Fin 2) (Fin 3) := by
  sorry

theorem exercise_threeNumbers_not_four :
    cardinal (Elem threeNumbers) ≠ 4 := by
  sorry

end Exercises.FiniteCardinality
