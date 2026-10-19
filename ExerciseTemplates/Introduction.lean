import AlgebraBook.Introduction
import AlgebraBook.Tactic.Auto

open IntroExamples
open scoped Ample.Auto

namespace Exercises.Introduction

-- 문제 1: 함수의 일부 인수
-- rectangleArea 3에 4를 넣은 값과 areaWithWidthThree 4의 값이 같음을 확인하고,
-- 그 값이 12임을 증명하라.
theorem exercise_partial_area :
    areaWithWidthThree 4 = rectangleArea 3 4 := by
  sorry

theorem exercise_area_value :
    areaWithWidthThree 4 = 12 := by
  sorry

-- 문제 2: 술어와 그 증명
-- 먼저 4\cdot4=16을 확인하고, 이 증명으로 4가 방정식 n^2=16의 해임을 보이라.
-- 이어서 h : solvesSquare a n이 주어졌을 때 이 증명을 사용하여 n\cdot n=a를 보이라.
-- 마지막 증명에서는 a와 n의 구체적인 값이 주어지지 않는다.
theorem exercise_four_square : 4 * 4 = 16 := by
  sorry

theorem exercise_four_solves_square :
    solvesSquare 16 4 := by
  sorry

theorem exercise_square_proof (a n : Nat)
    (h : solvesSquare a n) :
    n * n = a := by
  sorry

end Exercises.Introduction
