import AlgebraBook.Relations
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.Relations
variable {A B C : Type} {m n : Nat}

theorem exercise_mem_own_equivalenceClass
    (R : Relation A)
    (hR : IsEquivalence R)
    (a : A) :
    a ∈ equivalenceClass R a := by
  sorry

theorem exercise_equal_values_equivalence (f : A → B) :
    IsEquivalence (fun x y : A => f x = f y) := by
  sorry

theorem exercise_relation_of_classes_equal
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : equivalenceClass R a = equivalenceClass R b) :
    R a b := by
  sorry

-- 문제 4: 첫 등식과 parityClass_zero_ne_one을 사용하라.
theorem exercise_parityClass_three_one :
    parityClass 3 = parityClass 1 := by
  sorry

theorem exercise_parityClass_three_ne_zero :
    parityClass 3 ≠ parityClass 0 := by
  sorry

-- 문제 5: 첫 좌표가 같은 점들
-- 두 좌표가 모두 정수인 점들 사이에 첫 좌표가 같다는 관계를 정의한다.
-- (1) 이 관계가 동치관계임을 증명하라.
-- (2) (a,b)의 동치류가 첫 좌표가 a인 점들의 집합임을 보이라.
-- (3) 첫 결과와 equivalenceClass_eq를 사용하여 (2,3)과 (2,-5)의 동치류가 같음을 보이라.
def practiceSameFirst : Relation (Int × Int) :=
  fun p q => p.1 = q.1
theorem exercise_sameFirst_equivalence :
    IsEquivalence practiceSameFirst := by
  sorry

theorem exercise_sameFirst_class (a b : Int) :
    equivalenceClass practiceSameFirst (a, b) =
      (fun p => p.1 = a) := by
  sorry

theorem exercise_vertical_class :
    equivalenceClass practiceSameFirst (2, 3) =
      equivalenceClass practiceSameFirst (2, -5) := by
  sorry

-- 문제 6: 겹치는 동치류
-- (1) 동치관계의 두 동치류가 공통 원소를 가지면 두 동치류가 같음을 증명하라.
-- (2) 6을 법으로 하는 합동에서 2가 8과 20의 동치류에 모두 속함을 보이라.
-- (3) 앞의 두 결과를 사용하여 두 동치류가 같음을 보이라.
theorem exercise_classes_of_common_element
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : ∃ x, x ∈ equivalenceClass R a ∧
      x ∈ equivalenceClass R b) :
    equivalenceClass R a = equivalenceClass R b := by
  sorry

theorem exercise_mod_six_common :
    ∃ x, x ∈ equivalenceClass (Congruent 6) 8 ∧
      x ∈ equivalenceClass (Congruent 6) 20 := by
  sorry

theorem exercise_mod_six_classes :
    equivalenceClass (Congruent 6) 8 =
      equivalenceClass (Congruent 6) 20 := by
  sorry

-- 문제 7: 대표원에 따라 달라지는 값
-- 모든 정수 a에 대하여 F([a])=a\bmod3을 만족하는 함수 F:\operatorname{Parity}\to\mathbb{Z}는 존재하지 않음을 증명하라.
-- 여기서 [a]는 2를 법으로 한 동치류이다.
-- 같은 동치류에 속하지만 3으로 나눈 나머지가 다른 두 정수를 찾으라.
theorem exercise_parity_no_mod_three :
    ¬ ∃ F : Parity → Int,
      ∀ a, F (parityClass a) = a % 3 := by
  sorry

-- 문제 8: 짝수 동치류와 홀수 동치류의 교환
-- 동치류 [a]에 [a+1]을 대응시키는 함수를 구성한다.
-- (1) a\equiv b\pmod2이면 [a+1]=[b+1]임을 증명하여 대표원에 무관함을 확인하라.
-- (2) 이 증명을 사용한 아래 함수의 계산 규칙을 증명하라.
-- (3) 이 함수를 두 번 적용하면 원래 몫 원소를 얻음을 보이라.
theorem exercise_nextParity_respects (a b : Int)
    (hab : Congruent 2 a b) :
    parityClass (a + 1) = parityClass (b + 1) := by
  sorry

noncomputable def practiceNextParity : Parity → Parity :=
  quotientLift (Congruent 2) (congruent_equivalence 2)
    (fun a => parityClass (a + 1))
    exercise_nextParity_respects
theorem exercise_nextParity_class (a : Int) :
    practiceNextParity (parityClass a) =
      parityClass (a + 1) := by
  sorry

theorem exercise_nextParity_twice (q : Parity) :
    practiceNextParity (practiceNextParity q) = q := by
  sorry

end Exercises.Relations
