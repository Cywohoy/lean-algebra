import AlgebraBook.Proofs
import AlgebraBook.Tactic.Auto

/-!
증명의 구성과 사용: 연습문제
각 sorry를 자신의 증명으로 바꾸어 완성하라.
-/

open ProofExamples
open scoped Ample.Auto

namespace Exercises.Proofs

-- 문제 1: Nat.add_lt_add_right로 양변에 3을 더한 부등식을 증명하라.
theorem exercise_add_three_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  sorry

-- 문제 2: P, P → Q, Q → R에서 R을 얻으라.
theorem exercise_implication_chain
    (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  sorry

-- 문제 3: 모든 원소에서 성립하는 관계를 a와 b에서 사용하라.
theorem exercise_relation_specialization
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry

-- 문제 4: 각 원소에서 주어진 함의를 사용하여 전칭명제를 증명하라.
theorem exercise_forall_implication
    (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  sorry

-- 문제 5: 대소 관계를 보존하는 함수
-- 자연수 함수 f, g가 각각 a<b이면 f(a)<f(b), g(a)<g(b)를 만족한다고 하자.
-- (1) a<b이면 g(f(a))<g(f(b))임을 증명하라.
-- (2) 첫 결과와 comparisonProof를 사용하여 g(f(3))<g(f(5))를 보이라.
theorem exercise_increasing_composition (f g : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b)
    (hg : ∀ a b, a < b → g a < g b) :
    ∀ a b, a < b → g (f a) < g (f b) := by
  sorry

theorem exercise_increasing_at_three_five
    (f g : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b)
    (hg : ∀ a b, a < b → g a < g b) :
    g (f 3) < g (f 5) := by
  sorry

-- 문제 6: 함수값의 범위
-- 모든 자연수 n에 대하여 f(n)<g(n)이고 g(n)<n+10이라고 하자.
-- f(3)<13임을 증명하라.
-- 부등식의 추이성은 Nat.lt_trans로 사용할 수 있으며,
-- 이 정리는 a<b와 b<c의 증명을 받아 a<c의 증명을 돌려준다.
theorem exercise_function_bound (f g : Nat → Nat)
    (hfg : ∀ n, f n < g n)
    (hg : ∀ n, g n < n + 10) :
    f 3 < 13 := by
  sorry

-- 문제 7: 부등식과 연속된 덧셈
-- (1) a<b이면 임의의 자연수 c에 대하여 a+c<b+c임을 증명하라.
-- (2) 첫 결과를 두 번 사용하여 (a+c)+d<(b+c)+d를 보이라.
theorem exercise_shift_lt (a b c : Nat)
    (hab : a < b) :
    a + c < b + c := by
  sorry

theorem exercise_two_shifts_lt (a b c d : Nat)
    (hab : a < b) :
    (a + c) + d < (b + c) + d := by
  sorry

-- 문제 8: 반복하여 유지되는 조건
-- 함수 f:A\to A가 조건 P를 유지한다고 하자.
-- 즉 P(x)이면 P(f(x))이다.
-- (1) P(x)이면 P(f(f(x)))임을 증명하라.
-- (2) 첫 결과를 사용하여 f를 네 번 적용한 뒤에도 P가 성립함을 보이라.
theorem exercise_property_twice (A : Type)
    (P : A → Prop) (f : A → A)
    (hf : ∀ x, P x → P (f x)) :
    ∀ x, P x → P (f (f x)) := by
  sorry

theorem exercise_property_four_times (A : Type)
    (P : A → Prop) (f : A → A)
    (hf : ∀ x, P x → P (f x)) :
    ∀ x, P x → P (f (f (f (f x)))) := by
  sorry

end Exercises.Proofs
