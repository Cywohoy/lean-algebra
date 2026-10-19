import AlgebraBook.InfiniteCardinality
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Course
open scoped Course.Auto Classical
namespace Exercises.InfiniteCardinality
variable {A B C : Type} {m n : Nat}

-- Advanced 보조정리, 문제 1: 무한집합 A로 가는 단사함수 f : Fin n → A가 주어졌다고 하자.
-- f의 상에 속하지 않는 원소가 A에 존재함을 증명하라.
theorem fresh_element_exists
    (hA : IsInfinite A)
    (f : Fin n → A)
    (hf : Injective f) :
    ∃ a : A, ∀ i : Fin n, f i ≠ a := by
  sorry

-- Advanced 보조정리, 문제 2: 무한집합 A의 유한한 목록에 새 원소를 하나 덧붙여
-- 기존 번호의 함수값을 보존하는 목록을 만들 수 있음을 증명하라.
theorem finite_listing_extension
    (hA : IsInfinite A)
    (s : FiniteListing A n) :
    ∃ t : FiniteListing A (n + 1),
      ∀ i : Fin n, t.val i.castSucc = s.val i := by
  sorry

theorem exercise_from_two_countably_infinite :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
  sorry

theorem exercise_powerSet_inter (S T : Set A) :
    powerSet (S ∩ T) = powerSet S ∩ powerSet T := by
  sorry

-- 문제 3: 등차수열과 가산무한집합
-- 집합 S=\{1,4,7,10,\ldots\}을 3k+1 꼴의 자연수로 정의한다.
-- (1) 아래 함수가 자연수에서 S의 원소 타입으로 가는 전단사임을 증명하라.
-- (2) 첫 결과로 S가 가산무한집합임을 보이라.
-- (3) S가 자연수 전체와 같은 집합은 아님을 보이라.
-- 집합의 같음과 크기의 같음을 구별하라.
def practiceOneModThree : Set Nat :=
  fun n => ∃ k, n = 3 * k + 1
def practiceToOneModThree (n : Nat) :
    Elem practiceOneModThree :=
  { val := 3 * n + 1
    property := by exists n }

theorem exercise_oneModThree_bijective :
    Bijective practiceToOneModThree := by
  sorry

theorem exercise_oneModThree_countable :
    IsCountablyInfinite (Elem practiceOneModThree) := by
  sorry

theorem exercise_oneModThree_ne_whole :
    practiceOneModThree ≠ whole Nat := by
  sorry

-- 문제 4: 순서쌍 집합의 무한성
-- 자연수의 순서쌍 전체가 무한집합임을 증명하라.
-- 자연수에서 오는 단사함수를 하나 구성하여 infinite_of_nat_injection을 사용하라.
-- 선택한 함수가 전사일 필요가 없는 이유도 설명하라.
theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry

-- 문제 5: 멱집합의 포함 관계
-- (1) S\subseteq T이면 \mathcal{P}(S)\subseteq\mathcal{P}(T)임을 증명하라.
-- (2) 반대 방향도 증명하여 이 두 포함 관계가 동치임을 보이라.
-- (3) 첫 결과와 twoThree_subset_positives를 사용하여
-- \mathcal{P}(\{2,3\})\subseteq\mathcal{P}(\mathbb{N}_{>0})임을 보이라.
theorem exercise_powerSet_mono (S T : Set A)
    (hST : S ⊆ T) :
    powerSet S ⊆ powerSet T := by
  sorry

theorem exercise_powerSet_subset_iff (S T : Set A) :
    powerSet S ⊆ powerSet T ↔ S ⊆ T := by
  sorry

theorem exercise_powerSet_twoThree_positives :
    powerSet twoThree ⊆ powerSet positives := by
  sorry

-- 문제 6: 한 원소 집합들을 나열한 경우
-- f(n)=\{n\}으로 부분집합들을 나열하자.
-- (1) 이 나열의 대각선 집합 D=\{n:n\notin f(n)\}이 공집합임을 보이라.
-- (2) 공집합이 이 함수의 상에 속하지 않음을 직접 증명하라.
-- (3) 둘째 결과로 이 함수가 전사가 아님을 보이라.
def practiceSingletonDiagonal : Set Nat :=
  fun n => n ∉ singleton n
theorem exercise_singleton_diagonal_empty :
    practiceSingletonDiagonal = ∅ := by
  sorry

theorem exercise_empty_not_singleton_image :
    (∅ : Set Nat) ∉ image singleton (whole Nat) := by
  sorry

theorem exercise_singleton_not_surjective :
    ¬ Surjective (singleton : Nat → Set Nat) := by
  sorry

end Exercises.InfiniteCardinality
