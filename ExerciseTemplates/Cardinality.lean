import AlgebraBook.Cardinality
import AlgebraBook.Tactic.Auto

/-! 유한성과 무한집합의 연습문제를 함께 모은 파일이다. -/

open Course
open scoped Course.Auto Classical
namespace Exercises.Cardinality
variable {A B C : Type} {m n : Nat}

theorem exercise_singletons_same_cardinal (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry

theorem exercise_finite_cardinal_transport
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry

theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
  sorry

theorem exercise_infinite_transport
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  sorry

theorem exercise_cardinal_product
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

end Exercises.Cardinality
