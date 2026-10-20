import AlgebraBook.Sets
import AlgebraBook.Tactic.Auto

/-!
집합의 구성: 연습문제
각 sorry를 자신의 증명으로 바꾸어 완성하라.
-/

open Ample
open scoped Ample.Auto
open scoped Classical

namespace Exercises.Sets

-- 문제 1: 포함 관계의 추이성을 증명하라.
-- 각 단계에 대응하는 수학적 문장을 -- 주석으로 적으라.
theorem exercise_subset_trans {A : Type} (S T U : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U) :
    S ⊆ U := by
  sorry

-- 문제 2: 교집합은 두 번째 집합의 부분집합이다.
theorem exercise_inter_subset_right
    {A : Type} (S T : Set A) :
    S ∩ T ⊆ T := by
  sorry

-- 문제 3: S에서 S를 뺀 차집합은 공집합의 부분집합이다.
theorem exercise_diff_self_subset_empty
    {A : Type} (S : Set A) :
    S \ S ⊆ ∅ := by
  sorry

-- 문제 4: 차집합의 두 번째 집합이 커지면 차집합은 작아진다.
theorem exercise_diff_antitone_right
    {A : Type} (S T U : Set A)
    (hTU : T ⊆ U) :
    S \ U ⊆ S \ T := by
  sorry

-- 문제 5: 포함 관계와 합집합
-- (1) S\subseteq T이면 S\cup T=T임을 증명하라.
-- (2) 첫 결과와 본문의 twoThree_subset_positives를 사용하여
-- \{2,3\}\cup\mathbb{N}_{>0}=\mathbb{N}_{>0}임을 보이라.
theorem exercise_union_eq_right {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∪ T = T := by
  sorry

theorem exercise_twoThree_union_positives :
    twoThree ∪ positives = positives := by
  sorry

-- 문제 6: 흡수법칙
-- S\cap(S\cup T)=S임을 증명하라.
-- 원소별로 두 방향을 보인 뒤, 본문의 inter_eq_left_of_subset을 사용한 증명도 작성하라.
theorem exercise_inter_union_absorb {A : Type}
    (S T : Set A) :
    S ∩ (S ∪ T) = S := by
  sorry

-- 문제 7: 구체적인 교집합과 차집합
-- T=\{3,4\}라 하자. 앞에서 정의한 twoThree를 사용하여
-- \{2,3\}\cap T=\{3\}과 \{2,3\}\setminus T=\{2\}를 각각 증명하라.
-- 두 증명에서 3을 다루는 방식이 어떻게 다른지 비교하라.
def practiceThreeFour : Set Nat :=
  fun n => n = 3 ∨ n = 4

theorem exercise_twoThree_inter :
    twoThree ∩ practiceThreeFour = (fun n => n = 3) := by
  sorry

theorem exercise_twoThree_diff :
    twoThree \ practiceThreeFour = (fun n => n = 2) := by
  sorry

-- 문제 8: 포함 관계의 반례
-- (1) \mathbb{N}_{>0}\not\subseteq\{2,3\}임을 증명하라.
-- (2) 첫 결과를 사용하여 두 집합이 서로 다름을 보이라.
theorem exercise_positives_not_subset_twoThree :
    ¬ positives ⊆ twoThree := by
  sorry

theorem exercise_positives_ne_twoThree :
    positives ≠ twoThree := by
  sorry

-- 문제 9: 드모르간 법칙
-- (S\cup T)^{\mathsf c}=S^{\mathsf c}\cap T^{\mathsf c}임을 증명하라.
-- 원소 조건을 이용하여 합집합에 속하지 않는다는 말이 두 집합 각각에 속하지 않는다는 말과 동치임을 보이라.
theorem exercise_compl_union {A : Type} (S T : Set A) :
    (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  sorry

-- 문제 10: 공집합인 차집합
-- S\setminus T=\varnothing일 필요충분조건이 S\subseteq T임을 증명하라.
-- 힌트: S \ T = ∅에서 S ⊆ T를 보일 때는 원소 x ∈ S를 택하라.
-- x ∉ T라고 가정하면 x가 차집합에 속하여 모순이 생긴다.
theorem exercise_diff_empty_iff {A : Type}
    (S T : Set A) :
    S \ T = ∅ ↔ S ⊆ T := by
  sorry

end Exercises.Sets
