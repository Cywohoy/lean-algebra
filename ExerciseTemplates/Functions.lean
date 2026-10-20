import AlgebraBook.Functions
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.Functions

-- 문제 1
theorem exercise_preimage_subset {A B : Type}
    (f : A → B) (S T : Set B)
    (hST : S ⊆ T) :
    preimage f S ⊆ preimage f T := by
  sorry

-- 문제 2: 두 원소 집합의 상과 역상
-- (1) \operatorname{double}(\{2,3\})=\{4,6\}임을 증명하라.
-- (2) 첫 결과와 preimage_image_of_injective를 사용하여
-- \operatorname{double}^{-1}(\{4,6\})=\{2,3\}임을 보이라.
def practiceFourSix : Set Nat := fun n => n = 4 ∨ n = 6

theorem exercise_image_double_twoThree :
    image double twoThree = practiceFourSix := by
  sorry

theorem exercise_preimage_double_fourSix :
    preimage double practiceFourSix = twoThree := by
  sorry

-- 문제 3
theorem exercise_double_after_successor_at_three {n : Nat} :
    (double ∘ (fun n : Nat => n + 1)) 3 = 8 := by
  sorry

theorem exercise_successor_after_double_at_three {n : Nat} :
    ((fun n : Nat => n + 1) ∘ double) 3 = 7 := by
  sorry

theorem exercise_double_successor_noncommute {n : Nat} :
    double ∘ (fun n : Nat => n + 1) ≠
    (fun n : Nat => n + 1) ∘ double := by
  sorry

-- 문제 4
theorem exercise_setProduct_swap {A B : Type}
    (S : Set A) (T : Set B) (a : A) (b : B)
    (h : (a, b) ∈ setProduct S T) :
    (b, a) ∈ setProduct T S := by
  sorry

-- 문제 5
theorem exercise_injective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Injective (g ∘ f)) :
    Injective f := by
  sorry

-- 문제 6
theorem exercise_surjective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Surjective (g ∘ f)) :
    Surjective g := by
  sorry

-- 문제 7
theorem exercise_inverse_inverse {A B : Type}
    (f : A → B)
    (hf : Bijective f) :
    inverseMap (inverseMap f hf)
      (inverseMap_bijective f hf) = f := by
  sorry

-- 문제 8: 좌표 함수
-- 첫 좌표를 꺼내는 함수 p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}에 대하여
-- 전사성을 증명하고 단사성이 성립하지 않음을 보이라.
-- 단사성을 반박할 때에는 함수값이 같아지는 서로 다른 두 순서쌍을 찾으라.
def practiceFirst : Nat × Nat → Nat := fun p => p.1

theorem exercise_first_surjective :
    Surjective practiceFirst := by
  sorry

theorem exercise_first_not_injective :
    ¬ Injective practiceFirst := by
  sorry

-- 문제 9: 대각선 함수
-- d(n)=(n,n)으로 정한 함수 d:\mathbb{N}\to\mathbb{N}\times\mathbb{N}의 단사성을 증명하라.
-- 또한 이 함수는 전사가 아님을 증명하라.
def practiceDiagonal : Nat → Nat × Nat := fun n => (n, n)

theorem exercise_diagonal_injective :
    Injective practiceDiagonal := by
  sorry

theorem exercise_diagonal_not_surjective :
    ¬ Surjective practiceDiagonal := by
  sorry

-- 문제 10: 역상과 집합 연산
-- 역상은 교집합과 여집합을 보존한다. 다음 두 등식을 증명하라.
-- 함수의 단사성이나 전사성을 가정하지 않고 증명하라.
theorem exercise_preimage_inter {A B : Type} (f : A → B)
    (S T : Set B) :
    preimage f (S ∩ T) = preimage f S ∩ preimage f T := by
  sorry

theorem exercise_preimage_compl {A B : Type}
    (f : A → B) (T : Set B) :
    preimage f Tᶜ = (preimage f T)ᶜ := by
  sorry

-- 문제 11: 합집합의 상
-- f(S\cup T)=f(S)\cup f(T)임을 증명하라.
theorem exercise_image_union {A B : Type}
    (f : A → B) (S T : Set A) :
    image f (S ∪ T) = image f S ∪ image f T := by
  sorry

-- 문제 12: 합성에서의 소거
-- (1) 단사함수 h에 대하여 h\circ f=h\circ g이면 f=g임을 증명하라.
-- (2) 전사함수 h에 대하여 f\circ h=g\circ h이면 f=g임을 증명하라.
-- 두 증명에서 단사성과 전사성이 각각 어디에 쓰이는지 주석으로 적으라.
theorem exercise_cancel_injective {A B C : Type}
    (f g : A → B)
    (h : B → C)
    (hh : Injective h)
    (heq : h ∘ f = h ∘ g) :
    f = g := by
  sorry

theorem exercise_cancel_surjective {A B C : Type}
    (f g : B → C)
    (h : A → B)
    (hh : Surjective h)
    (heq : f ∘ h = g ∘ h) :
    f = g := by
  sorry

end Exercises.Functions
