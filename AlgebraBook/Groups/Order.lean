import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Automation
import AlgebraBook.FiniteCardinality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "유한군과 위수" =>

%%%
tag := "group-order"
file := "order"
%%%

지금까지 군의 법칙과 구체적인 연산을 다루었다. 이제 원소 집합의 크기를 군에 적용하여 유한군과 위수를 정의하자. 군론으로 먼저 진행했다면 {ref "relations"}[동치관계와 몫집합]과 {ref "cardinality"}[집합의 크기와 유한성]을 읽은 뒤 이 절로 돌아오라.

```savedImport
import AlgebraBook.Groups.Automation
import AlgebraBook.FiniteCardinality
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample
variable {A B C : Type} {m n : Nat}
local infixr:90 (priority := high) " ∘ " => compose
```

# 군의 위수
%%%
tag := "cardinality-group-order"
file := "group-order"
%%%

군에는 원소들의 집합과 그 위의 연산이 주어진다.
{ref "cardinality"}[집합의 크기]에서 정의한 유한성과 원소 수를 이 집합에 적용하자.

*정의* 원소들의 집합이 유한한 군을 *유한군*이라고 하고 무한한 군을 *무한군*이라고 한다.
군의 원소 집합의 기수를 군의 *위수*라고 하며 $`|G|`로 나타낸다.
특히 유한군의 위수는 그 원소의 수인 자연수이다.

`G : Group A`에서 원소들의 타입은 `A`이므로 `IsFinite A`가 유한군의 조건이다.
이를 전제로 유한군의 위수를 자연수로 정의하자.

```savedLean
def IsFiniteGroup : Group A → Prop := fun _G => IsFinite A
noncomputable def groupOrder (G : Group A)
    (hG : IsFiniteGroup G) : Nat :=
  cardinality A hG
```

`groupOrder G hG`는 유한성의 증명 `hG`를 받아 `A`의 원소 수를 구한다.

## 위수의 양수성
%%%
tag := "cardinality-positive-order"
%%%

*정리* 유한군의 위수는 $`0`보다 크다.

*증명* 군에는 항등원이 있으므로 원소 집합이 비어 있지 않다.
위수를 $`n`이라 하고 군에서 `Fin n`으로 가는 전단사를 택하면
항등원의 함수값으로 번호 $`i`를 얻는다.
$`0\leq i<n`이므로 $`0<n`이다.

Lean에서는 항등원에 붙인 번호의 범위 조건을 `suffices`로 먼저 목표로 삼자.
번호의 값은 자연수이므로 그 값보다 위수가 크면 위수는 양수이다.

```savedLean
theorem groupOrder_pos (G : Group A)
    (hG : IsFiniteGroup G) :
    0 < groupOrder G hG := by
  have hCard : cardinal A = groupOrder G hG :=
    cardinality_spec A hG
  -- 항등원을 유한한 번호로 옮기면 원소 수보다 작은 번호를 얻는다.
  unpack (cardinal_eq_iff _ _).mp hCard with ⟨f, hf⟩
  suffices bound : (f G.id).val < groupOrder G hG by
    arith

  exact (f G.id).isLt
```

`cardinality_spec`으로 위수에 관한 기수의 등식을 얻고
`cardinal_eq_iff`로 그 등식을 위수만큼의 번호를 붙이는 전단사의 존재로 바꾼다.
함수값 `f G.id`는 항등원에 대응하는 번호이다.
`by arith`로 연결을 증명하면 번호의 범위 조건이 새 목표로 남으며 `(f G.id).isLt`가 그 증명이다.
연결 증명을 적는 방법과 더 많은 예는 {ref "tactic-suffices-search"}[새 목표의 지정]을 참고하라.

원소 타입이 `Fin n`인 군에서는 `cardinal_fin n`에 따라 위수가 $`n`이다.

```savedLean
theorem groupOrder_fin (n : Nat) (G : Group (Fin n)) :
    groupOrder G (fin_isFinite n) = n := by
  exact cardinality_eq (fin_isFinite n) (cardinal_fin n)
```

## 정수의 덧셈군의 무한성
%%%
tag := "cardinality-infinite-integer-group"
%%%

자연수를 같은 값의 정수로 보내는 함수는 단사이다.
따라서 정수 전체는 무한집합이며 앞에서 구성한 정수의 덧셈군은 무한군이다.

정수로 바꾼 두 자연수가 같으면 원래 자연수도 같다.
가정 `hxy`에서 `indisc`으로 이 비교를 얻어 단사성을 증명하자.

```savedLean
theorem intAdditionGroup_infinite :
    ¬ IsFiniteGroup intAdditionGroup := by
  apply infinite_of_nat_injection (fun n : Nat => (n : Int))
  intro x y hxy
  expand at hxy
  indisc at hxy
  arith
```

이 증명에서는 `infinite_of_nat_injection`에 자연수에서 정수로 가는 함수를 제시한다.
남은 단사성의 목표에서는 `expand at hxy`로 함수값의 가정을 펼친 뒤
`indisc at hxy`로 얻은 자연수의 등식에 `arith`를 적용하여 증명을 마친다.

# 두 원소 군의 위수
%%%
tag := "group-two-element-cardinality"
file := "cardinality"
%%%

두 값이라는 설명을 준비 장의 기수와 연결해 보자. `Fin 2`의 번호 $`0`을 `false`로, 번호 $`1`을 `true`로 보내는 함수를 정의한다.

```savedLean
def boolEnumeration (i : Fin 2) : Bool := if i.val = 0
  then false else true
```

이 함수의 단사성을 보일 때는 두 번호가 $`0`인지에 따라 나눈다. 양쪽 모두 $`0`이 아니면 $`2`보다 작은 자연수이므로 모두 $`1`이다. 전사성은 주어진 값이 `false`이면 번호 $`0`, `true`이면 번호 $`1`을 택하면 된다.

```savedLean
theorem boolEnumeration_bijective :
    Bijective boolEnumeration := by
  constructor
  · intro i j h
    have hi : i.val < 2 := i.isLt
    have hj : j.val < 2 := j.isLt

    -- 두 번호가 0인지에 따라 함수값을 비교한다.
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0

      · ext
        arith

      · rw [boolEnumeration, ite_eq_left hi0,
          boolEnumeration, ite_eq_right hj0] at h

        contradiction

    · by_cases hj0 : j.val = 0

      · rw [boolEnumeration, ite_eq_right hi0,
          boolEnumeration, ite_eq_left hj0] at h

        contradiction

      · ext
        arith

  · intro b
    cases b with
    | false =>
        exists ({ val := 0, isLt := by decide } : Fin 2)

    | true =>
        exists ({ val := 1, isLt := by decide } : Fin 2)
```

이 전단사를 사용하면 `Bool`의 원소 수를 기수의 등식으로 나타낼 수 있다.

```savedLean
theorem bool_cardinal : cardinal Bool = 2 := by
  symm
  ext
  exists boolEnumeration
  exact boolEnumeration_bijective
```

`symm`으로 $`2=\operatorname{cardinal}(\mathrm{Bool})`을 목표로 삼고 `ext`를 쓰면
`Fin 2`에서 `Bool`로 가는 전단사를 제시하는 목표가 된다.
앞에서 구성한 `boolEnumeration`과 그 전단사성의 증명을 사용한다.

이 원소 수로 유한성의 증명을 얻으면 앞에서 정의한 군의 위수도 $`2`이다.

```savedLean
theorem twoElementGroup_order :
    groupOrder twoElementGroup
      (isFinite_of_cardinal_eq bool_cardinal) = 2 := by
  exact cardinality_eq _ bool_cardinal
```

# 연습문제
%%%
tag := "group-order-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* 두 유한군의 원소 집합 사이에 전단사가 있으면 두 군의 위수가 같음을 증명하라.

```savedLean -keep
theorem exercise_groupOrder_equal
    (G : Group A) (H : Group B)
    (hG : IsFiniteGroup G)
    (hH : IsFiniteGroup H)
    (hAB : cardinal A = cardinal B) :
    groupOrder G hG = groupOrder H hH := by
  sorry
```

*힌트* `cardinality_spec`으로 각 위수가 해당 집합의 원소 수임을 확인하라.
기수의 등식으로 한쪽의 원소 수를 다른 쪽으로 옮긴 뒤 `finite_cardinal_unique`로 비교하라.

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
