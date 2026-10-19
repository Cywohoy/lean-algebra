import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Powers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "군의 곱" =>

%%%
tag := "group-products"
file := "products"
%%%

두 군의 원소를 순서쌍으로 묶고 각 성분에서 연산하여 새로운 군을 만들자. 군의 법칙을 증명할 때도 두 성분을 나누어 비교한다. 이 구성을 통해 아벨성이나 원소의 제곱이 각 성분의 성질에서 어떻게 나오는지 살펴본다.

```savedImport
import AlgebraBook.Groups.Powers
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample
variable {A B : Type}
```


# 성분별 연산
%%%
tag := "group-product-definition"
file := "definition"
%%%

*정의* 두 군 $`G,H`에 대하여 집합 $`G\times H`에

$$`(a,b)(c,d)=(ac,bd),\qquad e_{G\times H}=(e_G,e_H),\qquad (a,b)^{-1}=(a^{-1},b^{-1})`

로 연산, 항등원과 역원을 정한 군을 $`G`와 $`H`의 *곱*이라고 한다.

이 연산이 군의 법칙을 만족하는지 각 성분에서 확인하자.
결합법칙의 두 식을 비교하면 첫째 성분에서는 $`(ac)f=a(cf)`를,
둘째 성분에서는 $`(bd)g=b(dg)`를 얻는다.
이는 각각 $`G`와 $`H`의 결합법칙이다.
항등원과 역원도 각 성분에서 해당 법칙을 적용하면 된다.

Lean에서는 원래 타입이 `A`와 `B`이면 새 원소의 타입은 `A × B`이다. `ext`를 쓰면 두 성분의 등식이 남으므로 각각 `G`와 `H`의 법칙으로 증명한다.

```savedLean
def productGroup (G : Group A) (H : Group B) :
    Group (A × B) where
  op x y := (G.op x.1 y.1, H.op x.2 y.2)
  id := (G.id, H.id)
  inv x := (G.inv x.1, H.inv x.2)

  -- 각 성분에서 원래 군의 결합법칙을 사용한다.
  assoc := by
    intro x y z
    ext
    · exact G.assoc x.1 y.1 z.1
    · exact H.assoc x.2 y.2 z.2

  -- 항등원과 역원의 법칙도 두 성분에서 각각 확인한다.
  id_left := by
    intro x
    ext
    · exact G.id_left x.1
    · exact H.id_left x.2

  id_right := by
    intro x
    ext
    · exact G.id_right x.1
    · exact H.id_right x.2

  inv_left := by
    intro x
    ext
    · exact G.inv_left x.1
    · exact H.inv_left x.2

  inv_right := by
    intro x
    ext
    · exact G.inv_right x.1
    · exact H.inv_right x.2
```

`assoc`의 첫 목표는 첫째 성분에서의 결합법칙이고 둘째 목표는 둘째 성분에서의 결합법칙이다. 나머지 네 법칙도 같은 방식으로 확인하므로 새로운 연산을 정의한 뒤 이미 알고 있는 군의 법칙을 그대로 사용할 수 있다.

# 아벨성과 구체적인 예
%%%
tag := "group-product-examples"
file := "examples"
%%%

*정리* 두 아벨군의 곱은 아벨군이다.

두 순서쌍의 곱을 반대 순서로 연산한 결과와 비교하면 각 성분의 교환법칙이 남는다.

```savedLean
theorem productGroup_abelian (G : Group A) (H : Group B)
    (hG : IsAbelian G)
    (hH : IsAbelian H) :
    IsAbelian (productGroup G H) := by
  intro x y
  ext
  · exact hG x.1 y.1
  · exact hH x.2 y.2
```

*보기* 두 원소 군을 두 번 곱하면 원소가 $`(e,e),(e,u),(u,e),(u,u)`인 군을 얻는다. 각 원소의 제곱은 $`(e,e)`이다.

```savedLean
def fourElementGroup : Group (Bool × Bool) :=
  productGroup twoElementGroup twoElementGroup
example :
    IsAbelian fourElementGroup := by
  exact productGroup_abelian twoElementGroup twoElementGroup
    twoElementGroup_abelian twoElementGroup_abelian

example (p : Bool × Bool) :
    fourElementGroup.op p p = fourElementGroup.id := by
  ext
  · exact twoElementGroup.inv_left p.1
  · exact twoElementGroup.inv_left p.2
```

마지막 증명에서는 두 원소 군의 역원 함수가 원래 값을 그대로 주므로 `inv_left`가 바로 제곱에 관한 등식이다. 이 군에서 항등원 이외의 세 원소는 각각 두 번 연산하면 항등원으로 돌아온다.

# 성분으로 가는 함수
%%%
tag := "group-product-projections"
file := "projections"
%%%

두 군의 곱에서 첫째 성분만 꺼내는 함수 $`\pi_1(a,b)=a`를 생각하자.
두 순서쌍을 먼저 연산하면 $`(a,b)(c,d)=(ac,bd)`이므로
그 첫째 성분은 $`ac`이다.
이는 먼저 각 첫째 성분을 꺼내 원래 군에서 연산한 값과 같다.

$$`\pi_1\bigl((a,b)(c,d)\bigr)=ac=\pi_1(a,b)\pi_1(c,d).`

```savedLean
theorem product_first_preserves_op
    (G : Group A) (H : Group B) (p q : A × B) :
    ((productGroup G H).op p q).1 = G.op p.1 q.1 := by
  rfl
```

또한 임의의 `a : A`는 순서쌍 `(a, H.id)`의 첫째 성분이므로 이 함수는 전사이다.

```savedLean
theorem product_first_surjective (H : Group B) :
    Surjective (fun p : A × B => p.1) := by
  intro a
  exists (a, H.id)
```

이처럼 군 사이의 함수가 연산을 보존하는 조건은 뒤에서 준동형으로 정의한다. 여기서는 그 조건이 성분별 연산의 정의에서 어떻게 나오는지 확인한 것이다.

# 연습문제
%%%
tag := "group-product-exercises"
file := "exercises"
%%%

*문제 1* 두 군의 곱이 아벨군이면 각 군도 아벨군임을 증명하라.

```savedLean -keep
theorem exercise_product_abelian_factors
    (G : Group A) (H : Group B)
    (h : IsAbelian (productGroup G H)) :
    IsAbelian G ∧ IsAbelian H := by
  sorry
```

*문제 2* 순서쌍의 자연수 거듭제곱은 각 성분의 거듭제곱으로 이루어진 순서쌍임을 증명하라.

```savedLean -keep
theorem exercise_product_power (G : Group A) (H : Group B)
    (a : A) (b : B) (n : Nat) :
    power (productGroup G H) (a, b) n =
      (power G a n, power H b n) := by
  sorry
```


```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
