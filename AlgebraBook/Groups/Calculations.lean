import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Definition

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "역원과 곱의 계산" =>

%%%
tag := "group-calculations"
file := "calculations"
%%%

앞 절의 유일성과 소거법칙을 사용하여 역원을 포함한 식을 계산하자. 항등원의 역원과 역원의 역원을 구한 뒤 곱의 역원에서 원소의 순서가 바뀌는 이유를 살펴본다. 마지막에는 오른쪽 소거법칙을 증명하여 등식의 양쪽에서 계산할 수 있게 한다.

```savedImport
import AlgebraBook.Groups.Definition
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Course
variable {A B : Type}
```

# 항등원과 역원
%%%
tag := "group-inverse-basics"
file := "identity-and-inverse"
%%%

*정리* 항등원의 역원은 항등원이며 역원의 역원은 원래 원소이다.

항등원은 자기 자신의 역원이므로 역원의 유일성에 따라 $`e^{-1}=e`이다.

또한 $`aa^{-1}=e`이므로 $`a`는 $`a^{-1}`의 좌역원이다.
유일성 정리를 이번에는 $`a^{-1}`에 적용하면 $`a=(a^{-1})^{-1}`을 얻는다.

앞 절에서 이 두 성질을 연습문제로 살펴보았다. 이제 뒤의 계산에서 사용할 수 있도록 이름을 붙인 정리로 증명하자. 아래의 `G.op a b`, `G.id`와 `G.inv a`는 각각 $`ab`, $`e`와 $`a^{-1}`이다.

```savedLean
theorem inv_id (G : Group A) : G.inv G.id = G.id := by
  symm
  apply inverse_unique G G.id G.id
  exact G.id_left G.id

theorem inv_inv (G : Group A) (a : A) :
    G.inv (G.inv a) = a := by
  have h : a = G.inv (G.inv a) := by
    apply inverse_unique G (G.inv a) a
    exact G.inv_right a

  exact h.symm
```

`inv_id`에서는 `symm`으로 $`e=e^{-1}`을 목표로 삼고 `inverse_unique`를 적용한다. 남은 조건 $`ee=e`는 항등원의 법칙이다. `inv_inv`에서도 같은 원리를 사용하되 이번에는 역원을 구할 원소가 `G.inv a`이다.

*보기* $`(a^{-1}a)^{-1}=e`이다. 먼저 괄호 안을 항등원으로 바꾸고 방금 증명한 정리를 사용하면 된다.

```savedLean
theorem inverse_cancelled_product (G : Group A) (a : A) :
    G.inv (G.op (G.inv a) a) = G.id := by
  rw [G.inv_left, inv_id]
```

# 곱의 역원
%%%
tag := "group-inverse-product"
file := "inverse-of-product"
%%%

*정리* $`(ab)^{-1}=b^{-1}a^{-1}`이다.

*증명* $`b^{-1}a^{-1}`가 $`ab`의 좌역원임을 보이자.
결합법칙으로 가운데의 $`a^{-1}a`를 묶고 역원과 항등원의 법칙을 적용하면 다음과 같다.

$$`(b^{-1}a^{-1})(ab)=b^{-1}(a^{-1}a)b=b^{-1}b=e.`

따라서 좌역원의 유일성으로 원하는 등식을 얻는다.
순서를 뒤집어 $`b^{-1}a^{-1}`를 택했기 때문에 이 계산에서 서로 역원인 원소들을 이웃하게 묶을 수 있다.

```savedLean
theorem inv_op (G : Group A) (a b : A) :
    G.inv (G.op a b) = G.op (G.inv b) (G.inv a) := by
  symm
  apply inverse_unique G (G.op a b)
  -- 곱의 왼쪽에 역원을 놓고 이웃한 원소와 역원을 차례로 소거한다.
  calc
    G.op (G.op (G.inv b) (G.inv a)) (G.op a b) =
        G.op (G.inv b) (G.op (G.inv a) (G.op a b)) := by
      rw [G.assoc]
    _ = G.op (G.inv b) (G.op (G.op (G.inv a) a) b) := by
      rw [G.assoc]
    _ = G.op (G.inv b) b := by rw [G.inv_left, G.id_left]
    _ = G.id := by exact G.inv_left b
```

첫 `rw [G.assoc]`는 바깥의 괄호를 오른쪽으로 옮긴다. 다음 줄에서는 `G.inv a`와 `a`가 이웃하도록 안쪽의 괄호를 옮기고, `G.inv_left`와 `G.id_left`로 그 곱을 정리한다. 남은 $`b^{-1}b`도 역원의 법칙으로 항등원이다.

*보기* $`(abc)^{-1}=c^{-1}(b^{-1}a^{-1})`이다. 두 원소의 곱에 대한 정리를 차례로 적용하면 된다.

```savedLean
theorem inverse_three_factors (G : Group A) (a b c : A) :
    G.inv (G.op (G.op a b) c) =
      G.op (G.inv c) (G.op (G.inv b) (G.inv a)) := by
  rw [inv_op, inv_op]
```

# 오른쪽 소거법칙
%%%
tag := "group-right-cancellation"
file := "right-cancellation"
%%%

*정리* $`ba=ca`이면 $`b=c`이다.

*증명* 양변의 오른쪽에 $`a^{-1}`를 곱하면 $`(ba)a^{-1}=(ca)a^{-1}`이다. 결합법칙과 $`aa^{-1}=e`를 사용하면 각각 $`b`와 $`c`가 남는다. 아래에서는 이 논증을 $`b`에서 $`c`로 이어지는 등식 연쇄로 적는다.

```savedLean
theorem op_right_cancel (G : Group A) (a b c : A)
    (h : G.op b a = G.op c a) :
    b = c := by
  calc
    b = G.op b G.id := by rw [G.id_right]
    _ = G.op b (G.op a (G.inv a)) := by rw [G.inv_right]
    _ = G.op (G.op b a) (G.inv a) := by rw [G.assoc]
    _ = G.op (G.op c a) (G.inv a) := by rw [h]
    _ = G.op c (G.op a (G.inv a)) := by rw [G.assoc]
    _ = c := by rw [G.inv_right, G.id_right]
```

앞 절의 `op_left_cancel`은 공통 원소가 왼쪽에 있을 때, `op_right_cancel`은 오른쪽에 있을 때 사용한다. 두 정리는 앞으로 지수 법칙을 증명할 때도 사용한다.

# 이어진 곱의 소거
%%%
tag := "group-adjacent-cancellation"
file := "adjacent-cancellation"
%%%

서로 역원인 두 원소가 여러 곱 안에서 이웃하면 그 부분을 소거할 수 있다. 앞 절의 `solve_op_left`는 $`a(a^{-1}b)=b`라는 계산이었다. 반대 순서에서도 $`a^{-1}(ab)=b`이며, 결합법칙으로 먼저 $`a^{-1}a`를 묶으면 된다.

```savedLean
theorem inv_op_cancel_left (G : Group A) (a b : A) :
    G.op (G.inv a) (G.op a b) = b := by
  calc
    G.op (G.inv a) (G.op a b) =
        G.op (G.op (G.inv a) a) b := by rw [G.assoc]
    _ = b := by rw [G.inv_left, G.id_left]
```

# 연습문제
%%%
tag := "group-calculations-exercises"
file := "exercises"
%%%

*문제 1* $`ab=e`이면 $`ba=e`임을 증명하라.

```savedLean -keep
theorem exercise_op_reverse_identity (G : Group A) (a b : A)
    (h : G.op a b = G.id) :
    G.op b a = G.id := by
  sorry
```

*문제 2* $`axa^{-1}=e`이면 $`x=e`임을 증명하라.

```savedLean -keep
theorem exercise_conjugate_identity (G : Group A) (a x : A)
    (h : G.op (G.op a x) (G.inv a) = G.id) :
    x = G.id := by
  sorry
```

*문제 3* $`a^{-1}=b^{-1}`이면 $`a=b`임을 증명하라.

```savedLean -keep
theorem exercise_inverse_injective (G : Group A) (a b : A)
    (h : G.inv a = G.inv b) :
    a = b := by
  sorry
```


```savedLean
end Course
```
