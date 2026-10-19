import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Operations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "군의 정의와 기본 성질" =>

%%%
tag := "group-basics"
file := "groups"
%%%

앞 절에서 배운 결합법칙과 항등원, 역원의 조건을 모아 군을 정의하자.
정수의 덧셈과 두 원소의 연산표에서 구체적인 군을 구성한 뒤,
모든 군에서 항등원과 역원이 유일함을 증명한다.
이 성질로 공통 원소를 소거하고 방정식의 해를 구하는 방법을 익힌다.

```savedComment
군의 정의와 기본 성질: 정수의 덧셈군, 두 원소 군, 유일성과 소거법칙.
연습문제의 sorry는 독자가 채울 빈 증명이다.
```

```savedImport
import AlgebraBook.Operations
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample

variable {A B : Type}

local infixr:90 (priority := high) " ∘ " => compose
```

# 군의 정의
%%%
tag := "groups-definition"
file := "definition"
%%%

정수의 덧셈은 결합법칙을 만족하고 항등원과 각 원소의 역원을 갖는다.
이 세 조건을 모아 군을 정의하자.

*정의* 집합 $`A`와 그 위의 이항연산 $`\ast`가 다음 조건을 만족하면 *군*이라고 한다.

1. 모든 $`a, b, c \in A`에 대하여 $`(a \ast b) \ast c = a \ast (b \ast c)`이다.
2. 모든 $`a \in A`에 대하여 $`e \ast a = a \ast e = a`인 항등원 $`e \in A`가 존재한다.
3. 각 $`a \in A`에 대하여 $`b \ast a = a \ast b = e`인 역원 $`b \in A`가 존재한다.

Lean에서 군을 정의할 때는 연산과 항등원, 각 원소의 역원을 주는 함수에
군의 법칙을 만족한다는 증명을 함께 묶어야 한다.
`Fin`에서 자연수 값과 범위 조건을 묶었던 것과 같이 `structure`로 이 자료들을 묶자.
연산은 `op`, 항등원은 `id`, 역원 함수는 `inv`라는 이름으로 둔다.

```savedLean
structure Group (A : Type) where
  op : BinaryOp A
  id : A
  inv : A → A
  assoc : Associative op
  id_left : IsLeftIdentity op id
  id_right : IsRightIdentity op id
  inv_left : ∀ a, op (inv a) a = id
  inv_right : ∀ a, op a (inv a) = id
```

이 선언으로 `Group A`는 타입 `A` 위의 군 구조를 나타내는 타입이 된다.
`where` 아래의 각 항목을 *필드*라고 하며 `G : Group A`가 주어지면
`G.op`, `G.id`, `G.inv`로 연산과 항등원, 역원 함수를 꺼낸다.
예를 들어 군의 원소 `a : A`의 역원은 `G.inv a`로 쓴다.

나머지 필드에는 이 연산과 원소가 군의 법칙을 만족한다는 증명이 들어 있다.
`G.assoc`는 결합법칙의 증명이며
`G.id_left`와 `G.id_right`는 각각 `G.id`가 좌항등원과 우항등원이라는 증명이다.
또한 `G.inv_left a`와 `G.inv_right a`는 `G.inv a`가 `a`의 좌역원과 우역원이라는 등식의 증명이다.

## 정수의 덧셈군
%%%
tag := "groups-integer-addition"
file := "integer-addition"
%%%

앞에서 살펴본 정수의 덧셈을 `Group Int`로 구성해 보자.
연산은 `intAdd`, 항등원은 $`0`, 역원 함수는 `fun a => -a`로 두고 각 법칙을 증명한다.

```savedLean
def intAdditionGroup :
    Group Int where
  op := intAdd
  id := 0
  inv := fun a => -a

  -- 정수의 덧셈 법칙으로 군의 조건을 확인한다.
  assoc := by
    intro a b c
    exact Int.add_assoc a b c

  id_left := by
    intro a
    exact Int.zero_add a

  id_right := by
    intro a
    exact Int.add_zero a

  inv_left := by
    intro a
    exact Int.add_left_neg a

  inv_right := by
    intro a
    exact Int.add_right_neg a
```

이제 `intAdditionGroup.op`을 사용하면 정수의 덧셈을 계산하고
`intAdditionGroup.id`를 사용하면 항등원 $`0`을 얻는다.
가령 아래의 등식은 $`3+(-3)=0`이므로 `rfl`로 증명할 수 있다.

```savedLean
example :
    intAdditionGroup.op 3 (-3) =
      intAdditionGroup.id := by
  rfl
```

## 아벨군
%%%
tag := "groups-abelian"
file := "abelian"
%%%

정수의 덧셈군에서는 군의 세 조건에 더하여 교환법칙도 성립한다.

*정의* 연산이 교환법칙도 만족하는 군을 *아벨군* 또는 *가환군*이라고 한다.

```savedLean
def IsAbelian : Group A → Prop :=
  fun G => Commutative G.op
```

정수의 덧셈군이 아벨군임은 덧셈의 교환법칙 `Int.add_comm`으로 확인한다.

```savedLean
theorem intAdditionGroup_abelian :
    IsAbelian intAdditionGroup := by
  intro a b
  exact Int.add_comm a b
```

## 곱셈 표기와 덧셈 표기
%%%
tag := "groups-additive-and-multiplicative-notation"
file := "additive-and-multiplicative-notation"
%%%

정수의 덧셈군에서는 연산과 항등원, 역원을 각각 $`+`, $`0`, $`-a`로 썼다.
이를 *덧셈 표기*라고 한다. 연산을 $`ab`나 $`a*b`로 쓰는 *곱셈 표기*에서는
항등원을 $`1` 또는 $`e`로, 역원을 $`a^{-1}`로 쓴다.
이에 따라 같은 역원의 법칙도 덧셈 표기에서는 $`(-a)+a=a+(-a)=0`이고
곱셈 표기에서는 $`a^{-1}a=aa^{-1}=e`이다.

표기는 연산과 원소를 어떻게 쓸지 정하는 약속이다.
덧셈 표기를 쓰는 경우에도 교환법칙을 사용하려면 그 군이 아벨군이라는 가정이나 증명이 있어야 한다.

Lean에서도 기호와 정의를 연결하여 표기를 정할 수 있다.
아래에서는 주어진 군 `G`의 연산과 항등원, 역원에 `+`, `0`, `-`를 연결해 보자.
`letI`는 앞의 `instance`와 같이 기호의 뜻을 정하되 이 증명 안에서만 사용하는 선언이다.
세 선언의 세부 문법은 모두 익힐 필요가 없으며,
지금은 `+`, `0`, `-`가 각각 `G.op`, `G.id`, `G.inv`에 연결된다는 점만 확인하면 된다.

```savedLean
example (G : Group A) (a : A) :
    G.op (G.inv a) a = G.id := by
  letI : Add A := { add := G.op }
  letI : OfNat A 0 := { ofNat := G.id }
  letI : Neg A := { neg := G.inv }

  have h : -a + a = 0 := by
    exact G.inv_left a

  exact h
```

이 표기에서 역원의 법칙은 `-a + a = 0`이다.
`G.inv_left a`로 이 등식을 증명하여 `h`로 이름을 붙이면
원래의 목표 `G.op (G.inv a) a = G.id`에도 같은 증명을 사용할 수 있다.

이 선언은 이 증명에서 새로 적는 기호의 뜻을 정한다.
이미 적은 목표나 가정의 연산은 그대로 유지되며,
같은 타입 위에 다른 군 구조 `H`가 주어져도 `G.op`와 `H.op`로 구별할 수 있다.

## 두 원소 군
%%%
tag := "group-two-elements"
%%%

### 두 값과 연산표
%%%
tag := "group-two-element-table"
file := "operation-table"
%%%

서로 다른 두 원소를 $`e,u`라고 하고 다음 표로 연산을 정하자. 행에서 고른 원소를 왼쪽에, 열에서 고른 원소를 오른쪽에 놓는다.

:::table +header (align := left)
*
  * $`*`
  * $`e`
  * $`u`
*
  * $`e`
  * $`e`
  * $`u`
*
  * $`u`
  * $`u`
  * $`e`
:::

표에서 $`e`가 양쪽 항등원이고 $`ee=uu=e`임을 읽을 수 있다. 각 원소가 자기 자신의 역원이며 표가 대각선에 대하여 대칭이므로 두 원소는 서로 가환한다. 결합법칙은 세 원소를 고르는 여덟 경우에서 확인하면 된다.

Lean에서는 두 값으로 이루어진 타입 `Bool`을 사용하여
`false`를 $`e`에, `true`를 $`u`에 대응시키자.
`Bool.xor`는 두 값이 같으면 `false`, 다르면 `true`이므로 위의 연산표와 일치한다.

여기서 `b : Bool`은 두 값 중 하나를 뜻한다.
앞에서 명제를 적은 `P : Prop`나 그 증명을 적은 `h : P`와 구별하라.

*보기* `false`를 왼쪽에서 연산하면 원래 값이 남는다. 아래에서는 `cases`로 두 값의 경우를 나누고 각 식을 계산한다.

```savedLean
theorem bool_xor_left_identity (b : Bool) :
    Bool.xor false b = b := by
  cases b with
  | false => rfl
  | true => rfl
```

`Bool`의 생성자 이름이 곧 `cases`에서 적은 두 경우의 이름이다. 결합법칙과 나머지 항등원·역원 법칙도 연산표의 계산이며, 이런 유한한 확인에는 앞에서 배운 `decide`를 사용할 수 있다.

```savedLean
def twoElementGroup :
    Group Bool where
  op := Bool.xor
  id := false
  inv a := a

  -- 두 원소의 연산표로 군의 법칙을 확인한다.
  assoc := by
    expand
    decide

  id_left := bool_xor_left_identity
  id_right := by
    expand
    decide

  inv_left := by decide
  inv_right := by decide

theorem twoElementGroup_abelian :
    IsAbelian twoElementGroup := by
  expand!
  decide
```

`assoc`에서 `expand`는 결합법칙의 정의를 드러내어 두 값에 관한 전칭명제를 만든다. 이 타입에서는 모든 경우를 계산할 수 있으므로 `decide`로 확인한다. 아벨성도 두 원소의 교환법칙을 같은 방법으로 확인한 것이다.


# 군의 첫 성질
%%%
tag := "groups-first-properties"
file := "first-properties"
%%%

이제 임의의 군 `G : Group A`를 고정하고 항등원과 역원의 유일성, 소거법칙을 증명하자.
이 성질들은 결합법칙과 항등원·역원의 법칙에서 나오므로 모든 군에 성립한다.
증명에서는 준비 장에서 익힌 {ref "preliminaries-calc"}[`calc`]로 등식을 이어서 쓴다.
이하에서는 곱셈 표기를 사용하여 연산을 `*`, 항등원을 `e`, 원소 `a`의 역원을 `a⁻¹`로 쓰겠다.
아래 선언은 이 기호들을 각각 `G.op`, `G.id`, `G.inv`에 연결한다.

```savedLean
variable (G : Group A)

local infixl:70 (priority := high) " * " => G.op
local notation "e" => G.id
local postfix:max (priority := high) "⁻¹" => G.inv
```

`a⁻¹`의 위첨자는 `\^-1`로 입력하며 앞에서 연결한 `G.inv a`를 뜻한다.
따라서 정수의 덧셈군에 이 표기를 사용하면 `a⁻¹`는 $`-a`에 해당한다.

## 항등원의 유일성
%%%
tag := "groups-identity-uniqueness"
file := "identity-uniqueness"
%%%

*정리* 군의 항등원은 유일하다.
더 나아가 $`u`가 좌항등원이면 $`u=e`이다.
즉 모든 원소 $`a`에 대하여 $`u*a=a`라는 조건만으로 $`u=e`를 얻는다.

*증명* 주어진 조건에서 $`a = e`를 택하면 $`u * e = e`이다.
또한 $`e`가 항등원이므로 $`u * e = u`이며 두 등식을 연결하면 다음과 같다.

$$`u = u * e = e.`

```savedLean
theorem identity_unique (u : A)
    (hu : ∀ a : A, u * a = a) :
    u = e := by
  calc
    u = u * e := by rw [G.id_right]
    _ = e := by exact hu e
```

첫 번째 줄에서 `rw [G.id_right]`은 오른쪽의 `u * e`를 `u`로 바꾸어 등식을 증명한다.
두 번째 줄에서는 전칭명제의 증명 `hu`에 원소 `e`를 적용하여 `u * e = e`를 얻는다.
따라서 군의 좌항등원도 처음 정한 항등원 $`e`와 같다.

## 역원의 유일성
%%%
tag := "groups-inverse-uniqueness"
file := "inverse-uniqueness"
%%%

*정리* 군에서 $`a`의 좌역원 $`b`는 $`b=a^{-1}`을 만족한다.
즉 $`b*a=e`이면 $`b=a^{-1}`이다.
특히 한 원소의 역원은 유일하다.

*증명* $`b`에 항등원 $`e=a*a^{-1}`를 오른쪽에서 곱한 뒤
결합법칙으로 $`b*a`를 묶으면 가정을 사용할 수 있다.

$$`b = b * e = b * (a * a^{-1}) = (b * a) * a^{-1} = e * a^{-1} = a^{-1}.`

이 계산에서 $`e`를 $`a * a^{-1}`로 바꾸는 단계는 등식 $`a * a^{-1} = e`를 반대 방향으로 사용한다.
앞에서 배운 `rw [← h]`로 이 등식을 반대 방향으로 사용한다.

```savedLean
theorem inverse_unique (a b : A)
    (hba : b * a = e) :
    b = a⁻¹ := by
  -- b의 오른쪽에 항등원 a * a⁻¹을 곱한다.
  calc
    b = b * e := by rw [G.id_right]
    _ = b * (a * a⁻¹) := by rw [← G.inv_right a]

    -- 가정 b * a = e를 사용할 수 있도록 묶는다.
    _ = (b * a) * a⁻¹ := by rw [← G.assoc]
    _ = e * a⁻¹ := by rw [hba]
    _ = a⁻¹ := by rw [G.id_left]
```

두 번째 줄의 `rw [← G.inv_right a]`는 `e`를 `a * a⁻¹`로 바꾸고
다음 줄의 `rw [← G.assoc]`는 `b * (a * a⁻¹)`의 괄호를 `(b * a) * a⁻¹`로 옮긴다.
이제 `rw [hba]`로 `b * a`를 `e`로 바꾸면
마지막 목표 `e * a⁻¹ = a⁻¹`은 항등원의 법칙 `G.id_left`로 증명된다.

## 왼쪽 소거법칙
%%%
tag := "groups-left-cancellation"
file := "left-cancellation"
%%%

*정리* 군에서 $`a * b = a * c`이면 $`b = c`이다.

*증명* 등식의 양변에 $`a^{-1}`를 왼쪽에서 곱하면
$`a^{-1}*(a*b)=a^{-1}*(a*c)`를 얻는다.
결합법칙으로 $`a^{-1}*a`를 묶고 역원·항등원의 법칙을 쓰면 각각 $`b`와 $`c`가 남는다.
이 계산을 $`b`에서 시작하는 등식 연쇄로 적으면 다음과 같다.

```savedLean
theorem op_left_cancel (a b c : A)
    (h : a * b = a * c) :
    b = c := by
  -- b를 a⁻¹ * (a * b)로 나타낸다.
  calc
    b = e * b := by rw [G.id_left]
    _ = (a⁻¹ * a) * b := by rw [← G.inv_left a]
    _ = a⁻¹ * (a * b) := by rw [G.assoc]

    -- 주어진 등식 a * b = a * c를 대입한다.
    _ = a⁻¹ * (a * c) := by rw [h]

    -- a⁻¹ * a를 묶어 항등원으로 바꾸면 c가 남는다.
    _ = (a⁻¹ * a) * c := by rw [← G.assoc]
    _ = e * c := by rw [G.inv_left]
    _ = c := by rw [G.id_left]
```

앞의 세 줄에서 `b = a⁻¹ * (a * b)`를 얻으면
`rw [h]`로 `a * b`를 `a * c`로 바꿀 수 있다.
이후에는 처음의 계산을 거꾸로 따라가며 결합법칙으로 `a⁻¹ * a`를 묶고
역원과 항등원의 법칙으로 `c`를 얻는다.

*보기* 군의 원소 $`a`가 $`a*a=a`를 만족하면 $`a=e`이다.
오른쪽을 $`a*e`로 쓰면 등식이 $`a*a=a*e`가 되므로 왼쪽의 $`a`를 소거할 수 있다.

```savedLean
example
    (a : A)
    (h : a * a = a) :
    a = e := by
  apply op_left_cancel G a
  rw [G.id_right]
  exact h
```

`apply op_left_cancel G a` 뒤의 목표는 `a * a = a * e`이다.
오른쪽을 항등원의 법칙으로 바꾸면 주어진 등식 `h`가 된다.

## 군의 방정식
%%%
tag := "groups-solving-equations"
file := "solving-equations"
%%%

방금 소거법칙을 증명할 때처럼 방정식 $`a*x=b`의 양변에 $`a^{-1}`를 왼쪽에서 곱하면
$`a^{-1}*(a*x)=a^{-1}*b`이며 왼쪽을 정리하여 $`x=a^{-1}*b`를 얻는다.
이 값을 원래 식에 넣고 결합법칙과 역원의 법칙으로 계산해 보자.

```savedLean
theorem solve_op_left (a b : A) : a * (a⁻¹ * b) = b := by
  calc
    a * (a⁻¹ * b) = (a * a⁻¹) * b := by rw [← G.assoc]
    _ = e * b := by rw [G.inv_right]
    _ = b := by rw [G.id_left]
```

위 계산으로 $`a^{-1}*b`가 해임을 확인했다.
또한 $`x`, $`y`가 모두 해라면 $`a*x=b=a*y`이므로 왼쪽 소거법칙에 따라 $`x=y`이다.
따라서 이 방정식의 해는 존재하며 유일하다.

*보기* 미지수의 오른쪽에 $`a`가 있는 방정식 $`x*a=b`의 해는 $`b*a^{-1}`이다.
이번에는 양변의 오른쪽에 $`a^{-1}`를 곱하여 해를 얻는다.
그 값을 원래 식에 넣으면 다음과 같이 확인할 수 있다.

```savedLean
theorem solve_op_right (a b : A) : (b * a⁻¹) * a = b := by
  calc
    (b * a⁻¹) * a = b * (a⁻¹ * a) := by rw [G.assoc]
    _ = b * e := by rw [G.inv_left]
    _ = b := by rw [G.id_right]
```

두 방정식에서는 $`a^{-1}`를 곱하는 쪽이 다르다.
각각 $`a^{-1}*a` 또는 $`a*a^{-1}`가 이웃하도록 곱해야 역원의 법칙을 사용할 수 있다.

# 연습문제
%%%
tag := "groups-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* 군의 우항등원도 항등원과 같음을 증명하라.

```savedLean -keep
theorem exercise_right_identity_unique
    (u : A)
    (hu : ∀ a : A, a * u = a) :
    u = e := by
  sorry
```


*문제 2* 항등원의 역원은 항등원임을 증명하라.

```savedLean -keep
theorem exercise_inverse_identity : e⁻¹ = e := by
  sorry
```


*문제 3* 역원의 역원이 원래 원소임을 증명하라.

```savedLean -keep
theorem exercise_inverse_inverse_group
    (a : A) :
    (a⁻¹)⁻¹ = a := by
  sorry
```


*문제 4* 오른쪽 소거법칙을 증명하라.

```savedLean -keep
theorem exercise_right_cancellation
    (a b c : A)
    (h : b * a = c * a) :
    b = c := by
  sorry
```


*문제 5* $`a * x = b`이면 $`x = a^{-1} * b`임을 증명하라.

```savedLean -keep
theorem exercise_solve_left_equation
    (a b x : A)
    (h : a * x = b) :
    x = a⁻¹ * b := by
  sorry
```


*문제 6* 집합 $`A` 위의 이항연산이 결합법칙을 만족하고 다음 두 조건을 만족한다고 하자.

1. 모든 $`a\in A`에 대하여 $`u\ast a=a`인 좌항등원 $`u`가 존재한다.
2. 각 $`a\in A`에 대하여 $`b\ast a=u`인 원소 $`b\in A`가 존재한다.

$`u`가 우항등원이기도 하며 $`b\ast a=u`를 만족하는 모든 $`b`에 대하여
$`a\ast b=u`도 성립함을 증명하라.
그러면 $`u`는 양쪽 항등원이고 각 원소는 양쪽 역원을 가지므로 $`A`는 이 연산에 대하여 군이 된다.

```savedLean -keep
theorem exercise_left_axioms_two_sided
    (op : BinaryOp A) (u : A)
    (hassoc : Associative op)
    (hleft : IsLeftIdentity op u)
    (hinv : ∀ a : A, ∃ b : A, op b a = u) :
    IsIdentity op u ∧
      ∀ a b : A, op b a = u → op a b = u := by
  sorry
```

*힌트* $`b\ast a=u`인 원소 $`b`에 대하여 $`c\ast b=u`인 원소 $`c`를 택하라.
결합법칙과 좌항등원의 조건으로 $`c\ast u=a`를 얻은 뒤
$`a\ast b=(c\ast u)\ast b`를 계산하라.
마지막으로 $`a\ast u=a\ast(b\ast a)`를 계산하면 우항등원의 조건을 얻는다.

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
