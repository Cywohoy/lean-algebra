import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Numbers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "이항연산" =>

%%%
tag := "binary-operations"
file := "operations"
%%%

이 절에서는 두 원소를 연산하는 방법과 그 연산이 만족하는 성질을 살펴본다.
여러 연산에서 결합법칙과 교환법칙을 확인한 뒤 항등원과 역원을 정의한다.
다음 절에서는 이 조건들을 모아 군을 정의한다.

```savedComment
이항연산: 결합법칙과 교환법칙, 항등원과 역원.
연습문제의 sorry는 독자가 채울 빈 증명이다.
```

```savedImport
import AlgebraBook.Numbers
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample

variable {A B : Type}

local infixr:90 (priority := high) " ∘ " => compose
```

# 이항연산의 정의
%%%
tag := "groups-binary-operations"
file := "binary-operations"
%%%

덧셈이나 곱셈에서는 두 수를 받아 새로운 수를 얻는다.
이처럼 두 원소를 받아 같은 집합의 원소를 돌려주는 함수를 먼저 정의하자.

*정의* 집합 $`A`의 원소 두 개 $`a`, $`b`에 다시 $`A`의 원소 하나를 대응시키는 함수를
$`A` 위의 *이항연산*이라고 한다.
연산을 $`\ast`로 나타내면 $`\ast : A \times A \to A`이며 그 값을 $`a \ast b`로 쓴다.

Lean에서는 앞에서 정한 방식대로 두 인수를 차례로 받는 타입 `A → A → A`를 사용한다.
{ref "intro-pairs-and-currying"}[두 인수를 받는 방식]에서 보았듯이
이 타입의 함수와 순서쌍을 받는 타입 `(A × A) → A`의 함수는 서로 변환할 수 있다.
이항연산의 타입을 `BinaryOp A`로 정의하고 자연수의 덧셈을 예로 들자.

```savedLean
def BinaryOp (A : Type) := A → A → A
def natAdd : BinaryOp Nat := fun a b => a + b
```

`natAdd 2 3`을 계산하면 자연수 $`5`를 얻으며 다른 자연수 두 개를 더해도 결과는 자연수이다.
이처럼 집합의 원소들을 연산한 결과가 언제나 그 집합에 속하면
그 집합이 연산에 대하여 *닫혀 있다*고 한다.

닫혀 있는지는 원소를 어느 집합에서 택하는지에 따라 달라진다.
정수 전체는 뺄셈에 대하여 닫혀 있지만 양의 정수들의 집합에서는 $`1-2=-1`이 그 집합을 벗어난다.
Lean의 `BinaryOp A`는 함수값의 타입도 `A`이므로 닫힘 조건을 타입에 포함한다.

*보기* $`A`에서 $`A`로 가는 함수 두 개를 합성하면 다시 $`A`에서 $`A`로 가는 함수를 얻는다.
따라서 합성은 함수의 타입 `A → A` 위의 이항연산이다.

```savedLean
def endoCompose (A : Type) : BinaryOp (A → A) :=
  fun f g => f ∘ g
```

# 결합법칙과 교환법칙
%%%
tag := "groups-operation-laws"
file := "operation-laws"
%%%

이항연산으로 원소 세 개를 계산하려면 어느 두 원소를 먼저 연산할지 정해야 한다.
이 순서를 괄호로 나타내고 괄호를 옮겨도 값이 같은 조건을 살펴보자.
두 원소의 순서를 바꾸어도 값이 같은 조건도 함께 정의한다.

*정의* 모든 $`a, b, c \in A`에 대하여
$`(a \ast b) \ast c = a \ast (b \ast c)`이면 연산이 *결합법칙*을 만족한다고 한다.
또한 모든 $`a, b \in A`에 대하여 $`a \ast b = b \ast a`이면 *교환법칙*을 만족한다고 한다.

```savedLean
def Associative : BinaryOp A → Prop :=
  fun op => ∀ a b c, op (op a b) c = op a (op b c)
def Commutative : BinaryOp A → Prop :=
  fun op => ∀ a b, op a b = op b a
```

*보기* 자연수의 덧셈은 결합법칙과 교환법칙을 모두 만족한다.
Lean에서는 자연수 덧셈의 정리 `Nat.add_assoc`와 `Nat.add_comm`으로 두 조건을 확인한다.

```savedLean
example :
    Associative natAdd := by
  intro a b c
  exact Nat.add_assoc a b c

example :
    Commutative natAdd := by
  intro a b
  exact Nat.add_comm a b
```

*보기* 정수에서 $`a\ast b=2(a+b)`로 정한 연산은 교환법칙을 만족한다.
정수의 덧셈에서 $`a+b=b+a`이므로 양변에 $`2`를 곱하면 두 연산값이 같다.

```savedLean
def doubleSum : BinaryOp Int := fun a b => 2 * (a + b)
example :
    Commutative doubleSum := by
  intro a b
  expand
  rw [Int.add_comm]
```

이 연산의 결합법칙도 확인해 보자.
$`(0\ast0)\ast1=2`이고 $`0\ast(0\ast1)=4`이므로 결합법칙은 성립하지 않는다.

```savedLean
example :
    ¬ Associative doubleSum := by
  intro h
  have hBad : (2 : Int) = 4 := by
    exact h 0 0 1

  contradiction
```

`h`를 결합법칙의 증명이라고 가정하고 $`0`, $`0`, $`1`을 차례로 넣으면
`h 0 0 1`이 $`2=4`의 증명이 된다.
이 등식에 `hBad`라는 이름을 붙인 뒤 `contradiction`으로 모순을 얻는다.

*보기* 함수의 합성은 결합법칙을 만족한다.
준비 장에서 증명한 합성의 결합법칙을 `Associative`로 쓰면 다음과 같다.

```savedLean
example
    (A : Type) :
    Associative (endoCompose A) := by
  intro f g h
  ext x
  rfl
```

합성의 순서를 바꾸었을 때에는 함수값이 달라지는 예가 있다.
자연수에서 $`f(n) = 2n`, $`g(n) = n + 1`이면
$`(f \circ g)(3) = 8`이고 $`(g \circ f)(3) = 7`이다.
따라서 두 합성함수가 같다고 가정하면 $`8=7`이라는 모순을 얻는다.

```savedLean
def increment (n : Nat) : Nat := n + 1
example :
    ¬ Commutative (endoCompose Nat) := by
  intro h
  have hfg : double ∘ increment = increment ∘ double := by
    exact h double increment

  -- 두 합성이 같다면 자연수 3에서도 값이 같아야 한다.
  have h3 : (double ∘ increment) 3 =
      (increment ∘ double) 3 := by
    rw [hfg]

  contradiction
```

`h double increment`로 얻은 등식에 `hfg`라는 이름을 붙이고
`rw [hfg]`로 두 합성함수가 $`3`에서 같은 값을 갖는다는 등식 `h3`를 얻는다.
함수값을 계산하면 `h3`가 $`8=7`의 증명이 되므로 `contradiction`으로 증명을 마친다.

이 두 예에서 $`2(a+b)`는 교환법칙만 만족하고 자연수 함수의 합성은 결합법칙만 만족한다.
따라서 한 법칙이 성립한다는 사실만으로 다른 법칙이 성립하는지는 정할 수 없다.

# 항등원과 역원
%%%
tag := "groups-identities-and-inverses"
file := "identities-and-inverses"
%%%

덧셈에서는 $`0`을 더하고 곱셈에서는 $`1`을 곱해도 원래의 수가 그대로 나온다.
일반적인 연산에서 이와 같은 역할을 하는 원소를 정의하자.

*정의* 모든 $`a \in A`에 대하여 $`e \ast a = a`이면 $`e`를 *좌항등원*이라고 하고
$`a \ast e = a`이면 $`e`를 *우항등원*이라고 한다.
좌항등원이면서 우항등원인 원소를 *항등원*이라고 한다.

이름의 좌·우는 항등원을 연산의 어느 쪽에 놓는지 가리킨다.
두 조건을 각각 정의한 뒤 논리곱으로 묶으면 항등원의 조건을 얻는다.

```savedLean
def IsLeftIdentity (op : BinaryOp A) : A → Prop :=
  fun e => ∀ a, op e a = a
def IsRightIdentity (op : BinaryOp A) : A → Prop :=
  fun e => ∀ a, op a e = a
def IsIdentity (op : BinaryOp A) : A → Prop :=
  fun e => IsLeftIdentity op e ∧ IsRightIdentity op e
```

*보기* 자연수에서 $`a\ast b=b`로 정한 연산을 생각하자.
어떤 $`e`를 택해도 $`e\ast a=a`이므로 모든 원소가 좌항등원이다.
우항등원의 조건은 $`a\ast e=e=a`이므로 모든 자연수가 $`e`와 같아야 한다.
따라서 이 연산에는 우항등원이 없다.

```savedLean
def rightProjection : BinaryOp Nat := fun _ b => b
example
    (e : Nat) :
    IsLeftIdentity rightProjection e := by
  intro a
  rfl

example :
    ¬ ∃ e : Nat, IsRightIdentity rightProjection e := by
  intro h
  unpack h with ⟨e, he⟩

  -- 같은 항등원 e가 0이면서 1이어야 하므로 모순이다.
  have h0 : e = 0 :=
    he 0
  have h1 : e = 1 :=
    he 1
  rw [h0] at h1
  contradiction
```

두 번째 증명에서는 우항등원 `e`가 있다고 가정한 뒤 `he`에 $`0`과 $`1`을 넣는다.
그러면 `e = 0`과 `e = 1`을 얻으므로 `rw [h0] at h1`으로 $`0=1`이라는 모순을 얻는다.

*보기* 자연수의 덧셈에서 항등원은 $`0`이다.
두 조건 $`0+a=a`와 $`a+0=a`는 각각 `Nat.zero_add`와 `Nat.add_zero`로 증명한다.

```savedLean
example :
    IsIdentity natAdd 0 := by
  constructor
  · intro a
    exact Nat.zero_add a

  · intro a
    exact Nat.add_zero a
```

정수의 덧셈에서 $`a`에 $`-a`를 더하면 방금 살펴본 항등원 $`0`을 얻는다.
이를 일반적인 연산으로 옮겨 주어진 원소와 연산하면 항등원이 되는 원소를 정의하자.

*정의* 항등원 $`e`를 고정하자.
$`b\ast a=e`이면 $`b`를 $`a`의 *좌역원*이라고 하고
$`a\ast b=e`이면 $`b`를 $`a`의 *우역원*이라고 한다.
$`a`의 좌역원이면서 우역원인 원소를 $`a`의 *역원*이라고 한다.

좌역원과 우역원에서는 역원을 원래 원소의 어느 쪽에 놓는지 구별한다.
예를 들어 $`b\ast a=e`라는 등식은 $`b`가 $`a`의 좌역원이라는 뜻이며
동시에 $`a`가 $`b`의 우역원이라는 뜻이다.
역원의 두 조건은 다음과 같이 논리곱으로 나타낸다.

```savedLean
def IsInverse (op : BinaryOp A) (e : A)
    (_he : IsIdentity op e) :
    A → A → Prop :=
  fun a b => op b a = e ∧ op a b = e
```

인수 `_he`로 `e`가 항등원이라는 증명을 먼저 받는다.
이 가정 아래에서 `b`가 `a`의 역원이라는 명제는 `op b a = e`와 `op a b = e`의 논리곱이다.
따라서 역원임을 증명할 때는 이 두 등식을 보이면 된다.

*보기* 자연수의 함수 $`s(n)=n+1`과 $`p(n)=n-1`을 합성해 보자.
자연수의 뺄셈에서는 $`p(0)=0`이며 모든 $`n`에 대하여 $`p(s(n))=n`이다.
따라서 합성 연산에서 항등함수 $`\operatorname{id}_{\mathbb{N}}`을 항등원으로 보면
$`p\circ s=\operatorname{id}_{\mathbb{N}}`이므로 $`p`는 $`s`의 좌역원이다.
그런데 $`s(p(0))=1`이므로 $`s\circ p`는 항등함수와 다르고 $`p`는 $`s`의 우역원이 아니다.

```savedLean
def decrement (n : Nat) : Nat := n - 1
example :
    decrement ∘ increment = identity Nat := by
  ext n
  expand
  expand
  expand
  arith

example :
    increment ∘ decrement ≠ identity Nat := by
  intro h
  have h0 : (increment ∘ decrement) 0 =
      identity Nat 0 := by
    rw [h]

  contradiction
```

첫 증명에서는 각 자연수 `n`에서의 함수값을 비교하고
둘째 증명에서는 두 함수가 같다는 가정을 $`0`에서 사용하여 $`1=0`이라는 모순을 얻는다.
같은 등식 $`p\circ s=\operatorname{id}_{\mathbb{N}}`을 $`p`의 관점에서 읽으면 $`s`가 $`p`의 우역원이며, 두 번째 예제에 따라 좌역원은 아니다.

*보기* 자연수의 덧셈에서는 항등원이 $`0`이므로 $`1`의 역원을 찾으려면 $`1+b=0`이어야 한다.
그러나 어떤 자연수 $`b`를 택해도 $`1+b\geq1`이므로 그러한 역원은 없다.

```savedLean
example :
    ¬ ∃ b : Nat, natAdd 1 b = 0 := by
  intro h
  unpack h with ⟨b, hb⟩

  -- 자연수에 1을 더한 값이 0일 수 없음을 사용한다.
  have hb' : b + 1 = 0 := by
    rw [Nat.add_comm]
    exact hb

  contradiction
```

`unpack`로 얻은 `hb`는 정의를 펼치면 `1 + b = 0`의 증명이다.
이를 그대로 `contradiction`에 쓰기 전에 교환법칙으로 `b + 1 = 0`으로 바꾼다.
Lean은 `b + 1`을 다음 자연수 `Nat.succ b`로 계산하므로
`contradiction`이 다음 자연수가 $`0`이라는 모순을 확인한다.

정수에서는 $`-a`도 정수이고 $`(-a)+a=a+(-a)=0`이므로 모든 원소가 덧셈에 대한 역원을 갖는다.
이를 Lean으로 보이기 위해 `Int` 위의 덧셈을 `intAdd`로 정의하고
먼저 $`0`이 항등원이라는 사실을 증명하자.

```savedLean
def intAdd : BinaryOp Int := fun a b => a + b
theorem intAdd_identity : IsIdentity intAdd 0 := by
  constructor
  · intro a
    exact Int.zero_add a

  · intro a
    exact Int.add_zero a
```

이 증명에 `intAdd_identity`라는 이름을 붙였으므로 역원을 다룰 때 인수로 사용할 수 있다.
이제 이를 전제로 $`-a`가 $`a`의 역원임을 보이자.

```savedLean
example (a : Int) :
    IsInverse intAdd 0 intAdd_identity a (-a) := by
  constructor
  · exact Int.add_left_neg a
  · exact Int.add_right_neg a
```

`constructor`로 목표를 $`(-a)+a=0`과 $`a+(-a)=0`으로 나눈 뒤
각각 `Int.add_left_neg`와 `Int.add_right_neg`로 증명한다.

# 연습문제
%%%
tag := "operations-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.
연산이 조건을 만족하지 않음을 보일 때는 그 조건에 어긋나는 원소를 택하라.

*문제 1* 자연수에서 $`a\ast b=a`로 정한 연산이 결합법칙을 만족함을 보이고
교환법칙은 만족하지 않음을 증명하라.

```savedLean -keep
theorem exercise_leftProjection_associative :
    Associative (fun a _ : Nat => a) := by
  sorry

theorem exercise_leftProjection_not_commutative :
    ¬ Commutative (fun a _ : Nat => a) := by
  sorry
```

*문제 2* 한 이항연산에 좌항등원 $`e`와 우항등원 $`u`가 있으면 $`e=u`임을 증명하라.

```savedLean -keep
theorem exercise_left_right_identity_eq
    (op : BinaryOp A) (e u : A)
    (he : IsLeftIdentity op e)
    (hu : IsRightIdentity op u) :
    e = u := by
  sorry
```

*문제 3* 항등원 $`e`가 주어졌을 때 $`b`가 $`a`의 역원이면
$`a`도 $`b`의 역원임을 증명하라.

```savedLean -keep
theorem exercise_inverse_symm
    (op : BinaryOp A) (e : A)
    (he : IsIdentity op e)
    (a b : A)
    (h : IsInverse op e he a b) :
    IsInverse op e he b a := by
  sorry
```

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
