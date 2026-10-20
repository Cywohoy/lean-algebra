import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Introduction
import AlgebraBook.Tactic.Rule

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "증명의 구성과 사용" =>

%%%
tag := "using-proofs"
file := "using-proofs"
%%%

이 절에서는 간단한 계산과 부등식의 증명을 작성하면서
가정에서 결론을 얻는 추론을 Lean의 증명 단계와 연결한다.
먼저 `apply`와 `exact`로 이미 증명된 정리를 사용하고,
이어 같은 추론을 증명에 인수를 넣는 식으로 나타낸다.
이를 바탕으로 함의와 전칭명제를 증명하고 사용하는 방법을 익힌다.

```savedComment
증명의 구성과 사용: 증명을 선언하고 정리를 사용하는 방법에서 함의와 전칭명제로 나아간다.
연습문제의 sorry는 독자가 채울 빈 증명이다.
```

```savedImport
import AlgebraBook.Introduction
import AlgebraBook.Tactic.Rule
```

```savedLean -show
open scoped Ample
```

```savedLean
namespace ProofExamples
```

앞 절의 `add`와 `positive`는 `IntroExamples`라는 이름 공간 안에 있다.
이들을 `IntroExamples.add`, `IntroExamples.positive`로 가리킬 수 있으며,
`open IntroExamples`로 이름 공간을 열면 짧은 이름으로 사용할 수 있다.

```savedLean
open IntroExamples
```

# 정리와 증명
%%%
tag := "proofs-propositions-and-proofs"
file := "propositions-and-proofs"
%%%

앞 절에서는 `add 2 3`을 계산하여 $`5`를 얻었다.
이번에는 이 계산을 등식 `add 2 3 = 5`로 적고, 그 등식의 증명에 이름을 붙이자.

```savedLean
theorem add_two_three : add 2 3 = 5 := by
  rfl
```

`theorem`의 선언 방식은 앞에서 본 `comparisonProof`와 같다.
`rfl`은 등식의 양변이 정의와 계산에 따라 같을 때 사용하는 전술이다.
왼쪽의 `add 2 3`을 계산하면 오른쪽의 `5`가 되므로 이 한 줄로 증명이 끝난다.

앞의 `#eval`은 함수값을 계산했고, 이번 선언은 등식의 증명에 이름을 붙였다.
따라서 같은 등식을 다시 증명할 때는 `exact add_two_three`로 이 증명을 제시할 수 있다.

# 정리의 사용
%%%
tag := "proofs-named-theorems"
file := "named-theorems"
%%%

부등식의 양변에 같은 수를 더하면 대소관계가 유지된다.
예를 들어 $`a<b`를 알고 있을 때 양변에 $`2`를 더하면 $`a+2<b+2`를 얻는다.
이 성질을 Lean에서는 `Nat.add_lt_add_right`라는 이름의 정리로 사용할 수 있다.

`#check` 뒤에 정리의 이름을 적으면 그 정리가 어떤 명제를 증명하는지 확인할 수 있다.

```lean (name := addLtAddRightType)
#check Nat.add_lt_add_right
```

```leanOutput addLtAddRightType
Nat.add_lt_add_right {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k
```

여기서 `h : n < m`은 알고 있는 부등식의 증명이고 `k`는 더할 수이다.
중괄호의 `{n m : Nat}`와 소괄호의 `(k : Nat)`가 다른 이유를 먼저 살펴보자.

## 정리와 함수의 인수
%%%
tag := "intro-explicit-and-implicit-arguments"
file := "explicit-and-implicit-arguments"
%%%

정리의 타입에도 함수에서처럼 원소나 증명을 받는 인수가 적혀 있다.
인수를 직접 적는 경우와 Lean이 추론하는 경우를 구별하기 위해,
먼저 원소를 그대로 돌려주는 항등함수 $`x\mapsto x`를 생각하자.
자연수 $`3`을 넣으면 $`3`을, $`5`를 넣으면 $`5`를 돌려준다.
같은 규칙을 다른 타입의 원소에도 사용할 수 있도록 원소의 타입을 `A`로 두자.

```savedLean
def identityExplicit (A : Type) (x : A) : A := x
```

`(A : Type)`은 타입 자체를 인수로 받는다는 표기이다.
첫 인수 `A`로 원소의 타입을 정하고, 둘째 인수 `x`로 그 타입의 원소를 받는다.
`:= x`이므로 함수값은 받은 원소 `x`이다.
소괄호로 쓴 인수는 함수를 사용할 때 직접 적는 *명시적 인수*이다.
가령 `identityExplicit Nat 3`에서는 `A`에 `Nat`를, `x`에 `3`을 넣으므로 결과는 `3`이다.

```lean (name := explicitArgumentValue)
#eval identityExplicit Nat 3
```

```leanOutput explicitArgumentValue
3
```

이 예제에서는 원소 `3`의 타입이 `Nat`임을 알면 첫 인수 `A`도 정해진다.
이처럼 다른 인수에서 알아낼 수 있는 인수는 Lean이 추론하도록 중괄호로 표시할 수 있다.

```savedLean
def identityImplicit {A : Type} (x : A) : A := x
```

중괄호로 쓴 `{A : Type}`은 *암시적 인수*이다.
`identityImplicit 3`에서는 `A`를 따로 적지 않아도 Lean이 `Nat`로 추론하며,
앞의 함수와 같이 주어진 원소 `3`을 그대로 돌려준다.

```lean (name := implicitArgumentValue)
#eval identityImplicit 3
```

```leanOutput implicitArgumentValue
3
```

암시적 인수도 직접 지정할 수 있으며,
이때는 `identityImplicit (A := Nat) 3`처럼 인수의 이름을 함께 적는다.
Lean이 인수를 추론할 정보가 부족할 때도 같은 방법으로 지정한다.

## 부등식에 대한 정리의 적용
%%%
tag := "proofs-applying-named-theorems"
%%%

이제 `Nat.add_lt_add_right`의 타입에서 각 인수의 역할을 확인하자.

- `{n m : Nat}`의 `n`, `m`은 비교할 두 자연수이며 암시적 인수이다.
- `h : n < m`은 전제인 부등식의 증명이다.
- `k : Nat`는 양변에 더할 자연수이다.
- 마지막 `n + k < m + k`는 이 정리를 사용하여 얻는 결론이다.

아래에서는 자연수 `a`, `b`와 부등식 `a < b`의 증명 `h`가 주어졌다고 하자.
위 정리의 `n`, `m`에 각각 `a`, `b`를 넣고 `k`를 `2`로 정하면
결론은 `a + 2 < b + 2`가 된다.
목표는 `a + 2 < b + 2`이므로 위 정리를 사용하려면 전제 `a < b`를 확인하면 된다.
이처럼 정리의 결론을 현재 목표에 맞추고 필요한 전제를 새 목표로 삼는 전술이 `apply`이다.
`(k := 2)`로 양변에 더할 수를 명시하여 정리를 사용하자.

```savedLean
theorem add_two_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  apply Nat.add_lt_add_right (k := 2)
  exact h
```

첫 줄에서는 `k`에 넣을 수를 `2`로 지정하여 정리를 사용하므로 목표가 `a < b`로 바뀐다.
이 부등식의 증명은 가정 `h`에 있으므로
둘째 줄에서 `exact h`로 제시하면 원래 부등식의 증명이 완성된다.
수학에서 “$`a<b`이므로 양변에 $`2`를 더하여 $`a+2<b+2`를 얻는다”라고 쓰는 추론을
Lean에서는 목표에서 필요한 전제로 거슬러 올라가며 작성한 것이다.

{anchor "proofs-inferred-theorem-arguments"}[]목표에 양변의 식이 모두 적혀 있으면 사용할 인수를 Lean이 정할 수도 있다.
앞의 목표 `a + 2 < b + 2`에서는 양변에 더하는 수가 `2`로 정해져 있으므로
`(k := 2)`를 생략해도 같은 정리를 사용할 수 있다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  apply Nat.add_lt_add_right
  exact h
```

이 코드에서 `apply`는 정리의 결론을 목표에 맞추면서 `k`를 `2`로 정하고,
전제 `a < b`를 새 목표로 남긴다.

이제 앞에서 증명한 `add_two_preserves_lt`를 사용해 새 부등식을 보이자.
양변에 $`2`를 두 번 더하려면 이 정리를 두 번 사용하면 된다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    (a + 2) + 2 < (b + 2) + 2 := by
  apply add_two_preserves_lt
  apply add_two_preserves_lt
  exact h
```

첫 번째 적용 뒤에는 `a + 2 < b + 2`가 목표가 되고,
두 번째 적용 뒤에는 `a < b`가 목표가 된다.
마지막 전제의 증명으로 `h`를 제시하면 두 번의 정리 적용으로 원래 결론을 얻는다.

아래 문제에서 `sorry`를 증명으로 바꾸어 방금 배운 정리 적용을 연습하라.

*문제 1* 자연수의 부등식 양변에 $`3`을 더해도 부등식이 성립함을
앞에서 배운 정리 `Nat.add_lt_add_right`로 증명하라.

```savedLean -keep
theorem exercise_add_three_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  sorry
```

:::solution
양변에 더할 수를 $`3`으로 지정하면 필요한 전제는 주어진 부등식이다.

```tryLean -keep
example (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  apply Nat.add_lt_add_right (k := 3)
  exact h
```
:::

# 증명 안의 보조정리
%%%
tag := "proofs-naming-proofs"
file := "naming-proofs"
%%%

{ref "intro-proofs-as-values"}[앞 절의 피타고라스 문제]에서는 빗변의 길이를 구하기 위해
먼저 그 제곱이 $`25`임을 보였다.
여러 정리를 차례로 사용할 때는 이처럼 중간에 얻은 사실에 이름을 붙여 두면
다음 추론에서 그 증명을 사용할 수 있다.

{anchor "intro-pythagoras-theorems"}[]이 예제는 빗변의 길이 `c`가 자연수인 경우로 한정한다.
삼각형이 직각삼각형이라는 명제를 `rightAngled`라고 하고,
피타고라스 정리와 제곱의 비교에 관한 다음 두 사실이 주어졌다고 하자.
기하학의 정의를 새로 작성하는 대신 이 두 사실을 사용하여 `c = 5`를 증명한다.

- `pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4`
- `equal_of_equal_squares (a b : Nat) (h : a * a = b * b) : a = b`

첫 정리는 직각이라는 전제를 확인하면 빗변의 제곱을 구하는 데 쓸 수 있다.
둘째 정리는 두 자연수의 제곱이 같음을 확인하면 두 수가 같다는 결론을 준다.
화살표 `→`로 적은 첫 정리의 전제도 `apply`를 쓰면 새 목표로 남는다.

```savedLean -show
theorem equal_of_equal_squares (a b : Nat)
    (h : a * a = b * b) : a = b := by
  apply Nat.mul_self_inj.mp
  exact h

section Pythagoras
variable (c : Nat) (rightAngled : Prop)
variable (pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4)
include pythagoras
```

이 증명에서 미리 주어진 원소와 정리는 다음과 같다.
정리의 인수 `hRight`는 이 삼각형이 직각이라는 증명이다.

```
c : Nat
rightAngled : Prop
pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4
```

{anchor "intro-pythagoras-lean"}[]`have hSquare : c * c = 25 := by` 아래에서 중간 등식을 증명하자.
`have`의 `:` 뒤에는 증명할 명제를 적고, `:= by` 아래에는 그 증명을 적는다.
이 증명을 마치면 `hSquare`라는 이름으로 사용할 수 있다.

```savedLean
theorem hypotenuse_eq_five
    (hRight : rightAngled) :
    c = 5 := by
  -- 직각이라는 가정으로 빗변의 제곱을 구한다.
  have hSquare : c * c = 25 := by
    apply pythagoras
    exact hRight

  -- 두 자연수의 제곱이 같으므로 길이도 같다.
  apply equal_of_equal_squares c 5
  exact hSquare
```

`have`를 시작하기 전에는 `c = 5`를 보이고 있다.
들여쓴 내부 증명에서는 잠시 `c * c = 25`를 목표로 삼으며,
`apply pythagoras`로 필요한 전제 `rightAngled`를 남긴 뒤 `exact hRight`로 확인한다.
정리에 적힌 `3 * 3 + 4 * 4`를 계산하면 `25`이므로 이 증명이 중간 등식에 맞는다.

내부 증명이 끝나면 원래 목표인 `c = 5`로 돌아오고,
사용할 수 있는 증명에 `hSquare : c * c = 25`가 추가된다.
두 제곱의 비교 정리를 적용하면 `c * c = 5 * 5`를 보이면 되므로
방금 얻은 `hSquare`로 증명을 마친다.
들여쓰기는 이처럼 중간 명제를 증명하는 부분과 원래 논증을 이어 가는 부분을 구별한다.

*확인* `have`의 내부 증명이 끝난 위치에서 증명 상태를 확인하라.
목표는 `c = 5`이고, 가정에는 새로 얻은 `hSquare : c * c = 25`가 있다.

```savedLean -show
end Pythagoras
```

# 함의의 증명과 사용
%%%
tag := "proofs-proving-implications"
file := "proving-implications"
%%%

앞의 보기에서는 $`a<b`를 가정하여 $`a+2<b+2`를 보였다.
이처럼 “$`P`이면 $`Q`이다”라는 형태의 명제를 *함의*라고 하며,
Lean에서는 `P → Q`로 쓴다.
함의 $`P \Rightarrow Q`를 증명할 때는 $`P`를 가정하고 $`Q`를 보인다.
Lean에서는 목표가 `P → Q`일 때 `intro hP`로 가정 `hP : P`를 도입하며
이후에는 `Q`가 새 목표가 된다.

*보기* $`P`를 가정하면 $`P`가 성립하므로 $`P \Rightarrow P`이다.

```savedLean
example (P : Prop) : P → P := by
  intro hP
  exact hP
```

처음 목표인 `P → P`에서 `intro hP`를 쓰면 가정 `hP : P` 아래에서 `P`를 보이는 목표로 바뀐다.
따라서 `exact hP`로 이미 갖고 있는 증명을 제시하면 증명이 끝난다.

{anchor "proofs-two-assumptions"}[]*정리* $`P`가 성립하고 $`P \Rightarrow Q`도 성립하면 $`Q`가 성립한다.
이를 두 가정을 차례로 받는 함의로 쓰면 다음과 같다.

$$`P \Rightarrow \bigl((P \Rightarrow Q) \Rightarrow Q\bigr).`

Lean에서는 이 명제를 `P → (P → Q) → Q`로 쓴다.
화살표는 오른쪽부터 묶으므로 `P → ((P → Q) → Q)`로 읽으며,
먼저 `P`를 가정한 뒤 `P → Q`를 가정하여 `Q`를 보이라는 뜻이다.
가정의 순서를 정리하면 다음과 같다.

1. `P`를 가정하고 그 증명에 `hP`라는 이름을 붙인다.
2. `P → Q`를 가정하고 그 증명에 `hPQ`라는 이름을 붙인다.
3. 이제 `Q`를 보여야 하며 두 가정을 함께 사용하면 이 결론을 얻는다.

마지막 추론을 Lean으로 옮길 때는 목표에서 거꾸로 생각해 보자.
`hPQ : P → Q`에서 `hPQ`는 이 함의의 증명이다.
`hPQ`에 의하면 $`P`가 성립할 때 $`Q`가 성립하므로
목표 $`Q`를 보이는 데 필요한 것은 전제 $`P`이다.
이때 `apply hPQ`를 쓰면 목표가 `Q`에서 `P`로 바뀌며,
이미 갖고 있는 가정 `hP`로 이 목표를 해결할 수 있다.

```savedLean
example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ
  exact hP
```

각 줄에서 가정과 목표는 다음과 같이 변한다.

1. `intro hP`: 가정 `hP : P`가 들어오고, 목표는 `(P → Q) → Q`가 된다.
2. `intro hPQ`: 가정 `hPQ : P → Q`가 들어오고, 목표는 `Q`가 된다.
3. `apply hPQ`: 함의의 결론이 목표 `Q`와 같으므로 그 전제 `P`를 새 목표로 삼는다.
4. `exact hP`: 새 목표 `P`의 증명을 이미 갖고 있으므로 이를 제시하여 증명을 마친다.

`apply hPQ`와 `exact hP`를 함께 읽으면 “$`P`를 알고 있고 $`P`이면 $`Q`이므로 $`Q`이다”라는 추론이 된다.

# 증명의 적용
%%%
tag := "proofs-proof-application"
file := "proof-application"
%%%

앞에서는 `apply`로 필요한 전제를 목표로 삼고 `exact`로 그 전제를 확인했다.
이번에는 이 두 단계를 하나의 식으로 나타내는 방법을 살펴보자.
이를 이해하려면 Lean에서 함의의 증명 자체를 어떻게 나타내는지 알아야 한다.

예를 들어 “$`a<b`이면 $`a+2<b+2`이다”를 증명한 논증은
첫 부등식의 증명이 주어질 때마다 둘째 부등식의 증명을 얻는 데 사용할 수 있다.
두 자연수 `a`, `b`를 고정하면 이 논증에 필요한 것은 `a < b`의 증명이고,
그 논증으로 얻는 것은 `a + 2 < b + 2`의 증명이다.

Lean은 함의의 증명을 이와 같이 전제의 증명을 받아 결론의 증명을 돌려주는 *함수*로 표현한다.
명제 `P`를 그 증명들의 타입으로 사용하므로,
`P`의 증명을 인수로 받아 `Q`의 증명을 돌려주는 함수의 타입은 `P → Q`이다.
따라서 `hPQ : P → Q`는 이런 함수이며,
인수 `hP : P`를 넣은 함수값 `hPQ hP`의 타입은 `Q`가 된다.
이때 함수에 넣는 인수는 명제 `P`가 아니라 그 명제의 증명 `hP`이다.
`P`가 참임을 이미 보였거나 가정으로 알고 있을 때 그 증명을 넣어 `Q`의 증명을 얻는다.
이러한 함수 적용을 “증명의 적용”이라고 한다.
세 식의 역할을 구별하면 다음과 같다.

- `hPQ : P → Q`: 전제가 성립할 때 결론을 얻는 데 사용하는 함의의 증명이다.
- `hP : P`: 그 함의에 필요한 전제의 증명이다.
- `hPQ hP : Q`: 두 증명으로 얻은 결론의 증명이다.

앞 절의 `add 2 3`과 비교하면 인수의 역할을 확인할 수 있다.
`add`의 인수는 자연수이고, `hPQ`의 인수는 `P`의 증명이다.
어떤 인수를 넣어야 하는지는 `add`나 `hPQ`의 타입에서 확인할 수 있다.

이제 같은 정리를 다음과 같이 증명할 수 있다.

```savedLean
example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  exact hPQ hP
```

`hPQ hP`가 바로 목표 `Q`의 증명이므로 `exact`로 이 식을 제시하면 된다.
앞에서는 `apply hPQ`로 전제 `P`를 목표로 삼은 뒤 `exact hP`로 증명했다.
이 두 단계를 `exact hPQ hP` 한 줄로 쓰면 `Q`의 증명을 바로 제시하게 된다.

`intro hP hPQ`는 두 가정을 차례로 도입하는 명령으로,
`intro hP`와 `intro hPQ`를 각각 쓰는 것과 같다.
앞의 증명에서는 각 단계의 목표를 확인할 수 있도록 두 줄로 나누어 썼다.

함의를 증명할 때 사용한 `intro`도 이 표현 방식으로 이해할 수 있다.
`P → Q`를 보이기 위해 `intro hP`로 `P`의 증명을 받은 뒤 `Q`를 증명하면,
그 전체 과정이 `P`의 증명을 인수로 받는 함수를 구성한다.
앞에서 증명한 `P → P`는 받은 증명을 그대로 돌려주므로 다음과 같이 쓸 수도 있다.

```savedLean
example (P : Prop) : P → P :=
  fun hP => hP
```

여기서 `hP`의 타입은 `P`이며 함수값도 `P`의 증명이다.
앞의 `intro hP`와 `exact hP`는 이 함수의 인수와 함수값을 단계별로 정한 것이다.

{anchor "proofs-theorem-arguments"}[]{ref "proofs-named-theorems"}[부등식의 보기]에서 사용한 정리도 같은 방식으로 읽을 수 있다.
`Nat.add_lt_add_right`에 부등식 `a < b`의 증명 `h`와 더할 수 `2`를 넣으면
`a + 2 < b + 2`의 증명을 얻는다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  exact Nat.add_lt_add_right h 2
```

여기서 `h`는 증명이고 `2`는 자연수이다.
`Nat.add_lt_add_right h 2` 전체는 부등식의 증명이므로 `exact`로 제시할 수 있다.
앞의 두 줄짜리 증명에서는 `apply`로 전제를 남긴 뒤 `exact h`로 확인했고,
이번에는 그 전제의 증명을 인수로 넣어 결론의 증명을 바로 얻었다.

이미 완성된 증명을 식으로 적을 수 있으면 `:=` 오른쪽에 그 식을 바로 쓸 수도 있다.
예를 들어 위 선언은 증명 부분을 `:= Nat.add_lt_add_right h 2`로 적어도 된다.
`:= by` 아래에 전술을 쓰는 방식은 이러한 증명을 단계별로 구성하는 방법이다.

{anchor "proofs-forward-application"}[]가정에서 함의를 사용하는 `apply hPQ at hP`와
여러 목표에 이름을 붙이는 `with`의 용법은
{ref "tactic-hypotheses"}[부록의 가정과 정리]와
{ref "tactic-select-items"}[항목의 선택과 명명]에서 예제로 설명한다.

## 함의의 연결과 중간 증명
%%%
tag := "proofs-chaining-proof-values"
%%%

*보기* $`P \Rightarrow Q`와 $`Q \Rightarrow R`을 알고 있을 때 $`P \Rightarrow R`을 보이자.
$`P`를 가정하면 첫 함의로 $`Q`를 얻고, 이 사실을 두 번째 함의에 사용하여 $`R`을 얻는다.
이때 중간에 얻은 $`Q`의 증명에 이름을 붙이면 두 추론을 나누어 읽을 수 있다.

{ref "proofs-naming-proofs"}[피타고라스 정리 예제]와 같이 `have hQ : Q := by` 아래에서 `Q`를 증명하면
그 증명을 `hQ`라는 이름으로 사용할 수 있다.

```savedLean
example
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R := by
  intro hP
  -- 첫 함의로 중간 결론 Q를 얻는다.
  have hQ : Q := by
    apply hPQ
    exact hP

  -- 얻은 Q를 두 번째 함의에 사용한다.
  apply hQR
  exact hQ
```

`have`에서 `:=`의 왼쪽에는 증명의 이름 `hQ`와 증명할 명제 `Q`를 적고,
오른쪽의 `by` 아래에는 그 명제의 증명을 적는다.
들여쓴 두 줄에서는 `Q`를 증명하며 이 증명이 끝나면 바깥의 목표 `R`로 돌아온다.
이제 `hQ : Q`가 가정에 추가되었으므로 두 번째 함의에 필요한 전제로 사용할 수 있다.

이미 배운 표기로 쓰면 `hPQ hP` 자체가 `Q`의 증명이므로
이 경우에는 `by` 아래에서 다시 증명하지 않고 `:=` 오른쪽에 그 증명을 바로 적어도 된다.

```savedLean
example
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R := by
  intro hP
  have hQ : Q :=
    hPQ hP
  exact hQR hQ
```

두 코드에서 `hQ`는 모두 명제 `Q`의 증명이며,
짧은 코드에서도 중간 명제와 그 증명은 `:=`를 기준으로 구별된다.

*문제 2* $`P`, $`P \Rightarrow Q`, $`Q \Rightarrow R`을 차례로 가정하여 $`R`을 얻으라.

```savedLean -keep
theorem exercise_implication_chain
    (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  sorry
```

:::solution
마지막 결론 $`R`에서 출발하면 먼저 $`Q`가 필요하고, 이를 얻으려면 $`P`가 필요하다.

```tryLean -keep
example (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  intro hP hPQ hQR
  apply hQR
  apply hPQ
  exact hP
```
:::

# 전칭명제의 증명과 사용
%%%
tag := "proofs-universal-statements"
file := "universal-statements"
%%%

모든 자연수는 $`0` 이상이므로 자연수 $`3`도 $`0` 이상이다.
이 추론에서는 모든 자연수에 관한 사실에서 $`n=3`인 경우를 사용했다.
이처럼 “모든 원소에서 성립한다”는 명제를 *전칭명제*라고 한다.

술어 `P : A → Prop`가 주어졌을 때
“$`A`의 모든 원소 $`x`에서 $`P(x)`가 성립한다”는 명제는 `∀ x : A, P x`로 쓴다.
예를 들어 위의 자연수에 관한 명제는 `∀ n : Nat, 0 ≤ n`이며,
기호 `∀`는 `\forall`로 입력한다.

{anchor "proofs-proving-forall"}[]전칭명제를 증명할 때는 임의의 원소 $`x`를 택하여 $`P(x)`를 보인다.
Lean에서는 `intro x`로 원소 `x : A`를 도입하고, 그 원소에 관한 명제 `P x`를 새 목표로 삼는다.

*보기* 모든 원소 $`x`에 대하여 $`x = x`이다.
앞에서 사용한 `rfl`로 이 원소가 자기 자신과 같음을 보인다.

```savedLean
example (A : Type) : ∀ x : A, x = x := by
  intro x
  rfl
```

`intro x`로 도입한 `x`는 `A`의 임의의 원소이므로 증명에서도 그 값에 관한 특별한 가정을 두지 않는다.
목표가 `x = x`로 바뀌면 `rfl`로 증명하며 이 논증은 `A`의 모든 원소에 적용된다.

## 전칭명제의 사용
%%%
tag := "proofs-using-forall-with-apply"
file := "using-forall-with-apply"
%%%

이번에는 모든 원소에 관한 가정 `h : ∀ x : A, P x`로부터
주어진 원소 `a : A`에 관한 명제 `P a`를 보이자.
모든 원소에서 성립하는 사실은 `a`에서도 성립하므로 다음 추론을 사용할 수 있다.

$$`\bigl(\forall x \in A,\ P(x)\bigr) \Rightarrow P(a), \qquad a \in A.`

```savedLean
theorem use_forall (A : Type) (P : A → Prop) (a : A) :
    (∀ x : A, P x) → P a := by
  intro h
  apply h
```

첫 줄의 `intro h`는 함의의 전제 전체를 가정으로 받으므로,
가정은 `h : ∀ x : A, P x`이고 목표는 `P a`이다.
이어서 `apply h`를 쓰면 Lean은 `h`의 결론 `P x`를 목표 `P a`에 맞추어 원소를 `a`로 정한다.
이 예제에서는 추가로 확인할 전제가 없으므로 `apply h`에서 증명이 끝난다.

전칭명제를 증명하는 `intro x`에서 특정한 원소를 선택할 수는 없다.
어떤 원소에서도 성립하는 논증을 작성해야 하므로 `x`에는 `A`의 원소라는 조건만 주어진다.
앞의 `intro x`는 이처럼 임의의 원소를 도입한 것이고,
이번의 `apply h`는 이미 알고 있는 전칭명제를 주어진 원소에서 사용한 것이다.

{anchor "proofs-forall-application"}[]앞의 `use_forall` 증명에서는 `apply h` 대신 `exact h a`로 증명을 마칠 수도 있다.
`apply h`에서는 Lean이 목표를 보고 원소를 정하고,
`exact h a`에서는 사용할 원소를 직접 지정한다.
`h : ∀ x : A, P x`에 원소 `a : A`를 넣으면 `P a`의 증명을 얻으며,
이를 `h a`로 쓴다.
이 추론도 함수로 표현할 수 있다.
모든 원소에 적용되는 논증이 주어지면 원소 하나를 받아 그 원소에 관한 증명을 돌려줄 수 있기 때문이다.
예를 들어 모든 자연수 `n`에 대해 `0 ≤ n`을 증명한 논증은
`3`을 주면 `0 ≤ 3`의 증명을, `5`를 주면 `0 ≤ 5`의 증명을 제공한다.

Lean은 전칭명제의 증명도 원소를 받아 그 원소에서의 증명을 돌려주는 함수로 표현한다.
`h : ∀ x : A, P x`에 `a : A`를 넣으면 함수값 `h a`의 타입은 `P a`이다.
여기서는 넣은 원소에 따라 증명할 명제가 달라지므로 함수값의 타입도 인수에 따라 달라진다.
`∀ x : A, P x`는 이러한 함수의 타입을 나타내는 표기이다.

앞의 함의에서는 전제의 *증명*을 인수로 넣었고, 여기서는 `A`의 *원소*를 인수로 넣었다.
두 경우 모두 함수를 적용하지만 어떤 것을 넣어야 하는지는 함수의 타입에 따라 정해진다.

```savedLean
example
    (A : Type) (P : A → Prop) (a : A) :
    (∀ x : A, P x) → P a := by
  intro h
  exact h a
```

`P a`는 술어에 원소를 넣어 얻은 명제이고, `h a`는 그 명제가 성립한다는 증명이다.
따라서 `P a`가 목표일 때 `exact h a`로 그 증명을 제시한다.

전칭명제를 증명할 때의 `intro x`는 이 함수의 인수를 정하는 단계이다.
임의의 `x`를 받아 `P x`를 증명하는 논증 전체를 작성하면 모든 원소에 관한 증명을 얻는다.
예를 들어 앞의 “모든 원소는 자기 자신과 같다”는 증명도 함수식으로 적을 수 있다.

```savedLean
example (A : Type) : ∀ x : A, x = x :=
  fun x => by rfl
```

`fun x => ...`는 원소 `x`를 받고, `by rfl`은 그 원소에 관한 `x = x`의 증명을 만든다.
어느 원소를 넣어도 이 논증을 사용할 수 있으므로 전칭명제의 증명이 된다.

## 전칭명제와 함의의 결합
%%%
tag := "proofs-successive-application"
file := "successive-application"
%%%

전칭명제 안에 함의가 들어갈 수도 있다.
“모든 원소 $`x`에 대하여 $`P(x)`이면 $`Q(x)`이다”를 Lean으로 쓰면 `∀ x : A, P x → Q x`이다.
다음 절에서 다룰 집합의 포함 관계도 이런 형태로 표현한다.
이 사실을 알고 있고 특정한 원소 $`a`에서 $`P(a)`도 성립한다면,
먼저 전칭명제를 $`a`에서 사용하여 $`P(a) \Rightarrow Q(a)`를 얻고,
여기에 전제 $`P(a)`를 사용하여 $`Q(a)`를 얻는다.

우선 `apply`와 `exact`로 이 추론을 적어 보자.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  apply h
  exact hPa
```

목표가 `Q a`이므로 `apply h`는 원소를 `a`로 정하고,
그 원소에서 필요한 전제 `P a`를 새 목표로 삼는다.
이어서 `exact hPa`로 그 전제를 확인하면 증명이 끝난다.

이제 원소를 넣는 단계와 증명을 넣는 단계를 따로 적어 보자.
`h a`는 `P a → Q a`의 증명이므로 여기에 `hAtA`라는 이름을 붙일 수 있으며,
그 증명에 `hPa`를 넣은 `hAtA hPa`는 목표 `Q a`의 증명이 된다.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  have hAtA : P a → Q a := by
    exact h a

  exact hAtA hPa
```

`hAtA`를 따로 두지 않고 두 인수를 차례로 넣으면 `h a hPa`로 쓸 수 있다.
앞 절의 `f x y`와 마찬가지로 이 식은 `(h a) hPa`로 읽는다.
첫 번째 인수 `a`는 원소이고, 두 번째 인수 `hPa`는 그 원소에서 전제가 성립한다는 증명이다.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  exact h a hPa
```

세 증명은 같은 추론을 적은 것이며,
마지막의 `h a hPa`에도 원소를 대입하는 단계와 전제의 증명을 넣는 단계가 모두 들어 있다.

*보기* 자연수에서 정의된 함수 $`f`가 $`a<b`일 때마다 $`f(a)<f(b)`를 만족한다고 하자.
그러면 $`f(3)+2<f(5)+2`이다.

*풀이* 먼저 $`3<5`를 이 함수의 조건에 사용하여 $`f(3)<f(5)`를 얻는다.
여기에 앞에서 증명한 `add_two_preserves_lt`를 적용하면 원하는 부등식이 된다.
Lean에서는 결론에서 거꾸로 필요한 전제를 확인하자.

```savedLean
example (f : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b) :
    f 3 + 2 < f 5 + 2 := by
  apply add_two_preserves_lt
  apply hf 3 5
  exact comparisonProof
```

첫 줄은 앞의 정리를 $`f(3)`과 $`f(5)`에 적용하여 목표를 `f 3 < f 5`로 바꾼다.
둘째 줄에서는 함수의 조건 `hf`를 $`3`, $`5`에서 사용하므로 `3 < 5`가 남는다.
이는 첫 절의 `comparisonProof`로 이미 증명한 사실이다.
함수 $`f`의 구체적인 계산식을 몰라도 주어진 조건만으로 이 부등식을 얻을 수 있다.

# 연습문제
%%%
tag := "proofs-exercises"
file := "exercises"
%%%

앞의 문제 1, 2에 이어 전칭명제와 여러 정리의 사용을 연습하자.
다음 코드의 `sorry`를 증명으로 바꾸어 완성하라.
정리를 사용하는 단계는 먼저 `apply`와 `exact`로 나누어 적으라.
그런 다음 `exact h a`처럼 증명에 인수를 넣는 식으로도 같은 단계를 적어 보라.

*문제 3* 두 원소에 관한 술어 `R : A → A → Prop`를 생각하자.
모든 원소 `x`, `y`에서 `R x y`가 성립한다는 사실을 주어진 원소 `a`, `b`에서 사용하라.

```savedLean -keep
theorem exercise_relation_specialization
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry
```

:::solution
전칭명제의 증명에 첫 원소 `a`를 넣으면 `∀ y, R a y`의 증명을 얻는다.
여기에 두 번째 원소 `b`를 넣으면 목표의 증명이 된다.

```tryLean -keep
example (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  intro h
  exact h a b
```
:::

*문제 4* 모든 원소 $`x`에서 $`P(x)\Rightarrow Q(x)`가 성립한다고 하자.
또한 모든 원소에서 $`P(x)`가 성립하면 모든 원소에서 $`Q(x)`도 성립함을 보이라.

```savedLean -keep
theorem exercise_forall_implication
    (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  sorry
```

:::solution
두 가정을 받은 뒤 임의의 원소 `a`에서 `Q a`를 보이자.
첫 가정을 이 원소에서 사용하면 `P a`가 필요하며, 둘째 가정이 그 증명을 제공한다.

```tryLean -keep
example (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  intro hPQ hP
  intro a
  apply hPQ a
  exact hP a
```
:::

*문제 5* (대소 관계를 보존하는 함수)

자연수 함수 $`f`, $`g`가 각각 $`a<b`이면 $`f(a)<f(b)`, $`g(a)<g(b)`를 만족한다고 하자.

(1) $`a<b`이면 $`g(f(a))<g(f(b))`임을 증명하라.

(2) 첫 결과와 `comparisonProof`를 사용하여 $`g(f(3))<g(f(5))`를 보이라.

```savedLean -keep
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
```

*문제 6* (함수값의 범위)

모든 자연수 $`n`에 대하여 $`f(n)<g(n)`이고 $`g(n)<n+10`이라고 하자.
$`f(3)<13`임을 증명하라.
부등식의 추이성은 `Nat.lt_trans`로 사용할 수 있으며,
이 정리는 $`a<b`와 $`b<c`의 증명을 받아 $`a<c`의 증명을 돌려준다.

```savedLean -keep
theorem exercise_function_bound (f g : Nat → Nat)
    (hfg : ∀ n, f n < g n)
    (hg : ∀ n, g n < n + 10) :
    f 3 < 13 := by
  sorry
```

*문제 7* (부등식과 연속된 덧셈)

(1) $`a<b`이면 임의의 자연수 $`c`에 대하여 $`a+c<b+c`임을 증명하라.

(2) 첫 결과를 두 번 사용하여 $`(a+c)+d<(b+c)+d`를 보이라.

```savedLean -keep
theorem exercise_shift_lt (a b c : Nat)
    (hab : a < b) :
    a + c < b + c := by
  sorry

theorem exercise_two_shifts_lt (a b c d : Nat)
    (hab : a < b) :
    (a + c) + d < (b + c) + d := by
  sorry
```

*문제 8* (반복하여 유지되는 조건)

함수 $`f:A\to A`가 조건 $`P`를 유지한다고 하자.
즉 $`P(x)`이면 $`P(f(x))`이다.

(1) $`P(x)`이면 $`P(f(f(x)))`임을 증명하라.

(2) 첫 결과를 사용하여 $`f`를 네 번 적용한 뒤에도 $`P`가 성립함을 보이라.

```savedLean -keep
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
```

```savedLean
end ProofExamples
```
