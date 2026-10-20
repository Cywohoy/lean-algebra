import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Tactic.Rule

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "Lean의 기본 문법" =>

%%%
tag := "introduction"
file := "introduction"
%%%

이 절에서는 자연수와 함수를 정의하고 계산하면서 Lean에서 값을 다루는 방법을 익힌다.
이어서 명제를 표현하고, 원소마다 명제를 정하는 술어를 정의한다.
마지막에는 익숙한 정리를 사용하는 과정에서 증명에 이름을 붙이는 이유를 살펴보고,
이미 있는 증명을 제시하여 짧은 증명을 완성한다.
다음 절에서는 정리에 필요한 전제를 확인하고 중간 결론을 증명하는 방법을 익힌다.

```savedComment
Lean의 기본 문법: 값과 함수, 명제, 술어, 증명값의 순서로 익힌다.
명제와 증명을 구별하고 이미 있는 증명을 exact로 제시한다.
```

```savedImport
import AlgebraBook.Tactic.Rule
```

```savedLean -show
open scoped Ample
```

```savedLean -show
namespace IntroExamples
```

# 값과 타입
%%%
tag := "intro-values-and-types"
file := "values-and-types"
%%%

계산에서 같은 수를 여러 번 사용할 때는 그 수에 이름을 붙여 두면 편리하다.
예를 들어 $`3`을 `three`라고 정하면 `three + 2`를 계산하여 $`5`를 얻는다.
Lean에서도 수나 계산 결과를 *값*으로 다루며, `def`로 그 값에 이름을 붙일 수 있다.

```savedLean
def three : Nat := 3
def five : Nat := three + 2
```

Lean에서 값의 종류를 *타입*이라고 한다. `Nat`는 $`0`을 포함한 자연수의 타입이다.
`def three : Nat := 3`에서는 이름 `three` 뒤에 타입 `Nat`를 적고,
`:=` 오른쪽의 `3`을 그 값으로 정했다.
둘째 정의는 앞에서 정한 값을 사용하므로 `five`를 계산하면 `3 + 2`, 곧 `5`가 된다.

같은 숫자도 자연수로 사용할 때와 정수로 사용할 때 타입이 다르다.
정수의 타입은 `Int`이며, `(1 : Nat)`는 자연수 $`1`을,
`(1 : Int)`는 정수 $`1`을 나타낸다.
이처럼 `(값 : 타입)`으로 식의 타입을 직접 지정할 수 있으며,
`#check` 뒤에 식을 적으면 Lean이 확인한 타입을 볼 수 있다.

```lean (name := numeralTypes)
#check (1 : Nat)
```

```leanOutput numeralTypes
1 : Nat
```

앞의 `def three : Nat := 3`에서는 정의에 적은 타입에 따라 `3`을 자연수로 해석한다.
이처럼 주변 식에서 타입을 알 수 있으면 숫자마다 타입을 적을 필요는 없다.

값을 직접 계산하려면 식 앞에 `#eval`을 붙인다.

```lean (name := fiveValue)
#eval five
```

```leanOutput fiveValue
5
```

{anchor "intro-comments"}[]계산이나 증명의 각 단계에 설명을 덧붙이고 싶으면 *주석*을 사용한다.
`--`부터 그 줄의 끝까지는 주석이므로 Lean은 이 부분을 코드로 해석하지 않는다.

```savedLean
def five_commented : Nat :=
  -- 앞에서 정한 three에 2를 더한다.
  three + 2
```

설명이 여러 줄에 걸치면 `/-`와 `-/` 사이에 적을 수도 있다.
주석은 코드를 설명하는 글이며 Lean이 검사하는 코드에 포함되지 않는다.

# 함수 적용과 정의
%%%
tag := "intro-function-application"
file := "function-application"
%%%

수학에서 쓰는 함수값 $`f(x)`는 Lean에서 함수와 인수 사이에 공백을 두어 `f x`로 쓴다.
인수가 여러 항으로 이루어진 식이면 괄호로 묶으므로,
가령 $`f(x + 1)`은 `f (x + 1)`로 쓴다.

*보기* 두 자연수의 합을 구하는 함수 `add`를 정의하자.
두 자연수를 받으면 그 합을 돌려주므로 함수값도 자연수이다.

```savedLean
def add (x y : Nat) : Nat := x + y
```

`def`로 함수를 정의할 때는 함수 이름 `add` 뒤에 인수와 그 타입을 적는다.
`(x y : Nat)`는 `x`와 `y`가 모두 자연수라는 뜻으로,
`(x : Nat) (y : Nat)`를 줄여 쓴 것이다.
그다음의 `: Nat`는 함수값의 타입이며,
마지막으로 `:= x + y`에서 함수값을 두 인수의 합으로 정한다.

이 함수에 $`2`와 $`3`을 넣으면 $`5`를 얻는다.
앞에서 사용한 `#eval`로 함수값도 계산할 수 있다.

```lean (name := addValue)
#eval add 2 3
```

```leanOutput addValue
5
```

{anchor "intro-arguments-one-at-a-time"}[]`f x y`는 먼저 `f x`를 구한 뒤 그 결과인 함수에 `y`를 적용하는 식이므로
`(f x) y`로 읽는다. 이는 수학의 표기로 $`(f(x))(y)`에 해당한다.
앞의 `add`에 $`2`만 넣으면 자연수 $`y`에 $`2 + y`를 대응시키는 함수 `add 2`를 얻는다.
여기에 $`3`을 넣으면 두 인수를 차례로 적용한 것이므로
`(add 2) 3`은 `add 2 3`과 같은 값을 갖는다.

```lean (name := addGroupedValue)
#eval (add 2) 3
```

```leanOutput addGroupedValue
5
```

이처럼 자연수 하나를 받아 `Nat → Nat` 타입의 함수를 돌려주므로,
`add`의 타입은 `Nat → Nat → Nat`이다.
함수의 타입에서 화살표는 오른쪽부터 묶기 때문에 이를 `Nat → (Nat → Nat)`로 읽는다.
기호 `→`는 `\to`로 입력한다.

괄호는 하나의 인수로 묶을 범위를 나타내므로,
`add (2 + 1) 4`의 두 인수는 `2 + 1`과 `4`이다.
마찬가지로 `f (g x)`에서는 `g x` 전체가 `f`의 인수이며,
이는 수학에서 쓰는 $`f(g(x))`와 같다.

## 함수식
%%%
tag := "intro-defining-functions"
file := "defining-functions"
%%%

자연수 $`n`에 $`n+1`을 대응시키는 함수는 수학에서 $`n\mapsto n+1`로 나타낸다.
이처럼 인수에서 함수값을 정하는 식을 Lean에서는 `fun n => n + 1`로 쓴다.
함수도 하나의 값이므로 이 식에 이름을 붙일 수 있다.

```savedLean
def successor : Nat → Nat := fun n => n + 1
```

`Nat → Nat`는 자연수를 받아 자연수를 돌려주는 함수의 타입이다.
이 타입에 맞추어 Lean은 `n`이 자연수임을 추론하며,
타입을 직접 적을 때는 `fun (n : Nat) => n + 1`로 쓴다.
`successor 3`에서는 `n`에 `3`을 넣으므로 함수값은 `4`이다.

앞의 `add`처럼 인수를 이름 뒤에 적어도 같은 함수를 정의할 수 있다.

```lean +fresh -keep
def successor (n : Nat) : Nat := n + 1
```

두 선언은 같은 함수에 이름을 붙이는 두 방식이므로 실제 코드에서는 하나를 선택한다.

*보기* 가로와 세로의 길이가 자연수인 직사각형의 넓이를 구하자.
두 길이를 차례로 받는 함수를 정의한 뒤 가로를 $`3`으로 고정하면
세로의 길이만 받아 넓이를 구하는 함수를 얻는다.

```savedLean
def rectangleArea : Nat → Nat → Nat :=
  fun width height => width * height
def areaWithWidthThree : Nat → Nat := rectangleArea 3
```

```lean (name := rectangleAreaValue)
#eval areaWithWidthThree 4
```

```leanOutput rectangleAreaValue
12
```

`areaWithWidthThree`는 가로의 길이가 이미 정해져 있으므로 세로의 길이 하나만 받는다.
가령 `areaWithWidthThree 4`를 계산하면 `rectangleArea 3 4`, 곧 $`3\cdot4=12`를 얻는다.
이처럼 일부 인수를 먼저 정해 두면 남은 인수에 관한 함수를 만들 수 있다.

# 명제와 술어
%%%
tag := "intro-propositions-and-goals"
file := "propositions-and-predicates"
%%%

“$`3`은 $`5`보다 작다”는 참이고 “$`5`는 $`3`보다 작다”는 거짓이다.
이처럼 참인지 거짓인지가 정해지는 문장을 *명제*라고 한다.
두 문장을 Lean으로 쓰면 각각 `3 < 5`와 `5 < 3`이며,
명제의 타입은 `Prop`이다.

앞에서 자연수에 이름을 붙였던 것처럼 명제에도 이름을 붙일 수 있다.

```savedLean
def comparison : Prop := 3 < 5
def reversedComparison : Prop := 5 < 3
```

두 정의에서 `:=` 오른쪽에 적은 것은 명제이다.
`comparison`은 참인 명제에, `reversedComparison`은 거짓인 명제에 붙인 이름이며
둘 모두 타입이 `Prop`이다.
명제를 표현하는 것과 그 명제가 성립함을 증명하는 것은 구별된다.

{anchor "intro-predicates"}[]앞의 명제 `3 < 5`에서는 비교하는 두 수가 정해져 있다.
이번에는 “자연수 $`n`은 $`0`보다 크다”라는 조건을 생각하자.
$`n=3`을 넣으면 참인 명제 $`0<3`을 얻고,
$`n=0`을 넣으면 거짓인 명제 $`0<0`을 얻는다.
이처럼 원소를 정할 때마다 그 원소에 관한 명제를 얻는 조건을 *술어(predicate)*라고 한다.

앞에서는 자연수를 받아 자연수를 돌려주는 함수를 정의했다.
이번에는 자연수를 받아 명제를 돌려주도록 하면 위 조건을 표현할 수 있다.
자연수 $`n`에 $`0<n`을 대응시키는 함수를 `positive`라고 정의하자.

```savedLean
def positive : Nat → Prop := fun n => 0 < n
```

함수의 타입 `Nat → Prop`은 인수가 자연수이고 함수값이 명제라는 뜻이다.
`fun n => 0 < n`은 $`n\mapsto (0<n)`을 나타내므로
`positive 3`은 명제 `0 < 3`이고 `positive 0`은 명제 `0 < 0`이다.
이렇게 명제를 정하는 것과 그 명제가 참임을 증명하는 것은 별개의 일이다.
인수를 함수 이름 뒤에 적는 방식으로는 다음과 같이 쓸 수도 있다.

```lean +fresh -keep
def positive (n : Nat) : Prop := 0 < n
```

두 표기에서 `positive n`의 뜻은 같다.
이후에도 술어를 정의할 때는 함수의 타입을 한눈에 볼 수 있도록
`Nat → Prop`처럼 타입을 먼저 적고 `fun`으로 원소 조건을 나타내겠다.

일반적으로 타입 $`A`의 원소에 명제를 대응시키는 술어는 `A → Prop` 타입의 함수이다.
`P : A → Prop`가 주어지면 `P`는 술어이고,
원소 `x : A`를 넣어 얻는 `P x`는 그 원소에 관한 명제이다.
따라서 `positive`는 술어이고 `positive 3`은 명제이며,
`positive 3`이 성립함을 보이려면 $`0<3`을 증명해야 한다.

*보기* 방정식 $`n^2=a`의 해라는 조건을 술어로 나타내자.
$`a`를 고정하고 나면 각 자연수 $`n`에 명제 $`n\cdot n=a`가 대응된다.

```savedLean
def solvesSquare (a : Nat) : Nat → Prop :=
  fun n => n * n = a
```

`solvesSquare 9`는 “제곱이 $`9`인 자연수”라는 조건이므로 타입이 `Nat → Prop`이다.
여기에 $`3`을 넣은 `solvesSquare 9 3`은 명제 $`3\cdot3=9`이고,
$`4`를 넣은 `solvesSquare 9 4`는 명제 $`4\cdot4=9`이다.
첫 명제는 참이고 둘째 명제는 거짓이다.
이 술어로 해의 조건을 표현할 수 있으며, 특정한 수가 해임을 보이려면 해당 명제를 증명해야 한다.

# 증명과 값
%%%
tag := "intro-proofs-as-values"
file := "proof-values"
%%%

수학에서 한 번 증명한 정리는 다른 문제에서도 사용할 수 있다.
예를 들어 직각삼각형의 변의 길이를 구할 때는 피타고라스 정리를 사용하며,
문제를 풀 때마다 이 정리를 처음부터 증명하지는 않는다.

{anchor "intro-reusing-proof-values"}[]*보기* 직각삼각형에서 직각을 낀 두 변의 길이가 각각 $`3`, $`4`일 때 빗변의 길이를 구하자.

*풀이* 빗변의 길이를 $`c`라고 하면 피타고라스 정리에 따라
$`c^2=3^2+4^2=25`이다. 길이 $`c`는 양수이므로 $`c=5`를 얻는다.

이 풀이에서 피타고라스 정리를 쓸 수 있는 것은 주어진 삼각형이 직각삼각형이기 때문이다.
두 변의 길이가 $`3`, $`4`라는 정보만으로는 나머지 변의 길이를 구할 수 없으며,
두 변이 이루는 각이 직각이라는 조건도 확인해야 한다.
따라서 정리를 사용하는 단계에는 수와 함께 정리의 가정이 성립한다는 근거가 필요하다.

{anchor "intro-pythagoras-proof-steps"}[]이 풀이에서 어떤 사실을 근거로 다음 결론을 얻었는지 살펴보자.
삼각형이 직각삼각형이라는 가정에 `hRight`라는 이름을 붙이면,
피타고라스 정리에 이 증명을 사용하여 $`c^2=25`의 증명 `hSquare`를 얻는다.
이어서 길이가 음이 아니라는 사실과 `hSquare`를 사용하여
$`c=5`의 증명 `hLength`를 얻는다.

:::table +header (align := left)
*
  * 증명의 이름
  * 증명하는 내용
  * 사용하는 근거
*
  * `hRight`
  * 직각삼각형이다.
  * 문제의 가정
*
  * `hSquare`
  * $`c^2=25`
  * 피타고라스 정리, `hRight`
*
  * `hLength`
  * $`c=5`
  * 제곱의 비교, `hSquare`
:::

마지막 단계에서는 $`5^2=25`를 사용하여 $`c^2=5^2`를 얻는다.
두 수가 음이 아니므로 제곱이 같다는 사실에서 두 수가 같음을 결론 내릴 수 있다.

Lean에서도 이처럼 증명에 이름을 붙이고 다른 정리에 사용한다.
수나 함수처럼 증명을 이름으로 가리키고 인수로 쓸 수 있다는 뜻에서
*증명도 값으로 다룬다*고 말한다.

{anchor "intro-proof-value-notation"}[]앞에서 `three : Nat`로 이름과 타입을 구별했듯이,
명제 $`P`의 증명에 `h`라는 이름을 붙이면 `h : P`로 쓴다.
가령 `h : 0 < 3`에서 `0 < 3`은 명제이고 `h`는 그 명제의 증명이다.
Lean에서는 명제를 그 증명들이 속하는 타입으로 사용한다.
따라서 `P : Prop`라고 쓰면 명제를 정한 것이고, `h : P`라고 쓰면 그 명제의 증명을 가리킨다.

{anchor "intro-proposition-and-proof"}[]이 구별을 실제 선언에서 살펴보자.
앞에서 정의한 명제 `comparison`과 그 명제의 증명을 나란히 적으면 다음과 같다.

```lean +fresh -keep
def comparison : Prop := 3 < 5
theorem comparisonProof : 3 < 5 := by decide
```

```savedLean -show
theorem comparisonProof : 3 < 5 := by decide
```

첫 선언은 명제 `3 < 5`에 이름을 붙인다.
둘째 선언에서는 `theorem` 뒤에 증명의 이름을, `:` 뒤에 증명할 명제를 적는다.
`:=` 오른쪽의 `by` 아래에는 증명 단계를 적는다.
이때 사용하는 명령을 *전술(tactic)*이라고 한다.
여기서 쓴 `decide`는 두 수의 비교를 계산하여 증명을 만든다.
이 선언이 끝나면 `comparisonProof`를 `3 < 5`의 증명으로 사용할 수 있다.

웹에서는 코드 오른쪽 위의 ‘단계 보기’를 누르면 각 전술을 실행한 뒤의 가정과 목표를 확인할 수 있다.
코드 안의 전술을 누르면 그 단계로 바로 이동한다.

증명도 `def`로 정의할 수 있지만 명제의 증명을 선언할 때는 보통 `theorem`을 사용한다.
이 교재에서도 명제나 함수의 정의에는 `def`를, 명제의 증명에는 `theorem`을 사용한다.
`#check comparison`에서는 `comparison : Prop`를 확인하고,
`#check comparisonProof`에서는 `comparisonProof : 3 < 5`를 확인할 수 있다.

## 증명의 제시
%%%
tag := "intro-presenting-proofs"
%%%

이제 `3 < 5`를 증명할 때 방금 얻은 증명을 사용해 보자.
`example`은 설명을 위한 이름 없는 `theorem`이며,
이후에 이름으로 참조할 필요가 없는 증명에 사용한다.

```savedLean
example : 3 < 5 := by
  exact comparisonProof
```

`by` 아래에서 아직 증명해야 하는 명제를 *목표*라고 한다.
위 예제의 목표는 `3 < 5`이고, `exact comparisonProof`는 그 목표에 맞는 증명을 제시하는 단계이다.
`exact` 뒤의 식이 목표의 증명인지 Lean이 확인하면 증명이 끝난다.
여기에 `comparison`을 적으면 타입이 `Prop`인 명제를 제시하게 되므로,
타입이 `3 < 5`인 증명이 필요한 자리를 채울 수 없다.

{anchor "proofs-assumptions-and-goals"}[]이번에는 자연수 `n`이 양수라는 사실이 가정으로 주어졌다고 하자.
그 사실도 증명에 이름을 붙여 사용할 수 있다.

```savedLean
example (n : Nat)
    (h : 0 < n) :
    0 < n := by
  exact h
```

`h : 0 < n`은 `h`가 부등식의 증명이라는 뜻이다.
이 예제에서는 그 증명을 인수로 받으므로 `0 < n`이 성립한다는 가정 아래에서 논증한다.
편집기에서 `by` 뒤의 증명 상태를 확인하면 다음과 같다.

```
n : Nat
h : 0 < n
⊢ 0 < n
```

위쪽에는 사용할 수 있는 원소 `n`과 증명 `h`가 있고,
`⊢` 뒤에는 증명할 명제가 있다.
목표와 가정에 같은 부등식이 적혀 있어도 역할은 서로 다르다.
목표는 증명을 요구하며 `h`는 그 요구를 충족하는 증명이므로 `exact h`로 마친다.

같은 명제라도 정의에서 붙인 이름으로 쓰거나 그 조건을 풀어 쓸 수 있다.
예를 들어 `positive n`은 `0 < n`으로 정의했으므로,
`h : positive n`이 주어지면 그 증명을 목표 `0 < n`에 그대로 사용할 수 있다.

```savedLean
example (n : Nat)
    (h : positive n) :
    0 < n := by
  exact h
```

여기서 `exact`는 글자가 똑같은지만 비교하지 않는다.
`positive`의 정의를 확인하면 가정과 목표가 같은 명제이므로 `h`를 받아들인다.
반대로 `0 < n`의 증명도 `positive n`을 보이는 데 사용할 수 있다.

*확인* `positive`, `positive 3`, `h : positive 3`에서 술어, 명제, 증명을 각각 구별하라.
`positive`는 자연수를 받아 명제를 만드는 술어이고,
`positive 3`은 `0 < 3`이라는 명제이며 `h`는 바로 그 명제의 증명이다.
{ref "using-proofs"}[다음 절]에서는 이미 있는 증명을 다른 정리에 사용하여 새 결론을 얻는다.

# 연습문제
%%%
tag := "introduction-exercises"
file := "exercises"
%%%

아래 코드의 `sorry`는 독자가 채울 증명이다. Lean은 이 부분을 미완성으로 받아들이고 경고를 표시한다.
각 `sorry`를 실제 증명으로 바꾸어 문제를 완성하라.
구체적인 수의 계산에는 `decide`를, 이미 주어진 증명을 제시할 때에는 `exact`를 사용할 수 있다.

*문제 1* (함수의 일부 인수)

`rectangleArea 3`에 $`4`를 넣은 값과 `areaWithWidthThree 4`의 값이 같음을 확인하고,
그 값이 $`12`임을 증명하라.

```savedLean -keep
theorem exercise_partial_area :
    areaWithWidthThree 4 = rectangleArea 3 4 := by
  sorry

theorem exercise_area_value :
    areaWithWidthThree 4 = 12 := by
  sorry
```

*문제 2* (술어와 그 증명)

먼저 $`4\cdot4=16`을 확인하고, 이 증명으로 $`4`가 방정식 $`n^2=16`의 해임을 보이라.
이어서 `h : solvesSquare a n`이 주어졌을 때 이 증명을 사용하여 $`n\cdot n=a`를 보이라.
마지막 증명에서는 $`a`와 $`n`의 구체적인 값이 주어지지 않는다.

```savedLean -keep
theorem exercise_four_square : 4 * 4 = 16 := by
  sorry

theorem exercise_four_solves_square :
    solvesSquare 16 4 := by
  sorry

theorem exercise_square_proof (a n : Nat)
    (h : solvesSquare a n) :
    n * n = a := by
  sorry
```

```savedLean -show
end IntroExamples
```
