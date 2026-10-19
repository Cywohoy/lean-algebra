import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Meta.Notation
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Auto
import Lean.Elab.Tactic.Ext
import AlgebraBook.Tactic.Ext
import AlgebraBook.Tactic.Rules
import AlgebraBook.Tactic.Unfold

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "집합의 구성" =>

%%%
tag := "sets"
file := "sets"
%%%

이 절의 목표는 집합의 원소와 포함 관계를 Lean으로 나타내고,
익숙한 집합의 성질을 직접 증명하는 것이다.
앞의 두 절에서 배운 술어와 증명의 사용법을 바탕으로 집합을 정의하고,
그 성질을 증명하면서 새로운 표기와 전술을 익히자.

```savedComment
집합의 구성: 조건으로 집합을 나타내고 기본 성질을 직접 증명한다.
연습문제의 sorry는 독자가 채울 빈 증명이다.
```

```savedImport
import AlgebraBook.Meta.Notation
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Auto
import Lean.Elab.Tactic.Ext
import AlgebraBook.Tactic.Ext
import AlgebraBook.Tactic.Rules
import AlgebraBook.Tactic.Unfold
```

```savedLean
namespace Course
```

# 집합과 술어
%%%
tag := "sets-sets-as-predicates"
file := "sets-as-predicates"
%%%

양의 자연수들을 모으면 다음 집합을 얻는다.

$$`\{n \in \mathbb{N} : 0 < n\}`

이 집합은 술어 `positive`의 조건을 만족하는 자연수들을 모은 것이다.
$`\mathbb{N}`에는 Lean의 `Nat`와 마찬가지로 $`0`도 포함된다.

일반적으로 $`A` 위의 술어 $`P`가 주어졌을 때,
$`P(x)`가 성립하는 원소 $`x`들을 모은 집합을 $`S_P`라 하면 다음과 같다.

$$`S_P = \{x \in A : P(x)\}, \qquad x \in S_P \iff P(x).`

따라서 $`x \in S_P`를 보이는 것은 $`P(x)`를 보이는 것과 같다.
반대로 집합 $`S`가 주어지면 “$`x \in S`”가 $`x`에 관한 술어가 된다.
이처럼 집합은 어느 원소가 속하는지를 나타내는 술어로 표현할 수 있으므로,
Lean에서 사용할 집합도 이 방식으로 정의하겠다.

```savedLean
def Set (A : Type _) := A → Prop
```

```savedLean -show
attribute [implicit_reducible] Set
```

`Set A`는 `A → Prop`의 다른 이름으로, `A`의 원소들로 이루어진 집합을 `A` 위의 술어로 나타낸다.
여기서 `Type _`의 `_`는 Lean이 타입의 수준을 추론하도록 두는 표시이다.
지금은 `A`가 원소의 타입을 정한다는 점에 주목하자.
`S : Set A`일 때 `S x`는 $`x`가 $`S`에 속한다는 명제이다.
예를 들어 `Set Nat`은 자연수의 부분집합들을 나타내는 타입이다.

{ref "intro-predicates"}[술어]에서 사용한 양의 자연수의 술어를 이 절에서도 `positive`로 정의하자.

```savedLean
def positive : Nat → Prop := fun n => 0 < n
```

*보기* 이 술어로 양의 자연수의 집합 `positives`를 정의하자.

```savedLean
def positives : Set Nat := positive
```

`Set Nat`는 `Nat → Prop`이므로 술어 `positive`를 그대로 사용할 수 있다.
여기서는 조건을 나타낼 때의 이름과 집합을 나타낼 때의 이름을 구별하여 붙였다.
`positives n`의 정의를 펼치면 `positive n`, 곧 `0 < n`이므로
`positives`가 바로 위의 집합 $`\{n \in \mathbb{N} : 0 < n\}`이다.

## 원소 표기와 타입
%%%
tag := "sets-membership-notation"
file := "membership-notation"
%%%

이제 $`x`가 $`S`에 속한다는 명제 `S x`를 익숙한 기호 `x ∈ S`로 써 보자.
이를 위해 `instance`로 기호와 정의를 연결한다.
처음 읽을 때는 `instance`의 세부 문법을 모두 이해할 필요는 없으며,
아래 선언이 `x ∈ S`를 `S x`와 같은 뜻으로 정한다는 점만 알고 넘어가도 좋다.
뒤에 나오는 `∅`, `⊆`, `∩`, `∪`의 연결 선언도 같은 역할을 하므로
기호가 어떤 정의를 뜻하는지 확인하고 세부 문법은 필요한 때 다시 살펴보라.

```savedLean
instance {A : Type _} : Membership A (Set A) where
  mem S x := S x
```

`Membership`에는 원소 관계의 뜻을 정하는 함수 `mem`이 들어 있다.
위의 `instance`에서 `mem S x := S x`로 정했으므로,
`S : Set A`에 대한 `x ∈ S`는 `S x`를 뜻한다.

{anchor "sets-types-and-sets"}[]양의 자연수의 집합에 속하는 원소를 다룰 때는
자연수 `n : Nat`를 정하고 `n ∈ positives`가 성립하는지 살펴본다.
여기서 `n : Nat`는 `n`의 타입을 밝히며,
`n ∈ positives`는 그 자연수가 양수라는 명제이다.
이 명제는 `n`이 양수인지 확인하기 전에도 쓸 수 있다.
예를 들어 `0 ∈ positives`도 명제이며 그 뜻은 `0 < 0`이다.
`0 ∈ positives`는 쓸 수 있는 명제이지만 참인 명제는 아니다.
자연수 `n`이 실제로 이 집합에 속한다고 주장하려면 `h : n ∈ positives`와 같은 증명이 필요하다.

일반적으로 `S : Set A`에서 타입 `A`는 어떤 대상을 원소로 다루는지 정하고,
집합 `S`는 그 원소에 대한 조건을 정한다.
`x : A`가 주어지면 `x ∈ S`라는 명제를 만들 수 있으며,
그 명제를 증명하여 `x`가 `S`에 속함을 보인다.
앞의 예에서 `Nat`은 자연수의 타입이고 `positives`는 그 위에 정의한 집합이다.
또한 `Set Nat`은 `positives`를 비롯한 자연수의 부분집합들이 속하는 타입이다.

## 정의와 원소 조건
%%%
tag := "sets-membership-simplification"
%%%

가령 `n ∈ positives`의 정의를 차례로 펼치면
`positives n`, `positive n`, `0 < n`이 된다.
수학에서도 $`n \in \{m \in \mathbb{N} : 0 < m\}`이라고 하면 $`0 < n`이라는 뜻이므로
$`3`이 이 집합에 속함을 보이려면 $`0 < 3`을 보이면 된다.

`change`는 목표를 정의상 같은 명제로 바꾸는 전술이며,
`decide`는 명제의 참과 거짓을 계산하여 참임을 확인하는 전술이다.
아래에서는 먼저 원소 조건을 부등식으로 드러낸 뒤 두 구체적인 수를 비교한다.

```savedLean
example : 3 ∈ positives := by
  change 0 < 3
  decide
```

`change 0 < 3` 이후의 목표는 `0 < 3`이며 `decide`가 이 부등식을 확인하여 증명을 마친다.
변수가 들어 있는 `2 ≤ x + 2`처럼 모든 자연수 `x`에서 성립함을 보여야 하는 부등식은
구체적인 두 수를 비교하는 계산만으로 확인되지 않는다.
이런 명제에는 자연수의 성질을 사용한 증명이 필요하다.

집합을 `fun n => 2 ≤ n`으로 정하면 원소 `x`가 그 집합에 속한다는 조건은 `2 ≤ x`이다.
이처럼 원소 표기를 실제 조건으로 풀 때는 전술 `dsimp`를 사용할 수 있다.
`dsimp`는 교재에서 정한 원소 표기 `x ∈ S`를 함수 적용 `S x`로 풀어 계산한다.

```savedLean -show
@[simp] theorem mem_def {A : Type} (S : Set A) (x : A) :
    (x ∈ S) = S x := rfl

attribute [course_arith_simp] mem_def positives positive

```

`dsimp`는 정의를 풀거나 계산하는 규칙을 사용하여
목표와 정의상 같은 조건을 드러낸다.
펼칠 정의의 이름을 대괄호 안에 적으면 그 정의를 사용할 수 있으므로,
아래에서는 집합 `positives`와 술어 `positive`를 차례로 펼쳐 보자.

```savedLean
example
    (n : Nat)
    (h : 0 < n) :
    n ∈ positives := by
  dsimp [positives]
  dsimp [positive]
  exact h

example
    (n : Nat)
    (h : n ∈ positives) :
    0 < n := by
  dsimp [positives] at h
  dsimp [positive] at h
  exact h
```

첫 증명에서 `dsimp [positives]`는 원소 표기를 풀고 `positives`의 정의를 펼쳐
목표를 `positive n`으로 바꾼다.
이어서 `dsimp [positive]`로 술어의 정의를 펼치면 목표가 `0 < n`이 되어
가정 `h`로 증명을 마칠 수 있다.
둘째 증명에서는 `at h`를 붙여 같은 과정을 가정에 적용하므로,
`h : n ∈ positives`에서 `h : positive n`을 거쳐 `h : 0 < n`을 얻는다.

정의의 이름을 적지 않고 원소 조건을 한 층씩 확인하려면
교재에서 준비한 전술 `expand`를 사용할 수 있다.
이 전술은 식의 각 부분에서 가장 바깥에 있는 교재나 현재 풀이 파일의 정의를 찾아 펼치고,
인수 대입 같은 계산을 함께 처리한다.
새로 나타난 정의는 다음 `expand`까지 남겨 둔다.

`change`, `dsimp`, `expand`는 표현을 바꾼 뒤 양변이 정의상 같은 등식이 남으면 증명을 마친다.
아래에서는 부등식 `0 < n`이 남으므로 가정 `h`를 사용한다.

```savedLean
example
    (n : Nat)
    (h : 0 < n) :
    n ∈ positives := by
  expand
  expand
  exact h
```

첫 번째 `expand`는 원소 표기를 풀고 집합 `positives`의 정의를 펼쳐
목표를 `positive n`으로 바꾼다.
두 번째 `expand`는 술어 `positive`의 정의를 펼치고 `n`을 대입하여 `0 < n`을 얻는다.
따라서 이 예제의 두 `expand`는 앞의 `dsimp [positives]`와 `dsimp [positive]`에 각각 대응한다.
이제 가정 `h`로 증명을 마칠 수 있다.
가정의 원소 조건을 펼칠 때는 `dsimp at h`와 같이 `expand at h`로 쓴다.


정의들을 이어서 펼치려면 `expand!`를 사용할 수도 있다.
아래에서는 `positives`와 `positive`를 차례로 펼쳐 원소 조건을 얻는다.

```savedLean
example
    (n : Nat)
    (h : 0 < n) :
    n ∈ positives := by
  expand!
  exact h
```

세 전술은 모두 정의상 같은 표현 사이에서 목표를 바꾸며 다음과 같이 구분할 수 있다.

:::table +header (align := left)
*
  * 전술
  * 정리 방법
  * 위 원소 조건에서의 결과
*
  * `change 0 < n`
  * 바꿀 목표를 직접 적는다.
  * `0 < n`
*
  * `dsimp [positives]`, 이어서 `dsimp [positive]`
  * 펼칠 정의를 지정한다.
  * 첫 호출에서 `positive n`, 둘째 호출에서 `0 < n`
*
  * `expand`
  * 정의를 자동으로 찾아 한 층만 펼친다.
  * 첫 호출에서 `positive n`, 둘째 호출에서 `0 < n`
:::

순서쌍의 성분과 함수값 등 다른 식을 정리하는 예제는
{ref "tactic-unfold-auto"}[부록의 정의와 계산]에서 다룬다.

## 전체집합과 공집합
%%%
tag := "sets-universal-and-empty-sets"
file := "universal-and-empty-sets"
%%%

타입 $`A`의 모든 원소를 모은 집합이 전체집합이고, 원소가 하나도 없는 집합이 공집합이다.
집합을 술어로 나타내고 있으므로 전체집합의 조건은 항상 참이고 공집합의 조건은 항상 거짓이다.

```savedLean
def whole (A : Type) : Set A := fun _ => True
def empty (A : Type) : Set A := fun _ => False
instance {A : Type} : EmptyCollection (Set A) where
  emptyCollection := empty A
```

`True`는 항상 참인 명제이고 `False`는 거짓인 명제이다.
두 함수에서는 원소의 값이 필요하지 않으므로 `fun _ => ...`와 같이 이름을 생략했다.
자연수의 전체집합은 `whole Nat`, 공집합은 `empty Nat`로 쓴다.
이때 `Nat`은 자연수의 타입이고 `whole Nat : Set Nat`은 모든 자연수를 포함하는 집합이다.
원소 조건이 항상 참이므로 어느 `n : Nat`에 대해서도 `n ∈ whole Nat`이 성립한다.

마지막 `instance`는 공집합의 기호 `∅`를 `empty A`에 연결한다.
`∅`만으로 원소의 타입을 알 수 없을 때는 `(∅ : Set Nat)`와 같이 타입을 덧붙이며,
이 경우에는 `empty Nat`와 같은 집합을 나타낸다.

## Advanced: 원소의 타입과 러셀의 역설
%%%
tag := "advanced-set-types"
number := false
%%%

수학에서는 $`\{1, 2\}`처럼 집합을 쓰면서 원소가 속하는 범위를 따로 표시하지 않기도 한다.
그러나 Lean에서 집합을 술어로 정의하려면 어떤 타입의 원소에 그 조건을 적용할지 정해야 하므로
`Set A`의 `A`로 그 범위를 나타낸다.

원소의 범위를 구별하는 것은 집합을 아무 제한 없이 만드는 데서 생기는 모순과도 관련이 있다.
모든 집합을 원소로 갖는 집합 `U`가 있고,
그 안에서 조건을 만족하는 원소들을 골라 집합을 만들 수 있다고 가정해 보자.
그러면 다음과 같은 집합을 만들게 된다.

$$`R = \{S \in U : S \notin S\}.`

`R`은 자기 자신에 속하지 않는 집합들을 모은 것이다.
`U`는 모든 집합을 포함한다고 가정했으므로 `R`도 `U`에 속한다.
이제 `R`이 자기 자신에 속하는지 물어 보자.

`R`이 자기 자신에 속한다고 하면 `R`의 원소 조건에 따라 자기 자신에 속하지 않아야 한다.
반대로 자기 자신에 속하지 않는다고 하면 `R`도 `U`의 원소이고 그 조건을 만족하므로 `R`에 속해야 한다.
어느 쪽으로 생각해도 모순이 생기며, 이를 *러셀의 역설*이라고 한다.

이러한 모순을 피하려면 모든 집합을 한꺼번에 모으는 방식과
조건으로 집합을 만드는 방식을 아무 제한 없이 함께 허용해서는 안 된다.
이 교재에서는 원소의 타입 `A`를 먼저 정하고, 그 타입 위의 조건으로 집합을 만든다.
`S : Set A`는 `A`의 원소에 적용하는 함수이므로
타입이 다른 `S` 자신을 그대로 원소로 넣는 식은 쓸 수 없다.

집합을 원소로 갖는 집합을 만들 때는 원소의 타입도 집합의 타입으로 정한다.
예를 들어 `U : Set (Set Nat)`라고 하면 `U`의 원소는 `Set Nat` 타입의 집합, 곧 자연수의 집합이다.
이렇게 원소와 집합의 타입을 구별하므로 러셀의 역설에 등장한 `S ∈ S`를 그대로 만들 수 없다.

# 포함 관계와 함의의 증명
%%%
tag := "sets-subsets"
file := "subsets"
%%%

*정의* 집합 $`S`의 모든 원소가 집합 $`T`의 원소이면 $`S`가 $`T`의
*부분집합*이라고 한다. 이를 $`S \subseteq T`로 나타낸다.

```savedLean
def Subset {A : Type} : Set A → Set A → Prop :=
  fun S T => ∀ x, x ∈ S → x ∈ T
instance {A : Type} : HasSubset (Set A) where
  Subset := Course.Subset
```

앞에서와 같이 기호와 정의를 연결했으므로,
`S ⊆ T`는 `Subset S T`, 곧 `∀ x, x ∈ S → x ∈ T`를 뜻한다.

따라서 `S ⊆ T`를 증명하려면 임의의 원소 $`x`를 택하고,
$`x \in S`를 가정하여 $`x \in T`를 보이면 된다.

{anchor "sets-proving-universal-statements-and-implications"}[]앞 절의 {ref "proofs-universal-statements"}[전칭명제의 증명]에서와 같이,
먼저 `intro x`로 임의의 원소를 도입한 뒤 그 원소에 관한 명제를 보인다.
이 예제에서는 원소를 도입한 뒤의 목표가 `x ∈ S → x ∈ S`이므로
`intro hx`로 함의의 전제도 가정으로 받아야 한다.

*정리* 모든 집합은 자기 자신의 부분집합이다.

*증명* 임의의 원소 $`x`에 대하여 $`x \in S`를 가정하면,
보일 명제도 $`x \in S`이므로 이 가정을 그대로 쓰면 된다.

```savedLean
theorem subset_refl {A : Type} (S : Set A) :
    S ⊆ S := by
  expand
  -- 포함 관계: ∀ x : A, x ∈ S → x ∈ S
  intro x
  intro hx
  exact hx
```

`theorem`으로 정리에 이름을 붙였으므로,
이후에는 `subset_refl S`로 이 포함 관계의 증명을 사용할 수 있다.
각 증명 단계에서 가정과 목표는 다음과 같이 변한다.

1. `expand`로 포함 관계의 정의를 펼치면 전칭명제 `∀ x : A, x ∈ S → x ∈ S`를 얻는다.
2. `intro x`로 임의의 원소 `x : A`를 택하면 목표는 `x ∈ S → x ∈ S`가 된다.
3. `intro hx`로 가정 `hx : x ∈ S`를 도입하면 남은 목표는 `x ∈ S`이다.
4. `exact hx`로 이 가정을 사용하면 목표와 같은 명제를 얻으므로 증명이 끝난다.

이 예제의 `expand`는 목표에 들어 있는 전칭명제의 구조를 보여 주기 위해 썼다.
Lean은 `intro`를 처리할 때도 포함 관계의 정의를 펼치므로,
`expand`를 생략하고 바로 `intro x`와 `intro hx`를 써도 된다.

`intro x`와 `intro hx`는 `intro x hx`로 한 번에 쓸 수 있으며,
이후 증명에서는 두 단계를 이렇게 묶어 쓰겠다.
웹에서는 증명 코드의 전술을 눌러 각 단계의 가정과 목표를 확인할 수 있다.

## 전체집합과 공집합의 포함 관계
%%%
tag := "sets-basic-subsets"
%%%

전체집합과 공집합의 원소 조건은 각각 `True`와 `False`이므로
이 두 명제를 증명에 사용하는 방법을 살펴보자.

*정리* 모든 집합은 전체집합의 부분집합이다.

*증명* 임의의 원소 $`x \in S`를 택하면 $`x`는 $`A`의 원소이므로 전체집합에 속한다.
Lean에서는 `x ∈ whole A`의 정의를 펼치면 `True`가 되므로 항상 참인 이 명제를 증명하면 된다.
Lean은 `True`의 증명 `True.intro`를 제공하므로 `exact True.intro`로 증명을 마칠 수 있다.
전술 `trivial`도 이 목표를 해결하며 아래에서는 이 전술을 사용한다.

```savedLean
theorem subset_whole {A : Type} (S : Set A) :
    S ⊆ whole A := by
  intro x hx
  trivial
```

`intro x hx` 이후의 목표는 `x ∈ whole A`, 곧 `True`이다.
`x : A`이면 언제나 전체집합에 속하므로 `trivial`은 가정 `hx`를 사용하지 않고 증명을 마친다.

*정리* 공집합은 모든 집합의 부분집합이다.

*증명* 임의의 원소 $`x`에 대하여 $`x \in \varnothing`라고 가정하자.
공집합에는 원소가 없으므로 이 가정에서 모순이 생기며, 따라서 $`x \in S`라는 결론도 얻을 수 있다.
공집합에는 원소가 없으므로 “공집합에 속하면서 $`S`에는 속하지 않는 원소”도 없다는 뜻이다.

Lean에서 `x ∈ ∅`의 정의를 펼치면 모순을 나타내는 명제 `False`가 된다.
따라서 가정 `hx : x ∈ ∅`는 `False`의 증명으로 사용할 수 있다.

`False`의 증명에서 임의의 명제의 증명을 얻는 원리를 `False.elim`이라고 한다.
따라서 `False.elim hx`는 목표 `x ∈ S`의 증명이며, `exact False.elim hx`로 증명을 마칠 수 있다.
아래에서는 모순인 가정을 찾아 목표를 해결하는 전술 `contradiction`을 사용한다.

```savedLean
theorem empty_subset {A : Type} (S : Set A) :
    ∅ ⊆ S := by
  intro x hx
  contradiction
```

`intro x hx` 이후의 목표는 `x ∈ S`이며, 가정 `hx`의 명제는 정의에 따라 `False`이다.
따라서 `contradiction`이 바로 그 가정을 사용하여 증명을 마친다.

## 포함 관계의 추이성
%%%
tag := "sets-using-subset-proofs"
file := "using-subset-proofs"
%%%

*정리* $`S \subseteq T`이고 $`T \subseteq U`이면 $`S \subseteq U`이다.

*증명* $`x \in S`라고 하면 $`S \subseteq T`이므로 $`x \in T`이다.
또한 $`T \subseteq U`이므로 $`x \in U`를 얻는다.

Lean에서도 원소를 택하는 단계와 포함 관계를 사용하는 단계를 나누어 적자.
`hST : S ⊆ T`는 `∀ x, x ∈ S → x ∈ T`의 증명이므로
먼저 원소 `x`를 넣어 함의의 증명을 얻고 여기에 `hx : x ∈ S`를 넣는다.
이는 앞 절에서 배운 {ref "proofs-successive-application"}[원소와 증명의 연속 적용]이다.
각 중간 결과에는 `have`로 이름을 붙일 수 있다.

```savedLean
theorem subset_trans {A : Type} (S T U : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U) :
    S ⊆ U := by
  intro x hx
  -- S의 원소 x가 T에도 속함을 보인다.
  have hSTx : x ∈ S → x ∈ T := by
    exact hST x

  have hxT : x ∈ T := by
    exact hSTx hx

  -- 이제 T의 원소라는 사실로 U에 속함을 얻는다.
  have hTUx : x ∈ T → x ∈ U := by
    exact hTU x

  exact hTUx hxT
```

첫 `have`의 `:` 뒤에는 증명할 명제 `x ∈ S → x ∈ T`를 적고,
`by` 아래에는 그 증명 `hST x`를 제시했다.
각 줄을 수학적 추론과 대응시키면 다음과 같다.

1. `intro x hx`: 임의의 원소 $`x`에 대하여 $`x \in S`를 가정하며 이제 보일 것은 $`x \in U`이다.
2. `hST x`: $`S \subseteq T`의 증명을 이 원소 $`x`에 적용하여,
   “$`x \in S`이면 $`x \in T`이다”라는 함의의 증명을 얻고 `hSTx`로 이름 붙인다.
3. `hSTx hx`: $`x \in S`라는 가정 `hx`를 앞의 함의에 적용하여,
   $`x \in T`의 증명을 얻고 `hxT`로 이름 붙인다.
4. `hTU x`: 두 번째 포함 관계 $`T \subseteq U`의 증명을 같은 원소에 적용하여,
   “$`x \in T`이면 $`x \in U`이다”라는 함의의 증명을 얻고 `hTUx`로 이름 붙인다.
5. `exact hTUx hxT`: 앞서 얻은 $`x \in T`의 증명을 두 번째 함의에 적용하여,
   목표인 $`x \in U`를 증명한다.

두 인수를 차례로 적용한 `hST x hx`는 앞에서 배운 `f x y`와 같이 `(hST x) hx`로 읽으며,
위에서 `hSTx`를 얻고 여기에 `hx`를 적용한 두 단계를 줄여 쓴 것이다.
마찬가지로 `hTU x hxT`도 `(hTU x) hxT`이다.
또한 `hST x hx`를 `have`의 `:=` 오른쪽에 바로 적으면,
같은 증명을 다음과 같이 짧게 쓸 수 있다.

```savedLean
example {A : Type} (S T U : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U) :
    S ⊆ U := by
  intro x hx
  have hxT : x ∈ T :=
    hST x hx
  exact hTU x hxT
```

# 동치와 두 방향의 함의
%%%
tag := "sets-equivalence"
file := "equivalence"
%%%

포함 관계 $`S \subseteq T`에서는 $`x \in S`로부터 $`x \in T`를 얻는 한쪽 방향만 보였다.
두 집합이 같은 원소를 갖는다는 것을 표현하려면 역방향도 필요하므로
먼저 두 방향의 함의를 함께 나타내는 *동치*를 살펴보자.

두 명제 $`P`와 $`Q`가 *동치*라는 것은
$`P \Rightarrow Q`와 $`Q \Rightarrow P`가 모두 성립한다는 뜻이며, Lean에서는 `P ↔ Q`로 쓴다.
수학에서 “$`P`일 필요충분조건은 $`Q`이다”라고 하는 것도 같은 뜻이다.
즉 `P`를 가정하여 `Q`를 보이고 `Q`를 가정하여 `P`를 보이면 된다.

{anchor "sets-proving-equivalence"}[]`hPQ : P → Q`와 `hQP : Q → P`가 주어졌다고 하자.
각 방향의 증명을 이미 갖고 있으므로 이를 묶으면 `P ↔ Q`를 얻는다.
이때 `constructor`를 쓰면 동치를 두 방향의 함의로 나누어 각각 증명할 수 있다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hQP : Q → P) :
    P ↔ Q := by
  constructor
  · exact hPQ
  · exact hQP
```

`constructor`로 나뉜 목표는 `P → Q`와 `Q → P`이다.
목표가 여러 개로 나뉠 때는 `·` 뒤에 각 목표의 증명을 적으며,
첫 번째 목표는 `hPQ`로, 두 번째 목표는 `hQP`로 증명한다.
VS Code의 Lean 확장에서는 `\.`를 입력하여 이 기호 `·`를 넣을 수 있다.

두 방향의 증명을 묶는 정리 `Iff.intro`를 직접 사용할 수도 있다.
`apply Iff.intro`는 위의 `constructor`와 같이 두 방향의 함의를 목표로 남기며,
앞에서 배운 증명의 적용으로 두 증명을 한꺼번에 제시하면 `Iff.intro hPQ hQP`가 된다.
이 식은 첫 번째 인수로 정방향의 증명을, 두 번째 인수로 역방향의 증명을 받아 `P ↔ Q`의 증명을 만든다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hQP : Q → P) :
    P ↔ Q := by
  exact Iff.intro hPQ hQP
```

{anchor "sets-using-equivalence"}[]반대로 `h : P ↔ Q`가 있으면 `h.mp`로 `P → Q`의 증명을 얻고,
`h.mpr`로 `Q → P`의 증명을 얻는다.
따라서 `P`의 증명도 갖고 있다면 정방향인 `h.mp`를 사용하여 `Q`를 보일 수 있다.

```savedLean
example
    (P Q : Prop)
    (h : P ↔ Q)
    (hP : P) :
    Q := by
  apply h.mp
  exact hP
```

`apply h.mp` 이후에는 목표가 `P`로 바뀌므로 `exact hP`로 증명을 마친다.
역방향에서도 `h.mpr`를 사용하면 같은 방식으로 `Q`에서 `P`를 얻는다.

# 집합의 같음과 함수의 등식
%%%
tag := "sets-equality"
file := "equality"
%%%

두 집합이 같은 원소들을 가지면 두 집합은 같다.
따라서 $`S = T`를 보이려면 임의의 원소 $`x`가 $`S`에 속할 필요충분조건이
$`T`에 속하는 것임을 보이면 된다.
앞 절에서 배운 동치를 사용하면 이 조건을 `∀ x, x ∈ S ↔ x ∈ T`로 쓸 수 있다.
집합을 함수 `A → Prop`로 정의했으므로,
이 조건에서 `S = T`를 얻으려면 함수의 등식과 명제의 등식이 어떻게 증명되는지 알아야 한다.
먼저 함수의 등식을 증명하는 방법부터 살펴보자.

## 함수와 명제의 외연성
%%%
tag := "sets-function-extensionality"
%%%

두 함수 $`f, g : A \to B`가 모든 원소 $`x \in A`에서 같은 값을 가지면 두 함수는 같다.
이를 *함수의 외연성*이라고 하며 다음과 같이 나타낼 수 있다.

$$`\bigl(\text{모든 } x \in A \text{에 대하여 } f(x) = g(x)\bigr) \;\Longrightarrow\; f = g.`

Lean에서 이 원리를 사용하는 전술이 `funext`이다.
목표가 함수의 등식 `f = g`일 때 `funext x`를 쓰면,
임의의 원소 `x : A`를 도입하고 그 원소에서의 등식 `f x = g x`를 새 목표로 삼는다.
전칭명제를 증명할 때처럼 임의의 원소를 택하여, 그 원소에서 두 함수의 값을 비교하는 것이다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x : A, f x = g x) :
    f = g := by
  funext x
  exact h x
```

1. 처음 목표인 `f = g`는 두 함수 자체가 같다는 명제이고, `h`는 모든 원소에서 함수값이 같다는 명제의 증명이다.
2. `funext x`를 쓰면 `x : A`가 도입되고, 목표는 이 원소에서의 등식 `f x = g x`가 된다.
3. `h x`는 전칭명제의 증명 `h`를 원소 `x`에서 사용한 것이므로 바로 그 등식의 증명이다.
   따라서 `exact h x`로 증명을 마친다.

이때 `x`는 임의의 원소이므로 `exact h x`로 보인 등식은 모든 원소에서 성립한다.

{anchor "sets-proposition-extensionality"}[]이제 같은 방법으로 집합의 등식을 증명해 보자.
두 집합은 `A → Prop`의 함수이므로 먼저 `funext x`로 원소 하나에서의 값을 비교할 수 있다.
다음 코드는 이 단계에서 멈춘 미완성 증명이다.

```tryLean +error -keep
example {A : Type _} {S T : Set A}
    (h : ∀ x, x ∈ S ↔ x ∈ T) :
    S = T := by
  funext x
  have hx : S x ↔ T x := h x
```

이때 남은 목표와 가정에서 얻을 수 있는 증명을 나란히 적으면 다음과 같다.

:::table +header (align := left)
*
  * 구분
  * 명제
*
  * `funext x` 이후의 목표
  * `S x = T x`
*
  * 이미 얻은 증명 `hx`의 명제
  * `S x ↔ T x`
:::

`h x`로 얻은 동치에 `hx`라는 이름을 붙였으므로 `S x ↔ T x`의 증명은 이미 가지고 있다.
그러나 목표는 `S x = T x`이므로 `exact hx`로는 증명을 마칠 수 없다.
함수의 외연성으로 원소 하나에서의 비교까지는 왔지만,
그 원소에서 주어진 동치를 명제의 등식으로 바꾸는 단계가 남은 것이다.

`P ↔ Q`와 `P = Q`는 Lean에서 서로 다른 형태의 명제이다.
`P ↔ Q`는 두 방향의 함의이고, `P = Q`는 명제 `P`와 `Q`가 같다는 등식이다.
이 둘을 연결하는 원리가 *명제의 외연성*이며, Lean에서는 `propext`라고 한다.
`propext`에 `P ↔ Q`의 증명을 주면 `P = Q`의 증명을 얻는다.

```savedLean
example
    (P Q : Prop)
    (h : P ↔ Q) :
    P = Q := by
  apply propext
  exact h
```

`apply propext`는 결론 `P = Q`를 얻기 위해 필요한 전제 `P ↔ Q`를 새 목표로 삼는다.
이 새 목표는 가정 `h`로 증명할 수 있으므로 `exact h`로 증명을 마친다.
여기서는 두 명제의 정의를 펼쳐 비교하는 대신, 동치의 증명 `h`를 근거로 등식을 얻었다.

## 집합의 외연성
%%%
tag := "sets-proving-set-equality"
%%%

이제 `∀ x, x ∈ S ↔ x ∈ T`에서 `S = T`를 보이자.
`funext`로 집합의 등식을 원소별 명제의 등식으로 바꾸고,
`propext`로 그 등식을 원소 조건의 동치를 보이는 목표로 바꾸면 주어진 가정을 사용할 수 있다.

*정리* 모든 원소 $`x`에 대하여 $`x \in S \iff x \in T`이면 $`S = T`이다.

```savedLean
@[ext] theorem set_ext {A : Type _} {S T : Set A}
    (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := by
  funext x
  apply propext
  exact h x
```

1. 처음 목표인 `S = T`는 함수 `S`와 `T`의 등식이다.
2. `funext x`로 임의의 원소 `x : A`를 도입하면 목표는 함수값의 등식 `S x = T x`가 된다.
   원소 기호로 쓰면 두 명제 `x ∈ S`와 `x ∈ T`가 같다는 목표이다.
3. `apply propext`를 쓰면 목표가 `S x ↔ T x`, 곧 `x ∈ S ↔ x ∈ T`로 바뀐다.
4. `h x`는 전칭명제의 증명 `h`를 원소 `x`에서 사용한 것으로, 이 동치의 증명이다.
   따라서 `exact h x`로 모든 단계가 끝난다.

앞의 증명에서는 `funext`와 `propext`를 차례로 적용하여
집합의 등식을 원소 조건의 동치를 보이는 문제로 바꾸었다.
이제 이 과정을 담은 정리 `set_ext`를 사용할 수 있으므로 매번 두 원리를 따로 적용할 필요는 없다.
정리 앞의 `@[ext]`는 `ext`가 이 정리를 찾을 수 있도록 등록하는 표시이다.

`ext`는 목표에 맞는 외연성 정리를 적용하여 그 정리에 필요한 비교를 새 목표로 삼는다.
가령 목표가 `S = T`일 때 `ext x`를 쓰면 `set_ext`를 적용하고
임의의 원소 `x : A`를 도입하여 `x ∈ S ↔ x ∈ T`를 새 목표로 삼는다.
도입한 `x`는 임의의 원소이므로 이 원소에서 두 조건이 동치임을 보이면 집합의 등식이 성립한다.
남은 목표에는 앞에서 배운 함의와 동치의 증명 방법을 사용한다.

`ext`는 함수의 등식에서도 함수값을 비교하는 목표를 만든다.
앞의 함수 예제와 같이 `f g : A → B`가 주어졌을 때는 다음과 같이 쓴다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x : A, f x = g x) :
    f = g := by
  ext x
  exact h x
```

앞의 `funext`와 `propext`는 함수와 명제의 등식을 증명하는 원리를 설명하기 위해 따로 살펴보았다.
앞으로 함수나 집합의 원소별 비교를 시작할 때는 `ext`를 사용하겠다.
다음 절에서는 순서쌍과 부분타입을 다루면서 이 전술의 다른 용법도 살펴본다.

{anchor "sets-equality-from-subsets"}[]*정리* $`S \subseteq T`이고 $`T \subseteq S`이면 $`S = T`이다.

*증명* 임의의 원소 $`x`에 대하여 첫 번째 포함 관계로 $`x \in S \Rightarrow x \in T`를 얻고,
두 번째 포함 관계로 그 역방향을 얻는다.
따라서 두 집합의 원소 조건이 동치이므로 두 집합은 같다.

```savedLean
theorem set_eq_of_subset {A : Type} (S T : Set A)
    (hST : S ⊆ T)
    (hTS : T ⊆ S) :
    S = T := by
  ext x
  constructor
  · exact hST x
  · exact hTS x
```

`ext x`를 쓰면 임의의 원소 `x`에 대한 목표 `x ∈ S ↔ x ∈ T`가 남는다.
`constructor`로 이 동치를 두 방향의 함의로 나누면,
정방향은 `hST x`로, 역방향은 `hTS x`로 증명할 수 있다.

## 등식과 원소별 비교
%%%
tag := "sets-equality-comparisons"
%%%

앞에서는 원소마다 비교하여 함수나 집합의 등식을 증명했다.
이번에는 이미 두 대상이 같다는 등식을 알고 있을 때 그 등식을 사용하는 방법을 살펴보자.
두 함수가 같으면 어느 원소에서나 함수값이 같으며,
두 집합이 같으면 각 원소가 속한다는 조건도 서로 동치이다.
이처럼 같은 대상은 그 값이나 조건으로 구별할 수 없다는 원리를 *동일자의 구별 불가능성*이라고 한다.

함수의 등식 `h : f = g`에서 `f x = g x`를 얻으려면 등식에 따라 `f`를 `g`로 바꾸면 된다.
이와 같이 주어진 등식으로 식을 바꾸는 전술이 `rw`이며, 사용할 등식은 대괄호 안에 적는다.

```savedLean
example
    (A B : Type) (f g : A → B) (x : A)
    (h : f = g) :
    f x = g x := by
  rw [h]
```

`rw [h]`는 목표의 `f`를 `g`로 바꾸고, 남은 등식 `g x = g x`는 양변이 같으므로 증명을 마친다.
집합의 등식도 같은 방법으로 사용한다.
아래에서는 `hxS : x ∈ S`에 등식 `hST : S = T`를 사용하여 `hxS : x ∈ T`를 얻는다.

```savedLean
example {A : Type} (S T : Set A)
    (x : A)
    (hST : S = T)
    (hxS : x ∈ S) :
    x ∈ T := by
  rw [hST] at hxS
  exact hxS
```

`at hxS`는 등식을 사용할 가정을 지정한다.
이처럼 목표나 가정에 있는 대상을 주어진 등식으로 바꿀 때는 `rw`를 사용하면 된다.

등식에서 원소별 비교 조건을 꺼내 두고 사용할 수도 있다.
가령 집합의 등식 `hST : S = T`로부터 모든 원소에 대한 동치
`∀ x, x ∈ S ↔ x ∈ T`를 얻으려면 `indisc at hST`를 쓴다.
전술 `indisc`은 앞에서 살펴본 동일자의 구별 불가능성을 사용하며,
`with` 뒤에 이름을 적으면 원래 등식을 유지하고 그 이름으로 비교 조건의 증명을 얻는다.

```savedLean
example {A : Type} (S T : Set A)
    (hST : S = T) :
    ∀ x, x ∈ S ↔ x ∈ T := by
  indisc at hST with hmem
  -- hmem : ∀ x, x ∈ S ↔ x ∈ T
  exact hmem
```

이제 어느 원소 `a`에 대해서나 `hmem a`로 원소 조건의 동치를 사용할 수 있다.
처음부터 원소 하나를 지정하여 `indisc a at hST with ha`라고 쓰면
그 원소에서의 증명 `ha : a ∈ S ↔ a ∈ T`를 얻는다.
`with`를 생략하면 새 증명이 원래 가정을 대신하므로 가정의 이름은 유지되지만 그 타입은 바뀐다.

`indisc`으로 얻는 조건도 등식에 따라 한쪽 대상을 다른 쪽으로 바꾸어 증명할 수 있다.
`rw`가 필요한 곳의 식을 바꾸는 데 쓰인다면,
`indisc`은 함수값이나 원소 조건처럼 그 등식에서 사용할 비교를 꺼내는 데 쓰인다.
순서쌍에서 두 성분의 등식을 얻는 예는 {ref "functions-pair-comparison"}[순서쌍의 비교]에서 다룬다.

`ext`와 `indisc`은 기본적으로 비교 규칙을 한 번 적용한다.
예를 들어 집합에서는 등식과 원소 조건의 동치를 연결하는 `set_ext`가 하나의 비교 규칙이다.
대상이 여러 겹으로 구성되어 있으면 `ext : 2`, `indisc : 2 at h`로 깊이를 지정하거나
`ext!`, `indisc! at h`로 적용할 수 있는 비교를 반복할 수 있다.
목표에서의 `indisc`와 가정에서의 `ext at`을 비롯한 다른 용법은
{ref "tactic-equality-comparison-rules"}[부록의 전체 등식과 비교 조건]에서 다룬다.

# 교집합과 논리곱
%%%
tag := "sets-intersections-and-conjunctions"
file := "intersections-and-conjunctions"
%%%

*정의* $`S`와 $`T`에 모두 속하는 원소로 이루어진 집합을 *교집합*이라고 한다.

교집합을 Lean으로 정의하려면 `x ∈ S`와 `x ∈ T`가 모두 성립한다는 조건을 나타내야 한다.
이를 위해 두 명제 $`P`와 $`Q`가 모두 성립한다는 명제인 *논리곱* `P ∧ Q`를 사용하며
교집합의 원소 조건은 `x ∈ S ∧ x ∈ T`로 쓴다.

```savedLean
def inter {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∧ x ∈ T
instance {A : Type} : Inter (Set A) where
  inter := Course.inter
```

`inter S T`가 두 집합의 교집합이며,
뒤의 `instance`는 이를 `S ∩ T`로 쓰도록 기호와 정의를 연결한다.
따라서 `x ∈ S ∩ T`는 `x ∈ S ∧ x ∈ T`를 뜻한다.
논리곱 `P ∧ Q`의 증명에는 `P`의 증명과 `Q`의 증명이 함께 들어 있다.
`h : P ∧ Q`에서 이들을 각각 `h.left`, `h.right`로 꺼낼 수 있으므로,
교집합의 원소라는 증명에서도 두 집합에 속한다는 사실을 따로 사용할 수 있다.
첫 번째 사실을 사용하여 교집합이 $`S`의 부분집합임을 보이자.

```savedLean
theorem inter_subset_left {A : Type} (S T : Set A) :
    S ∩ T ⊆ S := by
  intro x hx
  exact hx.left
```

가정 `hx`는 `x ∈ S ∧ x ∈ T`의 증명이므로
`hx.left`로 `x ∈ S`를 얻고 `hx.right`로 `x ∈ T`를 얻는다.
반대로 논리곱을 증명할 때는 두 사실을 각각 보여야 한다.

*정리* $`x \in S \cap T`이면 $`x \in T \cap S`이다.

*증명* $`x \in S \cap T`라고 하면 $`x \in S`와 $`x \in T`를 모두 얻는다.
이 두 사실의 순서를 바꾸어 묶으면 $`x \in T \cap S`이다.

Lean에서도 `x ∈ T ∩ S`를 보이려면 `x ∈ T`와 `x ∈ S`를 모두 보여야 하므로
`constructor`를 써서 목표를 두 명제로 나눈다.

```savedLean
theorem inter_comm_forward {A : Type} (S T : Set A)
    (x : A) :
    x ∈ S ∩ T → x ∈ T ∩ S := by
  intro hx
  constructor
  · exact hx.right
  · exact hx.left
```

`intro hx`를 쓰면 `x ∈ S ∩ T`가 가정 `hx`로 들어오고, 목표는 `x ∈ T ∩ S`가 된다.
이어서 `constructor`로 나눈 첫 목표 `x ∈ T`는 `hx.right`로 증명하고,
둘째 목표 `x ∈ S`는 `hx.left`로 증명한다.
각 목표의 증명은 앞에서와 같이 `·` 뒤에 나누어 적는다.



같은 증명을 가정에 담긴 두 사실을 꺼내는 방식으로 적을 수도 있다.
`unpack hx with ⟨hxS, hxT⟩`는 논리곱의 증명 하나에서 두 성분의 증명을 꺼낸다.
이때 `hxS : x ∈ S`와 `hxT : x ∈ T`를 얻으므로
두 증명을 새 목표에 맞는 순서로 사용하면 된다.

```savedLean
theorem inter_comm_forward_by_parts {A : Type} (S T : Set A)
    (x : A) :
    x ∈ S ∩ T → x ∈ T ∩ S := by
  intro hx
  unpack hx with ⟨hxS, hxT⟩
  constructor
  · exact hxT
  · exact hxS
```

`unpack`은 논리곱의 증명에서 두 성분을 꺼내며,
꺾쇠괄호 안에는 그 성분에 붙일 이름을 적는다.
`⟨`, `⟩`는 `\<`, `\>`로 입력한다.
주어진 증명들을 한 증명으로 묶는 `constructor at`의 용법은
{ref "tactic-conjunctions"}[부록의 논리곱]에서 설명한다.

{anchor "sets-intersection-equivalence"}[]앞의 정리에서는 $`x \in S \cap T`에서 $`x \in T \cap S`를 얻는 한 방향을 증명했다.
이 정리에서 $`S`와 $`T`의 순서를 바꾸면 역방향도 얻으므로,
두 방향을 묶어 원소 조건의 동치를 증명할 수 있다.

*정리* $`x \in S \cap T`일 필요충분조건은 $`x \in T \cap S`이다.

동치를 증명하는 방법은 앞에서 배운 것과 같으므로,
`constructor`로 두 방향의 함의를 나누어 보이자.

```savedLean
theorem inter_comm {A : Type} (S T : Set A) (x : A) :
    x ∈ S ∩ T ↔ x ∈ T ∩ S := by
  constructor
  · exact inter_comm_forward S T x
  · exact inter_comm_forward T S x
```

첫 번째 목표에서는 `inter_comm_forward S T x`로 정방향의 함의를 얻고,
두 번째 목표에서는 `inter_comm_forward T S x`로 역방향의 함의를 얻는다.

*정리* $`S\subseteq T`이면 $`S\cap T=S`이다.

*증명* `inter_subset_left`에 따라 $`S\cap T\subseteq S`이다.
거꾸로 $`x\in S`이면 가정에 따라 $`x\in T`이기도 하므로 $`x\in S\cap T`이다.
두 포함 관계를 `set_eq_of_subset`에 사용하면 등식을 얻는다.

```savedLean
theorem inter_eq_left_of_subset {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∩ T = S := by
  apply set_eq_of_subset
  · exact inter_subset_left S T
  · intro x hx
    constructor
    · exact hx
    · exact hST x hx
```

이 정리를 사용하면 포함 관계를 아는 두 집합의 교집합을 바로 구할 수 있다.
다음에서는 원소를 나열한 집합에 이를 적용한다.

# 합집합과 논리합
%%%
tag := "sets-unions-and-disjunctions"
file := "unions-and-disjunctions"
%%%

*정의* $`S` 또는 $`T`에 속하는 원소로 이루어진 집합을 *합집합*이라고 한다.

합집합을 Lean으로 정의하려면 `x ∈ S`와 `x ∈ T` 중 적어도 하나가 성립한다는 조건을 나타내야 한다.
이를 위해 두 명제 $`P`와 $`Q` 중 적어도 하나가 성립한다는 명제인 *논리합* `P ∨ Q`를 사용하며
합집합의 원소 조건은 `x ∈ S ∨ x ∈ T`로 쓴다.

```savedLean
def union {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∨ x ∈ T
instance {A : Type} : Union (Set A) where
  union := Course.union
```

`union S T`가 두 집합의 합집합이며, 뒤의 `instance`로 이를 `S ∪ T`에 연결한다.
따라서 `x ∈ S ∪ T`를 보이려면 `x ∈ S`와 `x ∈ T` 중 하나를 보이면 된다.

*정리* $`S`는 $`S`와 $`T`의 합집합의 부분집합이다.

```savedLean
theorem subset_union_left {A : Type} (S T : Set A) :
    S ⊆ S ∪ T := by
  intro x hx
  left
  exact hx
```

목표는 `x ∈ S ∨ x ∈ T`이고, 가정 `hx`는 `x ∈ S`이다.
따라서 `left`로 왼쪽 명제를 선택하면 이 가정으로 증명할 수 있으며,
오른쪽 명제를 선택할 때는 `right`를 쓴다.

*정리* $`S`와 $`T`가 모두 $`U`의 부분집합이면 그 합집합도 $`U`의 부분집합이다.

합집합에 속한다는 가정에서는 두 원소 조건 중 적어도 하나가 성립함을 알 수 있다.
논리곱처럼 양쪽의 증명을 모두 꺼낼 수는 없으므로 어느 쪽이 주어지든 결론이 성립함을 보인다.
$`x\in S`인 경우에는 $`S\subseteq U`를, $`x\in T`인 경우에는 $`T\subseteq U`를 사용하면 된다.

```savedLean
theorem union_subset {A : Type} (S T U : Set A)
    (hSU : S ⊆ U)
    (hTU : T ⊆ U) :
    S ∪ T ⊆ U := by
  intro x hx
  cases hx with
  | inl hxS => exact hSU x hxS
  | inr hxT => exact hTU x hxT
```

이번에는 가정 `hx`가 `x ∈ S ∨ x ∈ T`이므로
`cases hx`로 $`x \in S`인 경우와 $`x \in T`인 경우를 나누어 생각한다.
`inl`은 첫 번째 경우, `inr`은 두 번째 경우이다.
첫 번째 경우에는 `hSU`, 두 번째 경우에는 `hTU`를 적용하여 $`x \in U`를 얻는다.

*보기* $`S=\{2,3\}`과 양의 자연수의 집합 $`T`에 대하여 $`S\cap T=S`임을 보이자.
$`S`의 원소는 $`2` 또는 $`3`이므로 논리합으로 원소 조건을 나타낼 수 있다.

```savedLean
def twoThree : Set Nat := fun n => n = 2 ∨ n = 3
```

두 수가 모두 양수이므로 $`S\subseteq T`이다.
이 포함 관계를 먼저 증명한 뒤 앞의 교집합 정리에 사용하자.

```savedLean
theorem twoThree_subset_positives :
    twoThree ⊆ positives := by
  intro n hn
  cases hn with
  | inl hTwo =>
      rw [hTwo]
      expand
      expand
      decide

  | inr hThree =>
      rw [hThree]
      expand
      expand
      decide

example : twoThree ∩ positives = twoThree := by
  exact inter_eq_left_of_subset twoThree positives
    twoThree_subset_positives
```

첫 증명은 `n = 2`와 `n = 3`으로 경우를 나눈다.
각 경우에 원소를 해당 수로 바꾸고 `positives`와 `positive`를 펼치면
각각 `0 < 2`와 `0 < 3`이 남는다.
이로써 포함 관계를 얻었으므로 둘째 증명에서는 `inter_eq_left_of_subset`에
두 집합과 포함 관계의 증명을 넣어 교집합을 구한다.

## 교집합의 분배법칙
%%%
tag := "sets-intersection-distributes-over-union"
%%%

교집합과 합집합이 함께 있으면 원소 조건에도 논리곱과 논리합이 함께 나타난다.
앞에서 배운 두 증명 방법을 다음 등식에 사용해 보자.

*보기* $`S\cap(T\cup U)=(S\cap T)\cup(S\cap U)`이다.

*풀이* 왼쪽 집합의 원소 $`x`는 $`S`에 속하며 $`T` 또는 $`U`에 속한다.
$`T`에 속하는 경우에는 $`S\cap T`에 속하고 $`U`에 속하는 경우에는 $`S\cap U`에 속하므로
어느 경우에도 오른쪽 합집합에 속한다.
거꾸로 오른쪽 집합의 원소는 $`S\cap T` 또는 $`S\cap U`에 속한다.
두 경우 모두 $`S`에 속하고 $`T\cup U`에도 속하므로 왼쪽 집합의 원소이다.

```savedLean
example
    {A : Type} (S T U : Set A) :
    S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U) := by
  -- 각 원소에서 두 집합의 원소 조건이 동치임을 보인다.
  ext x
  constructor
  · intro hx
    -- x가 T와 U 중 어디에 속하는지 나눈다.
    cases hx.right with
    | inl hxT =>
        -- x는 S ∩ T의 원소이다.
        left
        constructor
        · exact hx.left
        · exact hxT

    | inr hxU =>
        -- x는 S ∩ U의 원소이다.
        right
        constructor
        · exact hx.left
        · exact hxU

  · intro hx
    -- 두 교집합 중 어디에 속해도 S에 속한다.
    cases hx with
    | inl hxST =>
        constructor
        · exact hxST.left
        -- T에 속하므로 T ∪ U에도 속한다.
        · left
          exact hxST.right

    | inr hxSU =>
        constructor
        · exact hxSU.left
        -- U에 속하므로 T ∪ U에도 속한다.
        · right
          exact hxSU.right
```

정방향에서는 `hx.left`가 `x ∈ S`의 증명이고 `hx.right`가 `x ∈ T ∨ x ∈ U`의 증명이다.
따라서 `hx.right`로 경우를 나누면서 `hx.left`는 두 경우에 모두 사용한다.
역방향에서는 가정 자체가 논리합이므로 `cases hx`로 나눈 뒤
각 경우에 `constructor`로 `x ∈ S`와 `x ∈ T ∪ U`를 보인다.

# 여집합과 부정
%%%
tag := "sets-complements-and-negation"
file := "complements-and-negation"
%%%

*정의* $`A`의 원소 중 집합 $`S`에 속하지 않는 원소로 이루어진 집합을
$`S`의 *여집합*이라고 하며 $`S^{\mathsf{c}}`로 나타낸다.

여집합을 구할 때는 어떤 전체집합을 기준으로 삼는지 정해져 있어야 한다.
가령 $`S = \{1, 2\}`의 여집합은 자연수 전체를 기준으로 하면 $`\{0, 3, 4, \ldots\}`이고,
정수 전체를 기준으로 하면 여기에 음의 정수들도 포함된다.
Lean에서는 `S : Set A`의 `A`가 원소의 범위를 정하므로
여집합도 같은 타입 `A`의 원소들로 이루어진다.

이 절에서는 여집합의 원소 조건을 통해 부정의 증명과 사용을 익히고,
이를 바탕으로 여집합을 두 번 취하면 원래 집합을 얻는다는 성질을 증명한다.

{anchor "sets-negation"}[]여집합을 Lean으로 정의하려면 “$`x`가 $`S`에 속하지 않는다”라는 조건을 명제로 표현해야 한다.
명제 $`P`가 성립하지 않는다는 명제를 $`P`의 *부정*이라고 하며 Lean에서는 `¬ P`로 쓴다.
따라서 여집합의 원소 조건은 `¬ (x ∈ S)`이고,
이를 원소 관계의 기호와 함께 줄여 쓰면 `x ∉ S`이다.

수학에서 $`P`가 성립하지 않음을 보일 때는 $`P`가 성립한다고 가정한 뒤 모순을 이끌어 낸다.
앞에서 모순을 `False`로 나타냈듯이,
“`P`를 가정하면 모순이 나온다”는 주장은 함의 `P → False`로 나타낼 수 있으므로,
Lean에서는 이를 부정 `¬ P`의 정의로 사용한다.

목표가 `¬ P`이면 `P → False`를 증명하면 되므로,
`intro hP`로 `P`를 가정하고 목표를 `False`로 바꾼다.
주어진 가정들과 `hP`에서 모순을 이끌어 내면 `P`를 부정하는 증명이 완성된다.

한편 `P`의 증명 `hP`와 그 부정의 증명 `hnotP`가 모두 주어지면 모순을 보일 수 있다.
`hnotP`의 타입은 `P → False`이므로
목표가 `False`일 때 `apply hnotP`를 쓰면 `P`가 새 목표가 된다.

```savedLean
example
    (P : Prop)
    (hP : P)
    (hnotP : ¬ P) :
    False := by
  apply hnotP
  exact hP
```

새 목표는 이미 주어진 증명 `hP`로 해결하므로 `exact hP`로 증명을 마친다.
앞에서 배운 증명의 적용으로 두 단계를 줄여 쓰면,
`hnotP hP`가 `False`의 증명이므로 `exact hnotP hP` 한 줄로도 같은 모순을 얻는다.

이제 이 부정을 사용하여 여집합의 원소 조건을 `x ∉ S`로 정하자.

```savedLean
def compl {A : Type} (S : Set A) : Set A :=
  fun x => x ∉ S
instance {A : Type} : Complement (Set A) where
  complement := Course.compl

postfix:max "ᶜ" => Complement.complement
```

이 정의와 기호 연결에 따라 `compl S`를 `Sᶜ`로 쓰며,
`x ∈ Sᶜ`는 `x ∉ S`, 곧 `x ∈ S → False`를 뜻한다.
증명 상태에서는 여집합의 원소 관계를 `x ∈ Sᶜ`로 표시하며,
`expand`로 그 정의를 펼치면 `x ∉ S`가 된다.

*보기* 한 원소가 $`S`와 그 여집합에 모두 속한다고 가정하면 모순이다.

```savedLean
example
    {A : Type} (S : Set A) (x : A)
    (hx : x ∈ S)
    (hxc : x ∈ Sᶜ) :
    False := by
  apply hxc
  exact hx
```

여기서는 앞의 예제에서 `P`를 `x ∈ S`로 바꾼 것이다.
`hxc`는 `x ∉ S`, 곧 `x ∈ S → False`의 증명이므로
`apply hxc`로 필요한 전제를 목표로 삼고 `exact hx`로 그 증명을 제시한다.

## 부정의 증명
%%%
tag := "sets-proving-negation"
file := "proving-negation"
%%%

여집합을 취하면 포함 관계의 방향이 바뀐다는 것을 증명하자.
원소가 집합에 속하지 않음을 보여야 하므로 그 집합에 속한다고 가정하여 모순을 얻는 방법을 사용한다.

*정리* $`S \subseteq T`이면 $`T^{\mathsf{c}} \subseteq S^{\mathsf{c}}`이다.

*증명* 임의의 원소 $`x \in T^{\mathsf{c}}`를 택하면 $`x \notin T`이다.
만약 $`x \in S`라고 가정하면 $`S \subseteq T`에 따라 $`x \in T`를 얻으므로 앞의 가정과 모순이다.
따라서 $`x \notin S`, 곧 $`x \in S^{\mathsf{c}}`이며, 원하는 포함 관계가 성립한다.

```savedLean
theorem compl_subset_compl {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    Tᶜ ⊆ Sᶜ := by
  intro x hxTc
  intro hxS
  have hxT : x ∈ T := by
    exact hST x hxS

  exact hxTc hxT
```

Lean에서도 같은 순서로 가정을 도입하고 모순을 얻으며, 각 줄의 역할은 다음과 같다.

1. `intro x hxTc`: 임의의 원소 `x`에 대하여 `x ∈ Tᶜ`를 가정하고, `x ∈ Sᶜ`를 새 목표로 삼는다.
2. `intro hxS`: 목표는 `x ∈ S → False`이므로 `x ∈ S`를 가정하며 이제 보일 것은 `False`이다.
3. `have hxT : x ∈ T := by`: 포함 관계의 증명 `hST`를 사용하여 `x ∈ T`를 보이고, 그 증명에 `hxT`라는 이름을 붙인다.
4. `exact hxTc hxT`: `hxTc`는 `x ∈ T → False`의 증명이므로 여기에 `hxT`를 적용하여 `False`를 얻는다.

이 증명에서 `hxS`는 $`x \notin S`를 보이기 위해 임시로 도입한 가정이다.
그 가정에서 모순을 얻었으므로 `x ∈ S → False`, 곧 `x ∉ S`의 증명이 완성된다.

## 이중 여집합
%%%
tag := "sets-subset-double-complement"
file := "subset-double-complement"
%%%

여집합을 두 번 취한 집합 $`(S^{\mathsf{c}})^{\mathsf{c}}`가 원래 집합 $`S`와 같음을 보이려면,
두 집합이 서로의 부분집합임을 증명하면 된다.
먼저 $`S \subseteq (S^{\mathsf{c}})^{\mathsf{c}}`를 보이자.

*증명* 임의의 원소 $`x \in S`를 택하자.
만약 $`x \in S^{\mathsf{c}}`라고 가정하면 $`x \notin S`이므로 처음의 가정과 모순이다.
그러므로 $`x \notin S^{\mathsf{c}}`, 곧 $`x \in (S^{\mathsf{c}})^{\mathsf{c}}`이며, 원하는 포함 관계를 얻는다.

```savedLean
theorem subset_compl_compl {A : Type} (S : Set A) :
    S ⊆ Sᶜᶜ := by
  intro x hxS
  intro hxSc
  exact hxSc hxS
```

`intro x hxS`로 $`x \in S`를 가정하면 남은 목표는 `x ∈ Sᶜᶜ`, 곧 `x ∈ Sᶜ → False`이다.
이를 보이기 위해 `intro hxSc`로 $`x \in S^{\mathsf{c}}`를 가정하면
`hxSc`는 `x ∈ S → False`의 증명이므로 `hxSc hxS`에서 모순을 얻는다.
명제의 관점에서 보면 $`P \Rightarrow \neg\neg P`를 증명한 것이며,
여기까지는 앞에서 배운 부정의 정의만으로 충분하다.

## 배중률과 귀류법
%%%
tag := "sets-classical-logic"
file := "classical-logic"
%%%

반대 방향인 $`(S^{\mathsf{c}})^{\mathsf{c}} \subseteq S`에서는,
`x ∈ Sᶜᶜ`를 가정하고 `x ∈ S`를 보여야 한다.
가정을 펼치면 `¬¬ (x ∈ S)`이므로 이번에는 이중 부정에서 원래 명제를 얻는 추론이 필요하다.
부정의 정의까지 풀어 보면 가정과 목표는 다음과 같다.

```
hxScc : (x ∈ S → False) → False
⊢ x ∈ S
```

앞의 증명에서는 목표가 함의여서 `intro`로 그 전제를 가정할 수 있었다.
이번 목표는 `x ∈ S`이므로 같은 방법으로 시작할 수 없다.
또한 `hxScc`는 `x ∉ S`의 증명을 받아 `False`를 주는 함수이므로,
이를 사용하려면 먼저 그 부정의 증명이 있어야 한다.
이 지점에서 원래 명제 `x ∈ S`를 얻기 위해 고전논리의 배중률을 사용하자.

*배중률*은 모든 명제 $`P`에 대하여 $`P \lor \neg P`가 성립한다는 원리로,
$`P`가 성립하거나 그 부정이 성립한다는 뜻이다.
`¬¬ P`를 알고 있을 때 배중률에 따라 두 경우로 나누면,
`P`인 경우에는 원하는 결론을 이미 얻었으며, `¬ P`인 경우에는 주어진 이중 부정과 모순이 생긴다.
따라서 고전논리에서는 `¬¬ P`로부터 `P`를 얻을 수 있다.

이 경우 구분을 Lean으로 적을 때는 `by_cases h : P`를 사용한다.
첫 번째 경우에는 `h : P`를, 두 번째 경우에는 `h : ¬ P`를 가정으로 갖고
각 경우에 원래 목표를 증명한다.
이중 여집합의 포함 관계에서도 원소 `x`가 `S`에 속하는지에 따라 두 경우를 나누자.

```savedLean
theorem compl_compl_subset {A : Type} (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  by_cases hxS : x ∈ S
  · exact hxS
  · have hFalse : False := by
      exact hxScc hxS

    contradiction
```

첫 번째 경우에는 목표 `x ∈ S`의 증명 `hxS`가 주어져 있으므로 이를 그대로 사용한다.
두 번째 경우의 `hxS`는 `x ∉ S`의 증명이며
이를 `hxScc : ¬¬ (x ∈ S)`에 적용하면 모순을 얻는다.
`have hFalse : False := by`로 이 모순의 증명을 가정에 추가하면
`contradiction`으로 남은 목표 `x ∈ S`를 증명할 수 있다.
`by_cases`에서는 두 경우 모두 목표가 `x ∈ S`로 유지된다는 점을 확인하라.

이처럼 `¬¬ P`에서 `P`를 얻는 추론을 *이중 부정 제거*(DNE, double negation elimination)라고 한다.
Lean의 정리 `Classical.not_not`는 `¬¬ P ↔ P`의 증명이므로
그 정방향인 `Classical.not_not.mp`를 사용하면 이중 부정을 제거할 수 있다.
같은 포함 관계를 이중 부정 제거 정리로 증명하면 다음과 같다.

```savedLean
example
    {A : Type} (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  apply Classical.not_not.mp
  exact hxScc
```

`apply Classical.not_not.mp`는 목표 `x ∈ S`를 `¬¬ (x ∈ S)`로 바꾼다.
이 명제는 `x ∈ Sᶜᶜ`의 정의와 같으므로 가정 `hxScc`로 증명을 마친다.
정리의 증명에 가정을 직접 적용하면 `exact Classical.not_not.mp hxScc` 한 줄로도 쓸 수 있다.

고전논리의 *귀류법*에서는 `P`를 보이기 위해 `¬ P`를 가정하고 모순을 이끌어 낸다.
이 논증으로 `¬¬ P`를 증명한 뒤 이중 부정 제거를 사용하면 원래 목표인 `P`를 얻는다.
Lean에서는 `by_contra`로 귀류법을 시작할 수 있다.
아래 증명에서 `by_contra hxNotS`를 쓰면 목표인 `x ∈ S`의 부정을 `hxNotS`로 가정하고
`False`를 새 목표로 삼아 이 귀류법을 시작한다.

```savedLean
example
    {A : Type} (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  by_contra hxNotS
  exact hxScc hxNotS
```

`intro x hxScc` 이후에는 `hxScc : ¬¬ (x ∈ S)`를 가정으로 갖고 `x ∈ S`를 증명해야 한다.
`by_contra hxNotS`로 `hxNotS : ¬ (x ∈ S)`를 도입하면 목표가 `False`로 바뀌므로,
`exact hxScc hxNotS`로 이중 부정의 증명에 그 부정의 증명을 적용하여 모순을 얻는다.

부정을 증명하는 앞의 방법과 귀류법에서 무엇을 가정했는지 비교하라.
`¬ P`를 보일 때 `P`를 가정하는 것은 부정의 정의에 따른 것이며,
`P`를 보일 때 `¬ P`를 가정하는 귀류법에는 이중 부정 제거가 필요하다.

이제 두 집합이 서로의 부분집합임을 보였으므로,
앞의 정리 `set_eq_of_subset`를 사용하여 이중 여집합의 등식을 얻자.

*정리* 모든 집합 $`S`에 대하여 $`(S^{\mathsf{c}})^{\mathsf{c}} = S`이다.

```savedLean
theorem compl_compl_eq {A : Type} (S : Set A) :
    Sᶜᶜ = S := by
  apply set_eq_of_subset
  · exact compl_compl_subset S
  · exact subset_compl_compl S
```

`apply set_eq_of_subset`를 쓰면 목표가 `Sᶜᶜ ⊆ S`와 `S ⊆ Sᶜᶜ`로 나뉜다.
첫 번째 목표에는 고전논리로 증명한 `compl_compl_subset S`를,
두 번째 목표에는 부정의 정의로 증명한 `subset_compl_compl S`를 사용하여 등식의 증명을 마친다.

이후의 본문에서는 고전논리를 기본으로 사용하겠다.
파일에서 다음 선언을 적으면 그 뒤의 증명과 정의에서 고전논리를 사용할 수 있다.

```savedLean
open scoped Classical
```

`classical`은 한 증명 안에서 고전논리를 사용할 범위를 정하며
`open scoped Classical`은 선언한 범위 전체에 같은 설정을 적용한다.
이 선언은 다른 파일을 가져오는 `import`로 전달되지 않으므로
이후의 예제 코드와 연습문제 파일에도 같은 선언을 둔다.

자동 표현 정리를 켠 풀이 파일에서는 이 설정에 따라 `¬¬ P`를 `P`로 정리한다.
따라서 이중 여집합의 원소 조건을 펼친 뒤에는 다음과 같이 포함 관계를 증명할 수 있다.
자동 표현 정리의 설정과 범위는 {ref "tactic-auto-normalization"}[자동 표현 정리]에서 설명한다.

```savedLean -show
section
open scoped Course.Auto
open scoped Classical
```

```savedLean
example
    {A : Type} (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  expand at hxScc
  expand at hxScc
  exact hxScc
```

두 번의 `expand at hxScc`로 여집합의 원소 조건을 차례로 펼치면 이중 부정이 자동으로 제거된다.
그러면 가정이 목표 `x ∈ S`와 같은 명제로 정리되므로 `exact hxScc`로 증명을 마친다.

```savedLean -show
end
```

## 차집합
%%%
tag := "sets-differences"
file := "differences"
%%%

*정의* $`S`에 속하면서 $`T`에는 속하지 않는 원소로 이루어진 집합을
$`S`와 $`T`의 *차집합*이라고 하며 $`S \setminus T`로 나타낸다.

차집합의 원소는 두 조건을 모두 만족해야 하므로
논리곱과 부정을 함께 사용하여 `x ∈ S ∧ x ∉ T`로 표현한다.

```savedLean
def diff {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∧ x ∉ T
instance {A : Type} : SDiff (Set A) where
  sdiff := Course.diff
```

이 기호 연결로 `diff S T`를 `S \ T`로 쓴다.
따라서 `x ∈ S \ T`의 증명에서는 첫 번째 조건으로 `x ∈ S`를 얻고,
두 번째 조건으로 `x ∉ T`를 얻는다.

*보기* 두 집합 $`S`, $`T`에 대하여 $`S \setminus T = S \cap T^{\mathsf{c}}`임을 보이자.

*증명* 임의의 원소 $`x`에 대하여 차집합과 교집합, 여집합의 정의를 사용하면 다음을 얻는다.

$$`x \in S \setminus T
\iff (x \in S \land x \notin T)
\iff x \in S \cap T^{\mathsf{c}}.`

두 집합의 원소 조건이 서로 동치이므로 앞에서 배운 `ext`로 원소 조건을 비교하자.

```savedLean
theorem diff_eq_inter_compl {A : Type} (S T : Set A) :
    S \ T = S ∩ Tᶜ := by
  ext x
  expand
  expand
```

`ext x`를 쓰면 임의의 원소에 대하여
`x ∈ S \ T ↔ x ∈ S ∩ Tᶜ`를 보이는 것이 목표가 된다.
`expand`로 차집합과 교집합, 여집합의 정의를 차례로 펼치면 양쪽이 모두 `x ∈ S ∧ x ∉ T`이므로
동치의 반사성으로 증명이 자동으로 끝난다.

# 연습문제
%%%
tag := "sets-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.
앞에서 증명한 정리는 이름으로 사용할 수 있다.

*문제 1* 교집합이 두 번째 집합의 부분집합임을 증명하라.

```savedLean -keep
theorem exercise_inter_subset_right
    {A : Type} (S T : Set A) :
    S ∩ T ⊆ T := by
  sorry
```

*문제 2* 포함 관계의 추이성을 다시 증명하고,
{ref "intro-comments"}[주석 작성법]을 사용하여 각 증명 단계에 대응하는 수학적 문장을 `--` 주석으로 적으라.

```savedLean -keep
theorem exercise_subset_trans {A : Type} (S T U : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U) :
    S ⊆ U := by
  sorry
```

*문제 3* $`S \setminus S`가 공집합의 부분집합임을 증명하라.

```savedLean -keep
theorem exercise_diff_self_subset_empty
    {A : Type} (S : Set A) :
    S \ S ⊆ ∅ := by
  sorry
```

*문제 4* $`T \subseteq U`이면 $`S \setminus U \subseteq S \setminus T`임을 보이라.

```savedLean -keep
theorem exercise_diff_antitone_right
    {A : Type} (S T U : Set A)
    (hTU : T ⊆ U) :
    S \ U ⊆ S \ T := by
  sorry
```

*문제 5* (포함 관계와 합집합)

(1) $`S\subseteq T`이면 $`S\cup T=T`임을 증명하라.
(2) 첫 결과와 본문의 `twoThree_subset_positives`를 사용하여
$`\{2,3\}\cup\mathbb{N}_{>0}=\mathbb{N}_{>0}`임을 보이라.

```savedLean -keep
theorem exercise_union_eq_right {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∪ T = T := by
  sorry

theorem exercise_twoThree_union_positives :
    twoThree ∪ positives = positives := by
  sorry
```

*문제 6* (흡수법칙)

$`S\cap(S\cup T)=S`임을 증명하라.
원소별로 두 방향을 보인 뒤, 본문의 `inter_eq_left_of_subset`을 사용한 증명도 작성하라.

```savedLean -keep
theorem exercise_inter_union_absorb {A : Type}
    (S T : Set A) :
    S ∩ (S ∪ T) = S := by
  sorry
```

*문제 7* (구체적인 교집합과 차집합)

$`T=\{3,4\}`라 하자. 앞에서 정의한 `twoThree`를 사용하여
$`\{2,3\}\cap T=\{3\}`과 $`\{2,3\}\setminus T=\{2\}`를 각각 증명하라.
두 증명에서 $`3`을 다루는 방식이 어떻게 다른지 비교하라.

```savedLean -keep
def practiceThreeFour : Set Nat :=
  fun n => n = 3 ∨ n = 4
theorem exercise_twoThree_inter :
    twoThree ∩ practiceThreeFour = (fun n => n = 3) := by
  sorry

theorem exercise_twoThree_diff :
    twoThree \ practiceThreeFour = (fun n => n = 2) := by
  sorry
```

*문제 8* (포함 관계의 반례)

(1) $`\mathbb{N}_{>0}\not\subseteq\{2,3\}`임을 증명하라.
(2) 첫 결과를 사용하여 두 집합이 서로 다름을 보이라.

```savedLean -keep
theorem exercise_positives_not_subset_twoThree :
    ¬ positives ⊆ twoThree := by
  sorry

theorem exercise_positives_ne_twoThree :
    positives ≠ twoThree := by
  sorry
```

*문제 9* (드모르간 법칙)

$`(S\cup T)^{\mathsf c}=S^{\mathsf c}\cap T^{\mathsf c}`임을 증명하라.
원소 조건을 이용하여 합집합에 속하지 않는다는 말이 두 집합 각각에 속하지 않는다는 말과 동치임을 보이라.

```savedLean -keep
theorem exercise_compl_union {A : Type} (S T : Set A) :
    (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  sorry
```

*문제 10* (공집합인 차집합)

$`S\setminus T=\varnothing`일 필요충분조건이 $`S\subseteq T`임을 증명하라.

```savedLean -keep
theorem exercise_diff_empty_iff {A : Type}
    (S T : Set A) :
    S \ T = ∅ ↔ S ⊆ T := by
  sorry
```

*힌트* $`S\setminus T=\varnothing`에서 $`S\subseteq T`를 보일 때는 원소 $`x\in S`를 택하라. $`x\notin T`라고 가정하면 $`x`가 차집합에 속하여 모순이 생긴다.

```savedLean
end Course
```
