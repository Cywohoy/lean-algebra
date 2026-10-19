import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Arithmetic
import AlgebraBook.Functions
import AlgebraBook.Preliminaries
import AlgebraBook.Cardinality
import AlgebraBook.Tactic.Auto

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "부록: 전술 일람" =>

%%%
tag := "tactic-reference"
file := "tactics"
number := false
%%%

전술(tactic)은 현재의 가정으로 목표를 증명하는 과정을 한 단계씩 적는 명령이다.
이 부록에서는 본문에서 사용한 명령을 추론의 역할에 따라 정리하고,
각 예제에서 가정과 목표가 어떻게 바뀌는지 설명한다.
처음 증명을 읽을 때는 {ref "using-proofs"}[증명의 구성과 사용]을 따라가고,
명령의 사용법을 다시 확인할 때 이 부록을 참고하라.

Ample에서 제공하는 전술은 `open Ample` 또는 `open scoped Ample`로 사용할 수 있다.
아래 예제에는 이 설정과 고전논리 설정을 미리 적용했으며,
자동 표현 정리는 {ref "tactic-auto-normalization"}[해당 절]에서 따로 켠다.

```savedComment
전술 일람: 기본 전술의 실행 가능한 예제이다.
```

```savedImport
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Arithmetic
import AlgebraBook.Functions
import AlgebraBook.Preliminaries
import AlgebraBook.Cardinality
import AlgebraBook.Tactic.Auto
```

```savedLean
namespace TacticExamples
```

```savedLean -show
open scoped Ample Classical
```

# 전술 찾아보기
%%%
tag := "tactic-index"
file := "index"
%%%

본문과 연습문제에서 사용하는 명령을 역할별로 정리하면 다음과 같다.
각 설명에서는 기본 용법을 먼저 살펴보고 가정에서의 적용이나 여러 목표를 다루는 용법을 이어서 다룬다.
`let`·`have`와 `calc`도 증명 안에서 사용하는 명령이므로 같은 표에 모았다.
연습문제의 `sorry`는 독자가 완성할 증명의 자리이다.

:::table +header (align := left)
*
  * 분류
  * 명령
  * 역할
  * 설명
*
  * 증명의 구성
  * `intro`, `exact`, `apply`
  * 가정을 도입하고 주어진 증명을 사용한다.
  * {ref "tactic-hypotheses"}[가정과 정리]
*
  * 증명의 구성
  * `let`, `have`, `suffices`
  * 대상과 보조정리를 정의하거나 충분한 조건을 목표로 삼는다.
  * {ref "tactic-local-definitions"}[대상과 보조정리], {ref "tactic-suffices-search"}[충분한 조건]
*
  * 증명의 구성
  * `case`
  * 이름으로 증명할 목표를 선택한다.
  * {ref "tactic-select-items"}[항목의 선택과 명명]
*
  * 구성과 분해
  * `constructor`, `and_intros`, `unpack`, `rcases`
  * 성분을 함께 제시하거나 묶인 대상에서 성분을 꺼낸다.
  * {ref "tactic-conjunctions"}[논리곱], {ref "tactic-unpack"}[곱 구조와 패턴]
*
  * 구성과 분해
  * `exists`
  * 조건을 만족하는 원소를 제시하여 존재명제를 증명한다.
  * {ref "tactic-existence"}[존재명제]
*
  * 구성과 분해
  * `left`, `right`, `cases`
  * 논리합의 한쪽을 증명하거나 생성자에 따라 경우를 나눈다.
  * {ref "tactic-disjunctions"}[논리합과 생성자]
*
  * 구성과 분해
  * `trivial`, `contradiction`
  * 참인 명제를 증명하거나 모순인 가정으로 목표를 증명한다.
  * {ref "tactic-true-and-false"}[참과 모순]
*
  * 경우 구분과 귀납법
  * `by_cases`, `by_contra`, `wlog`, `induction`
  * 경우 구분, 귀류법, 경우 환원과 귀납법을 사용한다.
  * {ref "tactic-cases-and-induction"}[논증 방법]
*
  * 정의와 등식
  * `change`, `dsimp`, `expand`, `expand!`
  * 정의상 같은 표현으로 바꾸거나 정의를 펼쳐 계산한다.
  * {ref "tactic-unfold-auto"}[정의와 계산]
*
  * 정의와 등식
  * `rfl`, `symm`, `rw`, `calc`
  * 등식을 확인하고 식을 바꾸거나 여러 등식을 이어 쓴다.
  * {ref "tactic-equality"}[등식의 사용], {ref "tactic-calc"}[등식의 연쇄]
*
  * 정의와 등식
  * `simp`
  * 등록된 정리를 사용하여 식을 정리한다.
  * {ref "tactic-simp"}[간단한 식의 정리]
*
  * 등식의 비교
  * `ext`, `indisc`, `congr`, `funext`
  * 전체 등식과 원소별·성분별 비교 조건을 연결한다.
  * {ref "tactic-equality-comparison-rules"}[전체 등식과 비교 조건]
*
  * 계산과 자동화
  * `decide`
  * 계산으로 참·거짓을 판정할 수 있는 명제를 증명한다.
  * {ref "tactic-functions-and-computation"}[명제의 판정]
*
  * 계산과 자동화
  * `arith`
  * 배운 산술 성질과 가정을 연결하여 목표를 증명한다.
  * {ref "tactic-arith"}[산술 계산]
*
  * 계산과 자동화
  * `card`
  * 주어진 크기 관계와 기본 정리를 연결한다.
  * {ref "tactic-card"}[집합의 크기]
:::

표현을 단계마다 정리하는 `open scoped Ample.Auto`의 범위와 동작은
{ref "tactic-auto-normalization"}[자동 표현 정리]에서 설명한다.

기본 용법은 본문의 증명을 읽고 연습문제를 푸는 데 사용하는 형태이다.
확장 용법은 여러 증명 의무를 묶거나 이미 얻은 증명들을 조립할 때 찾아볼 수 있다.
한 전술에도 두 종류의 용법이 있으므로 명령의 이름보다 사용 형태를 기준으로 구분하라.

:::table +header (align := left)
*
  * 용법
  * 처음 익힐 형태
  * 필요할 때 찾아볼 확장
*
  * 추론
  * `intro`, `apply r`, `exact`
  * `apply r at h`, `apply goal`, `intro at`
*
  * 구성과 분해
  * `constructor`, `unpack h`, `cases h`, `rcases h`
  * `constructor at`, `unpack goals`, `rcases goals`, `cases goal`, `cases at`
*
  * 등식의 비교
  * `ext`, `indisc at h`
  * `ext at`, 목표에서의 `indisc`, `indisc goals`
*
  * 귀납과 경우 환원
  * `induction n`, `wlog`
  * `induction at`, `wlog at`
:::

각 절의 첫 예제는 기본 용법에서 출발한다.
가정에서 증명을 조립하거나 여러 목표를 묶는 용법은 필요한 때 찾아보라.
이들 용법에 공통인 이름과 패턴의 규칙은
{ref "tactic-select-items"}[항목의 선택과 명명]에서,
지원 범위와 수정 방법은 {ref "tactic-failures"}[실패 사례와 수정]에서 확인할 수 있다.

# 증명의 구성
%%%
tag := "tactic-proof-organization"
file := "proof-organization"
%%%

함의나 전칭명제의 가정을 도입하고 주어진 증명으로 결론을 얻는 방법을 정리한다.
이어서 증명 안에서 사용할 대상과 보조정리를 정의하고,
원래 목표에 충분한 조건을 새 목표로 삼는 방법을 살펴본다.

## 가정과 정리의 사용
%%%
tag := "tactic-hypotheses"
file := "hypotheses"
%%%

목표 `P → R`을 증명하려면 `P`를 가정하여 `R`을 보인다.
`intro hP`는 이 가정을 `hP : P`로 도입하고 `R`을 새 목표로 삼는다.
이후에 목표와 같은 명제의 증명 `hR : R`을 얻었다면 `exact hR`로 증명을 마친다.

*보기* `hPQ : P → Q`와 `hQR : Q → R`가 주어졌을 때 `P → R`을 증명하자.
`R`을 얻는 데 필요한 `Q`를 먼저 목표로 삼고,
다시 `Q`를 얻는 데 필요한 `P`를 목표로 삼을 수 있다.

```savedLean
example
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP
```

`apply hQR`는 목표 `R`을 전제 `Q`로 바꾸고,
`apply hPQ`는 그 목표를 `P`로 바꾼다.
마지막 목표의 증명은 처음 도입한 `hP`이다.

*확장: 가정에서의 적용.* 같은 함의를 가정에 사용하면 전제의 증명으로 결론을 얻는다.
다음의 `apply hPQ at hP with hQ`는 `hP : P`와 `hPQ : P → Q`로
새 증명 `hQ : Q`를 만들며 원래 가정 `hP`도 유지한다.

```savedLean
example
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R)
    (hP : P) :
    R := by
  apply hPQ at hP with hQ
  apply hQR
  exact hQ
```

`with hQ`를 생략한 `apply hPQ at hP`는 가정의 이름을 `hP`로 유지하여
`hP : Q`를 얻는다. 두 형태 모두 `hPQ hP`라는 증명 적용에 근거한다.
정리에 인수를 직접 넣는 표현은 {ref "proofs-proof-application"}[증명의 적용]에서 설명한다.

두 전제를 차례로 받는 정리에는 두 증명을 순서대로 공급할 수 있다.
이때 논리곱 하나의 증명은 인수 하나로 유지한다.

```savedLean
example
    (P Q R : Prop)
    (step : P → Q → R)
    (hP : P)
    (hQ : Q) :
    R := by
  apply step at hP hQ with hR
  exact hR
```

함의를 만드는 방향에서는 `intro at`으로 함수의 본문에 해당하는 증명을 사용할 수 있다.
아래에서는 `hQ`를 이미 알고 있으므로 `P`를 가정한 뒤에도 그 증명으로 `Q`를 얻는다.

```savedLean
example
    (P Q : Prop)
    (hQ : Q) :
    P → Q := by
  intro at hQ with h
  exact h
```

결과 타입이 현재 목표에서 정해지지 않으면 `: P → Q`처럼 지정한다.
원소에 따라 결론이 달라지는 함수에서는 임의의 원소에 사용할 수 있는 증명이 필요하며,
특정 원소에서 얻은 증명을 그대로 전칭명제의 증명으로 일반화하지 않는다.

## 전칭명제
%%%
tag := "tactic-universal-statements"
file := "universal-statements"
%%%

목표 `∀ x : A, P x`에서 `intro x`를 쓰면 임의의 `x : A`를 도입하고 `P x`를 증명한다.
함의의 가정을 도입하는 `intro h`와 같은 문법을 사용하지만,
여기서 새로 생기는 `x`는 명제의 증명이 아니라 `A`의 원소이다.

```savedLean
example
    (A : Type) :
    ∀ x : A, x = x := by
  intro x
  rfl

example (A : Type) (P : A → Prop)
    (h : ∀ x, P x)
    (a : A) :
    P a := by
  apply h
```

둘째 예제에서는 전칭명제의 증명 `h`를 원소 `a`에서 사용한다.
`apply h`는 결론을 `P a`에 맞추어 원소를 정하며,
같은 증명을 `exact h a`로 적을 수도 있다.
`h`는 원소를 받아 그 원소에 관한 증명을 주는 함수이므로 `h a`는 `P a`의 증명이다.
이는 전제의 증명을 인수로 받는 함의의 적용 `hPQ hP`와 인수의 역할이 다르다.
함의와 원소 대입을 함께 사용하는 과정은
{ref "proofs-universal-statements"}[전칭명제]에서 다룬다.

### 확장 용법: 사용할 명제의 구성
%%%
tag := "tactic-extension-apply-goal"
%%%

사용하려는 전칭명제 자체를 새 목표로 삼을 때는 `apply goal`을 사용할 수 있다.
이 명령에는 정리의 증명 대신 그 명제를 적고, 그 명제의 증명을 새로 요구한다.

```savedLean
example
    (A : Type) (P : A → Prop) (a : A)
    (h : ∀ x, P x) :
    P a := by
  apply goal (∀ x, P x) with all
  exact h
```

처음 목표는 `P a`이고 새 목표는 `∀ x, P x`이다.
새 전칭명제의 증명을 원소 `a`에 적용하여 원래 목표를 얻는다.
함의 `P → Q`를 새 목표로 삼아 `Q`를 얻으려면 그 함의의 증명과 전제 `P`의 증명이 모두 필요하다.

```savedLean
example
    (P Q : Prop)
    (step : P → Q)
    (hP : P) :
    Q := by
  apply goal (P → Q) with rule premise
  case rule => exact step
  case premise => exact hP
```

## 대상과 보조정리
%%%
tag := "tactic-local-definitions"
file := "local-definitions"
%%%

증명 도중에 사용할 대상은 `let`으로 정의하고,
뒤에서 사용할 사실은 `have`로 증명하여 이름을 붙일 수 있다.
두 명령 모두 `:=` 왼쪽에 이름과 타입을 적고 오른쪽에 그 타입의 항을 적는다.
`have hQ : Q := by`에서는 오른쪽에 `Q`의 증명을 작성한다.

```savedLean
example
    (P Q R : Prop)
    (hP : P)
    (hPQ : P → Q)
    (hQR : Q → R) :
    R := by
  have hQ : Q := by
    apply hPQ
    exact hP

  apply hQR
  exact hQ

example
    (n : Nat) :
    ∃ m : Nat, m = n + n := by
  let twice (k : Nat) : Nat := k + k
  exists (twice n)
```

첫 예제에서는 `have` 아래의 증명이 끝나면 `hQ : Q`를 사용할 수 있다.
이미 증명 `hPQ hP`를 갖고 있으므로 아래처럼 직접 적을 수도 있다.

```savedLean
example
    (P Q : Prop)
    (hP : P)
    (hPQ : P → Q) :
    Q := by
  have hQ : Q :=
    hPQ hP
  exact hQ
```

둘째 예제의 `twice`는 자연수에 관한 지역 함수이며,
`twice n`을 계산하면 `n + n`이므로 원하는 존재명제의 증인을 얻는다.

## 충분한 조건
%%%
tag := "tactic-suffices-search"
file := "suffices-search"
%%%

목표 `H`를 증명하는 데 충분한 조건 `G`를 먼저 보일 수 있다.
`suffices h : G by ...`의 `by` 아래에서는 `h : G`를 사용하여 원래 목표 `H`를 증명하고,
그 연결을 마치면 `G`가 새 목표로 남는다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hP : P) :
    Q := by
  suffices h : P by
    apply hPQ
    exact h

  exact hP
```

이 예제의 연결 증명은 `P`이면 `Q`라는 가정 `hPQ`를 사용한다.
이어지는 `exact hP`는 새 목표 `P`를 증명한다.
원래 목표와 새 조건 사이의 추론도 증명의 일부이므로 `by` 아래에 명시한다.

산술식에서는 그 연결을 `arith`로 확인할 수 있다.
아래 예제에서는 `ym.val < m`이면 나머지가 원래 값과 같으므로
범위 조건을 새 목표로 삼는다.

```savedLean
example
    (m : Nat) (ym : Fin m) :
    ym.val % m = ym.val := by
  suffices bound : ym.val < m by arith
  exact ym.isLt

example (x y m : Nat)
    (hr : x % m = y % m)
    (hq : x / m = y / m) :
    x = y := by
  suffices comparisons :
      x % m = y % m ∧ x / m = y / m by arith
  constructor
  · exact hr
  · exact hq
```

둘째 예제의 새 조건은 논리곱 하나이며 `constructor`로 두 조건을 각각 증명한다.
`suffices` 자체는 명제를 여러 목표로 나누지 않는다.

# 명제와 대상의 구성·분해
%%%
tag := "tactic-logical-structure"
file := "logic"
%%%

명제의 모양에 따라 필요한 증명과 그 증명을 사용하는 방법이 정해져 있다.
논리곱과 곱 구조에서는 성분을 함께 제시하고 존재명제에서는 증인과 그 조건을 제시한다.
논리합에서는 한쪽의 증명으로 논리합을 만들 수 있으며,
그 증명을 사용할 때는 어느 쪽이 성립하든 결론을 얻어야 한다.

## 구성과 사용의 대응
%%%
tag := "tactic-introduction-elimination"
file := "introduction-elimination"
%%%

증명을 만드는 도입 규칙과 주어진 증명에서 결론을 얻는 제거 규칙을 나란히 정리하면 다음과 같다.
각 규칙은 목표에서 필요한 증명을 요구하고 가정에서 그 증명들을 사용한다.

:::table +header (align := left)
*
  * 명제나 대상
  * 도입
  * 제거 또는 사용
*
  * 함의와 전칭명제
  * `intro`로 인수를 도입하고 본문을 증명한다.
  * `apply` 또는 증명에 인수를 적용한다.
*
  * 논리곱과 곱 구조
  * `constructor`로 각 인수의 증명을 요구한다.
  * `unpack`으로 각 성분을 꺼낸다.
*
  * 논리합과 합 구조
  * `left`·`right`로 어느 생성자인지 정한다.
  * `cases`로 각 경우에서 결론을 얻는다.
*
  * 존재명제
  * `exists`로 증인과 조건을 제시한다.
  * `unpack`으로 증인과 조건을 도입하거나 `cases`로 각 증인에서 결론을 얻는다.
*
  * 대상의 등식
  * `ext`로 비교 조건을 증명한다.
  * `indisc`으로 등식에서 비교 조건을 얻는다.
*
  * 자연수에 관한 전칭명제
  * `induction`으로 기초 단계와 귀납 단계를 결합한다.
  * 전칭명제의 증명을 원하는 자연수에서 사용한다.
:::

도입 규칙과 제거 규칙은 각각 필요한 전제와 결론이 있다.
논리합의 도입은 한쪽의 증명으로 충분하고,
제거에서는 두 경우가 모두 결론을 보장해야 한다.
이 추가 조건도 증명 의무에 포함하므로 규칙을 뒤집을 때 임의의 결론을 얻지 않는다.

`case`는 열린 목표를 선택하고 `have`·`let`은 증명 안의 이름을 정의한다.
`rfl`, `decide`, `arith`처럼 목표를 해결하는 명령으로 새 사실을 얻으려면
`have h : 명제 := by ...` 아래에 그 명령을 적는다.
논증의 규칙, 문맥의 구성, 표현 변환과 목표의 계산을 이 역할에 따라 구별한다.

## 논리곱
%%%
tag := "tactic-conjunctions"
file := "conjunctions"
%%%

`P ∧ Q`의 증명을 만들려면 `P`와 `Q`의 증명이 각각 필요하다.
`constructor`는 이 구성 규칙을 목표에서 거꾸로 사용하여 두 증명 의무를 만든다.
`with first second`로 이름을 붙이면 `case`로 각 목표를 선택할 수 있다.

```savedLean
example
    (P Q : Prop)
    (hP : P)
    (hQ : Q) :
    P ∧ Q := by
  constructor with first second
  case first => exact hP
  case second => exact hQ

example
    (P Q : Prop)
    (hP : P)
    (hQ : Q) :
    P ∧ Q := by
  have h : P ∧ Q := by
    constructor with first second
    case first => exact hP
    case second => exact hQ

  exact h

example
    (P Q : Prop)
    (hP : P)
    (hQ : Q) :
    P ∧ Q := by
  constructor at hP hQ with h
  exact h
```

첫 증명에서는 두 목표를 각각 증명한다.
둘째 증명에서는 같은 논증으로 보조정리 `h`를 만든 뒤 사용한다.
셋째 증명의 `constructor at hP hQ with h`는 그 보조정리를 만드는 부분을 한 줄로 적은 것이다.
이 명령은 `h : P ∧ Q`를 추가하며 원래 두 가정도 유지한다.

결과의 명제를 지정하려면 `constructor at hP hQ with h : P ∧ Q`로 쓴다.
전술은 결과 타입의 생성자가 요구하는 인수의 개수와 타입을 확인한다.
두 명제의 증명을 결합할 때 기본으로 얻는 결과는 그 명제들의 논리곱이다.

이미 논리곱의 증명 `h : P ∧ Q`를 알고 있다면 `unpack`으로 두 증명을 꺼낸다.
`with ⟨hP, hQ⟩`는 가정 하나의 곱 구조에서 꺼낼 두 성분에 이름을 붙인다.

```savedLean
example
    (P Q : Prop)
    (h : P ∧ Q) :
    Q ∧ P := by
  unpack h with ⟨hP, hQ⟩
  constructor at hQ hP with swapped
  exact swapped
```

`unpack`의 분해 규칙을 목표에서 거꾸로 사용하면 두 목표를 논리곱 하나로 묶는다.
새 목표 `combined`의 증명을 얻으면 그 두 성분이 원래 목표의 증명이 된다.

```savedLean
example
    (P Q : Prop)
    (h : P ∧ Q) :
    P ∧ Q := by
  constructor with first second
  unpack goals first second with combined
  exact h
```

중첩된 논리곱을 모두 나누어 각각 증명하려면 `and_intros`를 사용한다.
`P ∧ Q ∧ R`에서는 `P`, `Q`, `R`의 세 목표를 정의에 적은 순서대로 얻는다.

```savedLean
example
    (P Q R : Prop)
    (hP : P)
    (hQ : Q)
    (hR : R) :
    P ∧ Q ∧ R := by
  and_intros
  · exact hP
  · exact hQ
  · exact hR
```

`and_intros`도 가정에서 사용할 수 있다.
명제를 각각 증명한 뒤 그 결과를 한 번에 결합하려면
`and_intros at hP hQ hR with h`로 쓴다.

```savedLean
example
    (P Q R : Prop)
    (hP : P)
    (hQ : Q)
    (hR : R) :
    P ∧ Q ∧ R := by
  and_intros at hP hQ hR with h
  exact h
```

인수의 명제가 이미 논리곱이면 그 인수는 묶음 하나로 유지한다.
예를 들어 `hPQ : P ∧ Q`와 `hR : R`를 공급하면 `(P ∧ Q) ∧ R`를 얻는다.

## 곱 구조와 분해 패턴
%%%
tag := "tactic-unpack"
file := "unpack"
%%%

`unpack`은 곱 구조를 가진 대상 하나에서 한 단계의 성분들을 꺼낸다.
논리곱에서는 두 명제의 증명을, 순서쌍에서는 두 성분을 꺼낸다.
부분타입과 `Fin`에서는 값과 그 값에 대한 조건의 증명을 꺼낸다.
존재명제에서도 증인과 그 증인에 대한 조건을 얻을 수 있다.
구조체의 성분은 사영 함수로 꺼내고 원래 대상도 유지한다.
존재명제처럼 증인을 논증 안에 도입해야 하는 경우에는 한 생성자의 구성에 따라 성분을 얻는다.
이들 대상은 생성자가 하나이므로 경우를 여러 분기로 나눌 필요가 없다.

```savedLean
example
    (a b : Nat)
    (p : Nat × Nat)
    (h : p = (a, b)) :
    p.1 = a := by
  unpack p with ⟨x, y⟩

  -- x와 y는 각각 p.1과 p.2의 지역 정의이다.
  indisc at h with hx hy
  exact hx

example
    (A : Type)
    (P : A → Prop)
    (h : ∃ x, P x) :
    ∃ x, P x := by
  unpack h with ⟨x, hx⟩
  exists x
```

첫 예제의 성분 `x`와 `y`는 각각 자연수이다.
둘째 예제의 `x`는 `A`의 원소이고 `hx`는 `P x`의 증명이므로
뒤의 성분이 앞의 성분에 의존한다.
존재명제의 증명에서 원소를 꺼내 다른 명제를 증명할 수 있는 범위는
{ref "functions-existence-and-values"}[원소의 선택과 역함수]에서 설명한다.

중첩된 곱은 `unpack`을 한 번 더 적용하여 나누거나,
`rcases`에 그 구조를 나타내는 패턴을 적어 나눌 수 있다.
`unpack`에는 한 층의 성분 이름만 적는다.

```savedLean
example
    (P Q R : Prop)
    (h : P ∧ (Q ∧ R)) :
    R := by
  unpack h with ⟨hP, rest⟩
  unpack rest with ⟨hQ, hR⟩
  exact hR

example
    (P Q R : Prop)
    (h : P ∧ (Q ∧ R)) :
    R := by
  rcases h with ⟨hP, ⟨hQ, hR⟩⟩
  exact hR
```

`rcases`의 패턴은 경우 구분도 지정할 수 있다.
아래의 `⟨hP, hQ⟩ | hR`는 왼쪽 경우의 곱을 분해하고
오른쪽 경우의 증명에는 `hR`라는 이름을 붙인다.

```savedLean
example
    (P Q R : Prop)
    (h : (P ∧ Q) ∨ R) :
    Q ∨ R := by
  rcases h with ⟨hP, hQ⟩ | hR
  · left
    exact hQ

  · right
    exact hR
```

`cases`는 생성자에 따라 경우를 나누는 기본 전술이고,
`rcases`는 이 경우 구분과 곱 구조의 분해를 패턴에 따라 이어서 수행한다.
곱 구조 하나의 성분을 꺼낼 때는 `unpack`을 기본으로 사용한다.
Lean의 `cases`와 `rcases`도 곱을 분해할 수 있으며,
이 교재에서는 논증의 역할을 드러내기 위해 이 세 명령을 구분한다.

### 확장 용법: 묶인 목표의 구성
%%%
tag := "tactic-extension-unpack-goals"
%%%

목표들을 묶을 때는 `unpack goals`로 한 층의 곱을,
`rcases goals`로 중첩된 곱을 만들 수 있다.

```savedLean
example
    (P Q R : Prop)
    (h : P ∧ Q ∧ R) :
    P ∧ Q ∧ R := by
  constructor with first ⟨second, third⟩
  rcases goals first second third with combined
  exact h
```

이 용법은 같은 문맥의 독립적인 목표를 묶는다.
논리합의 서로 다른 분기나 아직 선택하지 않은 증인에 의존하는 목표를
곱의 성분처럼 묶지는 않는다.

## 동치
%%%
tag := "tactic-equivalence"
file := "equivalence"
%%%

`P ↔ Q`의 증명은 `P → Q`와 `Q → P`의 증명을 함께 담는다.
`constructor`로 두 방향을 각각 증명하거나,
이미 갖고 있는 두 증명을 `constructor at`으로 결합할 수 있다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hQP : Q → P) :
    P ↔ Q := by
  constructor with forward backward
  case forward => exact hPQ
  case backward => exact hQP

example
    (P Q : Prop)
    (hPQ : P → Q)
    (hQP : Q → P) :
    P ↔ Q := by
  constructor at hPQ hQP with h
  exact h
```

동치의 증명 `h : P ↔ Q`에서 `h.mp`는 `P → Q`의 증명이고
`h.mpr`는 `Q → P`의 증명이다.
이를 `apply`로 사용하거나 `h.mp hP`처럼 전제의 증명을 직접 넣을 수 있다.

## 존재명제
%%%
tag := "tactic-existence"
file := "existence"
%%%

목표 `∃ x : A, P x`를 증명하려면 원소 `a : A`를 택하고 `P a`를 보여야 한다.
`exists a`는 이 원소를 제시하고 그 조건을 새 목표로 삼는다.
조건이 정의상 같은 등식이면 `exists`가 그 등식까지 확인한다.

```savedLean
example
    (n : Nat) :
    ∃ m : Nat, m = n + 1 := by
  exists (n + 1)
```

존재명제의 증명 `h : ∃ x, P x ∧ Q x`에서는
`rcases h with ⟨x, hP, hQ⟩`로 원소 `x`와 두 조건의 증명을 얻는다.
이 패턴은 증인을 꺼낸 뒤 그 증인에 관한 논리곱을 다시 나눈다.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∃ x, P x ∧ Q x) :
    ∃ x, Q x ∧ P x := by
  rcases h with ⟨x, hP, hQ⟩
  exists x
```

남은 조건 `Q x ∧ P x`는 이미 얻은 두 증명으로 확인된다.
`constructor at x hP with h : ∃ y, P y`처럼 원소와 그 원소에 대한 증명을
존재명제의 증명으로 묶을 수도 있다.
이 경우 둘째 인수의 타입은 첫째 인수의 값에 의존한다.

```savedLean
example
    (A : Type) (P : A → Prop) (a : A)
    (ha : P a) :
    ∃ x, P x := by
  constructor at a ha with h
  exact h
```

증인을 아직 정하지 않은 목표와 그 증인에 의존하는 조건 목표는
독립적인 두 목표처럼 묶을 수 없다.
존재명제를 새로 증명할 때는 `exists`로 증인을 정하는 순서를 따른다.

`exists`도 선택한 원소와 조건의 증명으로 존재명제의 증명을 만드는 방향으로 사용할 수 있다.

```savedLean
example
    (A : Type)
    (P : A → Prop)
    (a : A)
    (ha : P a) :
    ∃ x, P x := by
  exists a at ha with h
  exact h
```

`a`는 증인이고 `ha`는 그 증인에 대한 조건의 증명이다.
현재 목표가 존재명제가 아니면 `exists a at ha with h : ∃ x, P x`로 결과를 명시한다.
존재명제에서 결론을 얻는 일반적인 제거 규칙은
증인마다 그 조건에서 결론을 얻는 함의 `∀ x, P x → R`를 요구한다.
이 함의를 이미 갖고 있다면 `cases at`으로 사용할 수 있다.

```savedLean
example
    (A : Type) (P : A → Prop) (R : Prop)
    (h : ∃ x, P x)
    (step : ∀ x, P x → R) :
    R := by
  cases at h step with result
  exact result
```

### 조건을 갖춘 원소
%%%
tag := "tactic-element-construction"
file := "element-construction"
%%%

존재명제를 증명하는 것과 조건을 갖춘 원소를 만드는 것은 결과의 타입이 다르다.
`∃ x, P x`의 결과는 명제의 증명이며,
`Elem S`의 결과는 집합 `S`의 원소를 값과 원소 조건의 증명으로 함께 담은 대상이다.

부분타입에는 `{ val := 값, property := 증명 }`을 쓰고,
`Fin n`에는 `{ val := 값, isLt := 증명 }`을 쓴다.

```savedLean
def tactic_fin_three_element : Fin 3 :=
  { val := 2, isLt := by decide }
```

이 정의의 결과는 `Fin 3`의 원소이며 `.val`로 값 `2`를,
`.isLt`로 범위 조건 `2 < 3`의 증명을 꺼낼 수 있다.
`a ∈ S`라는 명제와 `Elem S`의 원소의 차이는
{ref "functions-elements"}[집합 위의 함수]에서 설명한다.

## 논리합과 생성자의 경우 구분
%%%
tag := "tactic-disjunctions"
file := "disjunctions"
%%%

`P ∨ Q`를 보일 때는 어느 쪽이 성립하는지 제시하면 된다.
`left`는 `P`를, `right`는 `Q`를 새 목표로 삼는다.
논리합의 증명 `h`를 사용하는 경우에는 `cases h`로 두 경우를 각각 다룬다.

```savedLean
example
    (P Q : Prop)
    (h : P ∨ Q) :
    Q ∨ P := by
  cases h with
  | inl hP =>
    right
    exact hP

  | inr hQ =>
    left
    exact hQ
```

첫 경우에는 `hP : P`로 `Q ∨ P`의 오른쪽을 증명하고,
둘째 경우에는 `hQ : Q`로 왼쪽을 증명한다.
`inl`과 `inr`는 논리합을 만드는 두 생성자의 이름이다.
두 분기는 서로 다른 가정 아래의 증명이며 `P`와 `Q`를 동시에 가정하는 상황과 구별한다.


*확장: 가정에서의 구성.* `left`와 `right`도 가정에서 논리합을 만드는 방향으로 사용할 수 있다.

```savedLean
example
    (P Q : Prop)
    (hP : P) :
    P ∨ Q := by
  left at hP with h
  exact h

example
    (P Q : Prop)
    (hQ : Q) :
    P ∨ Q := by
  right at hQ with h
  exact h
```

`left at hP with h : P ∨ Q`처럼 결과를 명시할 수도 있다.
현재 목표가 논리합이면 나머지 명제를 그 목표에서 알아내고,
그렇지 않으면 아직 정하지 않은 명제로 남긴다.
결과를 바로 정하려면 `: P ∨ Q`를 덧붙인다. 후속 추론에서 정해지면 그 명제를 사용하며,
끝까지 정해지지 않으면 `alternative`라는 이름의 명제 선택 목표가 남는다.

```savedLean
example
    (P Q R : Prop)
    (hP : P)
    (step : P ∨ Q → R) :
    R := by
  left at hP with h
  apply step at h with result
  exact result
```

`left`를 적용한 직후에는 오른쪽 명제가 미정이지만,
`step`의 전제가 `P ∨ Q`이므로 다음 적용에서 그 명제를 `Q`로 정한다.

### 확장 용법: 경우별 증명의 조립
%%%
tag := "tactic-extension-cases"
%%%

논리합의 증명을 사용할 때는 어느 경우가 주어졌든 결론을 얻어야 한다.
각 경우의 함의를 이미 증명했다면 `cases at`으로 결론을 만들 수 있다.

```savedLean
example
    (P Q R : Prop)
    (h : P ∨ Q)
    (fromP : P → R)
    (fromQ : Q → R) :
    R := by
  cases at h fromP fromQ with result
  exact result

example
    (P Q R : Prop)
    (h : P ∨ Q)
    (fromP : P → R)
    (fromQ : Q → R) :
    R := by
  cases goal (P ∨ Q) with source leftBranch rightBranch
  case source => exact h
  case leftBranch => exact fromP
  case rightBranch => exact fromQ
```

둘째 증명의 새 목표는 논리합 `P ∨ Q`와 두 함의 `P → R`, `Q → R`이다.
`cases h`는 논리합의 증명 `h`를 미리 공급한 뒤 각 함의의 가정을 도입하여 경우를 나누는 형태이다.
분기의 함의에는 서로 다른 가정이 있으므로 논리곱의 두 성분과 구별한다.
`P ∨ Q`에서 `P`만 얻으려면 오른쪽 경우에서도 `P`를 얻는 근거가 필요하다.

## 부정
%%%
tag := "tactic-negation"
file := "negation"
%%%

`¬ P`는 `P → False`로 정의되므로 부정을 증명할 때도 함의를 증명하는 방법을 사용한다.
`intro hP`로 `P`를 가정하면 남은 목표는 `False`이다.
가정 `hnotQ : ¬ Q`를 사용할 때는 `apply hnotQ`로 모순에 필요한 `Q`를 목표로 삼을 수 있다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hnotQ : ¬ Q) :
    ¬ P := by
  intro hP
  apply hnotQ
  apply hPQ
  exact hP
```

이 증명의 목표는 `¬ P`, `False`, `Q`, `P`의 순서로 바뀐다.
마지막 `P`의 증명은 처음 도입한 `hP`이며,
이를 두 함의에 적용하여 모순을 얻는다.

```savedLean
example
    (P : Prop)
    (hP : P)
    (hnotP : ¬ P) :
    False := by
  apply hnotP at hP with hFalse
  exact hFalse
```

여기서 `hnotP`는 `P → False`의 증명이므로
가정에서 적용한 결과 `hFalse`의 타입은 `False`이다.

## 참과 모순
%%%
tag := "tactic-true-and-false"
file := "true-and-false"
%%%

`True`는 항상 참인 명제이므로 `trivial`로 증명할 수 있다.
`False`의 증명을 가정으로 갖고 있으면 모순에서 임의의 결론을 얻으며,
이때 `contradiction`으로 현재 목표를 해결한다.

```savedLean
example : True := by
  trivial

example
    (P : Prop)
    (h : False) :
    P := by
  contradiction
```

두 전술이 사용하는 기본 원리는 각각 `True.intro`와 `False.elim`이다.
`exact True.intro`는 참인 명제의 증명을 직접 제시하고,
`exact False.elim h`는 모순의 증명 `h`에서 결론을 얻는다.

`cases h`도 `h : False`가 생길 수 있는 경우를 나누려는 명령이다.
`False`에는 생성자가 없으므로 다룰 경우가 남지 않아 증명이 끝난다.
이 원리를 집합에 사용하는 예는 {ref "sets-basic-subsets"}[전체집합과 공집합]에서 다룬다.

### 증명 원리와 전술
%%%
tag := "tactic-proof-principles"
file := "proof-principles"
%%%

`apply`와 `exact` 뒤에는 사용할 증명을 적는다.
`False.elim`이나 `propext`도 이런 증명 원리이며,
각각의 타입이 어떤 전제에서 어떤 결론을 얻는지 알려 준다.

:::table +header (align := left)
*
  * 원리
  * 전제와 결론
  * 전술에서의 사용
*
  * `True.intro`
  * 참인 명제 `True`의 증명
  * `exact True.intro`
*
  * `False.elim`
  * `False`에서 임의의 결론
  * `cases hFalse`
*
  * `Iff.intro`
  * 두 방향의 함의에서 동치
  * `constructor`
*
  * `funext`, `propext`
  * 함수값의 등식이나 명제의 동치에서 등식
  * `ext`
*
  * `classOf_eq_iff`, `parityClass_eq_iff`
  * 대표원의 관계와 몫 원소의 등식
  * `ext`, `indisc`
*
  * `Classical.byContradiction`
  * 부정의 가정에서 모순을 얻어 원래 명제
  * `by_contra`
:::

# 경우 구분과 귀납법
%%%
tag := "tactic-cases-and-induction"
file := "cases-and-induction"
%%%

생성자에 따른 경우 구분은 앞의 `cases`에서 살펴보았다.
여기서는 명제가 성립하는지에 따른 경우 구분과 귀류법을 다루고,
일부 경우로 논증을 환원하는 방법 및 자연수에 대한 귀납법을 정리한다.
`by_cases`는 두 경우에서 원래 목표를 증명하며,
`induction`은 귀납 단계에서 앞선 경우의 증명을 사용할 수 있게 한다.

## 명제에 따른 경우 구분
%%%
tag := "tactic-by-cases"
file := "by-cases"
%%%

`by_cases h : P`는 조건 `P`가 성립하는 경우와 성립하지 않는 경우를 나눈다.
첫 경우에는 `h : P`를, 둘째 경우에는 `h : ¬ P`를 가정으로 갖고 원래 목표를 증명한다.
아래에서는 자연수가 $`0`인지에 따라 두 경우를 다룬다.

```savedLean
example
    (n : Nat) :
    n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · left
    exact h

  · right
    exact h
```

임의의 명제에 대해 경우를 나누면 배중률을 사용한다.
예를 들어 이중 부정 `¬¬ P`에서 `P`를 보일 때는
`P`인 경우에 그 증명을 사용하고 `¬ P`인 경우에 이중 부정과 모순을 얻는다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  by_cases hP : P
  · exact hP
  · have hFalse : False := by
      exact h hP

    contradiction
```

두 번째 경우의 목표도 `P`이며
가정 `hP : ¬ P`로 얻은 `hFalse : False`를 사용하여 이 목표를 증명한다.
집합의 원소 조건에 이 방법을 사용하는 과정은 {ref "sets-classical-logic"}[이중 여집합과 고전논리]에서 살펴볼 수 있다.

`if P then a else b`의 값도 각 경우의 가정으로 정할 수 있다.
`h : P`이면 `ite_eq_left h`가 이 식의 값이 `a`라는 등식의 증명이고
`h : ¬ P`이면 `ite_eq_right h`가 값이 `b`라는 등식의 증명이다.
따라서 `rw [ite_eq_left h]`나 `rw [ite_eq_right h]`로 목표 안의 `if` 식을 바꿀 수 있다.
정의를 펼친 뒤 이 등식을 사용하는 과정은
{ref "cardinality-erasing-an-index"}[번호의 재배열]에서 설명한다.

*확장: 경우별 증명의 결합.* 두 경우에서 같은 결론을 얻는 함의를 이미 증명했다면 가정에서 결합할 수 있다.
`by_cases at positive negative with h`에는 `P → R`와 `¬ P → R`의 증명을 공급한다.

```savedLean
example
    (P R : Prop)
    (positive : P → R)
    (negative : ¬ P → R) :
    R := by
  by_cases at positive negative with h
  exact h
```

목표에서의 `by_cases`는 두 함의를 증명하기 위해 각 가정을 도입한다.
가정에서의 용법은 그 두 함의와 배중률로 결론 `R`을 얻는다.

## 이중 부정과 귀류법
%%%
tag := "tactic-classical-contradiction"
file := "classical-contradiction"
%%%

`by_contra h`는 보이려는 명제의 부정을 가정하고 모순을 얻는 귀류법을 시작하는 전술이다.
아래 예제에서는 목표 `P`의 부정을 `hnotP : ¬ P`로 가정하고,
목표를 `False`로 바꾸므로 주어진 이중 부정의 증명을 사용할 수 있다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  by_contra hnotP
  exact h hnotP
```

`h`는 `¬ P → False`의 증명이므로 `exact h hnotP`로 모순을 얻어 증명을 마친다.
이 예제에서 `by_contra hnotP`는 `apply Classical.byContradiction`과 `intro hnotP`를 차례로 쓴 것과 같다.
목표 자체가 부정인 경우에는 `intro`로 그 부정을 증명할 수 있으며, `by_contra`도 같은 방식으로 가정을 도입한다.

교재의 `by_contra`는 `AlgebraBook.Tactic.Classical`에서 제공하며
Lean의 기본 논리 정리를 사용하여 귀류법을 시작한다.

이중 부정 제거를 직접 사용할 때는 `Classical.not_not.mp`를 적용한다.
이 정리는 `¬¬ P → P`의 증명이므로 목표가 `P`일 때 다음과 같이 사용할 수 있다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  apply Classical.not_not.mp
  exact h
```

`apply` 이후의 목표는 `¬¬ P`이므로 가정 `h`로 증명을 마친다.
`by_cases`는 원래 목표를 유지하며 두 경우를 나누고
`by_contra`는 목표의 부정을 가정하여 `False`를 새 목표로 삼는다.
`Classical.not_not.mp`를 적용한 증명에서는 이미 갖고 있는 이중 부정의 증명을 사용한다.

*확장: 귀류법의 결과 사용.* 필요한 모순을 이미 증명한 경우에는 그 결과를 가정에 적용할 수 있다.

```savedLean
example
    (P : Prop)
    (counter : ¬ P → False) :
    P := by
  by_contra at counter with h
  exact h
```

`counter`는 `¬ P`를 가정하면 모순을 얻는다는 증명이다.
`by_contra at counter`는 고전논리의 귀류법으로 `P`의 증명을 만든다.
자동 표현 정리로 이중 부정이 이미 제거된 경우에는
정리된 증명을 `exact`로 바로 사용할 수 있다.

## 경우의 환원
%%%
tag := "tactic-wlog"
file := "without-loss-of-generality"
%%%

대칭인 문제에서는 한쪽 순서만 다루고 다른 순서를 변수 교환으로 환원할 수 있다.
`wlog hab : a ≤ b generalizing a b with ordered`는 이 논증의 두 부분을 목표로 만든다.

첫 목표에서는 `¬ a ≤ b`를 가정한다. 아래에서는 자동 표현 정리를 켜므로
이 가정이 `hab : b < a`로 표시되며,
`ordered : ∀ a b, a ≤ b → min a b + max a b = a + b`로 제한한 경우의 결과를 사용할 수 있다.
둘째 목표에서는 `hab : a ≤ b`를 가정하여 그 결과를 직접 증명한다.

```savedLean -show
section
open scoped Ample.Auto
```

```savedLean
example
    (a b : Nat) :
    min a b + max a b = a + b := by
  wlog hab : a ≤ b generalizing a b with ordered
  · -- b < a에서 b ≤ a를 얻어 순서를 바꾼 경우에 적용한다.
    have hba : b ≤ a := by arith
    rw [Nat.min_comm a b, Nat.max_comm a b]
    rw [Nat.add_comm a b]
    exact ordered b a hba

  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
```

```savedLean -show
end
```

`generalizing a b`는 `ordered`를 임의의 두 자연수에 적용할 수 있게 한다.
따라서 `ordered b a hba`에서는 첫 번째 수에 `b`를, 두 번째 수에 `a`를 넣는다.
`hba`는 정리된 가정 `b < a`에서 얻은 `b ≤ a`의 증명이다.
일반화한 변수에 의존하는 가정도 함께 포함되며,
`generalizing`을 생략하면 현재 문맥의 변수와 가정을 일반화한다.
`with ordered`는 제한한 경우의 결과에 붙일 이름이다.
이 전술의 수학적 예는 {ref "preliminaries-wlog"}[대칭성을 이용한 경우의 환원]에서 다룬다.

제한한 경우의 결과와 나머지 경우를 환원하는 증명을 이미 갖고 있다면
`wlog at`으로 전체 결과를 만들 수 있다.
환원의 증명에는 제한한 경우의 결과를 인수로 공급한다.

```savedLean
example
    (P R : Prop)
    (restricted : P → R)
    (reduction : (P → R) → ¬ P → R) :
    R := by
  wlog at restricted reduction with h
  exact h
```

`reduction restricted`는 `¬ P → R`의 증명이다.
이를 `restricted : P → R`와 경우 구분으로 결합하면 `R`을 얻는다.
원소들을 일반화한 경우에는 두 증명에 같은 전칭 인수들을 넣어 각 원소에서 이 추론을 수행한다.

## 자연수의 귀납법
%%%
tag := "tactic-induction"
file := "induction"
%%%

`induction n`은 자연수에 관한 목표를 `zero`와 `succ`의 두 경우로 나눈다.
`succ n ih`에서는 이전 자연수 `n`에 관한 귀납 가정 `ih`를 사용할 수 있다.
자연수를 두 경우로 나누기만 할 때는 `cases n`을 사용하며
이 경우에는 귀납 가정이 생기지 않는다.
가정과 목표의 변화는 {ref "preliminaries-induction"}[자연수와 귀납법]에서 설명한다.
귀납 가정을 `∀ n, ...`의 형태로 두고 `cases n`으로 경우를 나누는 예제는
{ref "preliminaries-even-induction"}[짝수와 귀납법]을 참고하라.
귀납 단계에서 다른 변수 `m`의 값도 바뀐다면 `induction n generalizing m`을 사용하여
귀납 가정을 임의의 `m`에 적용할 수 있게 한다.
예를 들어 정의역의 크기가 `m + 1`에서 `m`으로 줄어드는 증명에서 그 크기를 고정하면
줄어든 정의역을 가진 함수에 귀납 가정을 적용할 수 없다.
두 방식에서 얻는 귀납 가정의 비교는 {ref "cardinality-pigeonhole"}[비둘기집 원리]에서 다룬다.

```savedLean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ]
      -- 목표: Nat.succ (0 + n) = Nat.succ n
      rw [ih]
```


### 확장 용법: 귀납 증명의 조립
%%%
tag := "tactic-extension-induction"
%%%

귀납법의 두 부분을 따로 증명한 뒤 전체 결과로 결합할 수도 있다.
`zero : P 0`와 `step : ∀ n, P n → P (n + 1)`를 공급하면
`induction at zero step with h`가 `h : ∀ n, P n`을 만든다.

```savedLean
example
    (P : Nat → Prop) (zero : P 0)
    (step : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  induction at zero step with h
  exact h
```

귀납 단계의 `P n`은 그 단계에서 사용할 귀납 가정이며,
전체 결과를 만드는 데 필요한 인수는 기초 단계의 증명과 귀납 단계의 함의이다.
이 가정 쪽 용법은 현재 자연수의 귀납법을 지원한다.

# 정의와 등식
%%%
tag := "tactic-definitions-and-equality"
file := "definitions-and-equality"
%%%

정의를 펼쳐 계산하는 과정과 등식의 증명으로 식을 바꾸는 과정을 구별하여 살펴본다.
그다음 여러 등식을 이어 쓰는 방법을 정리하고,
함수·집합·순서쌍 등의 전체 등식을 비교 조건과 연결하는 두 방향을 함께 다룬다.

## 정의와 계산
%%%
tag := "tactic-unfold-auto"
file := "unfold-auto"
%%%

정의에 따라 원소 조건을 확인할 때는 같은 명제를 여러 표기로 나타낼 수 있다.
예를 들어 `n ∈ positives`의 정의를 두 번 펼치면 `0 < n`이다.
`change`는 원하는 표기를 직접 적고,
`dsimp`는 지정한 정의를 펼쳐 계산하며,
`expand`는 식에서 펼칠 정의를 찾아 한 층을 드러낸다.

```savedLean
example
    (n : Nat)
    (h : n ∈ Ample.positives) :
    0 < n := by
  change 0 < n at h
  exact h

example
    (n : Nat)
    (h : n ∈ Ample.positives) :
    0 < n := by
  dsimp [Ample.positives] at h
  -- 가정: h : positive n
  dsimp [Ample.positive] at h
  exact h

example
    (n : Nat)
    (h : n ∈ Ample.positives) :
    0 < n := by
  expand at h
  -- 가정: h : positive n
  expand at h
  exact h
```

세 명령 모두 정의상 같은 명제로 가정을 바꾼다.
`change`에는 바꿀 명제를 적어야 하고,
`dsimp [Ample.positives]`에는 펼칠 정의의 이름을 적는다.
`expand`는 바깥 정의 `positives`를 먼저 펼치고 새로 나타난 `positive`는 다음 단계에 남긴다.

목표에 적용하려면 `at h`를 생략한다.
`expand at *`는 목표와 모든 가정을 함께 정리하며,
`expand!`는 새로 나타난 정의도 펼쳐 더 이상 변하지 않을 때까지 반복한다.
재귀함수처럼 계속 새 계산이 나타나는 정의에는 펼칠 단계를 직접 정하는 편이 좋다.

```savedLean
example
    (n : Nat)
    (h : n ∈ Ample.positives) :
    0 < n := by
  expand! at h
  exact h
```

`expand`의 한 층은 식의 각 부분에서 가장 바깥에 있는 교재나 현재 풀이 파일의 정의를 가리킨다.
인수 대입과 지역 정의의 계산, 직접 만든 원소의 성분과
이미 주어진 생성자에 대한 패턴 매칭은 같은 단계에서 계산한다.

```savedLean
example
    (A B : Type) (S : Ample.Set A) (T : Ample.Set B)
    (a : A)
    (b : B)
    (h : (a, b) ∈ Ample.setProduct S T) :
    a ∈ S := by
  expand at h
  unpack h with ⟨ha, hb⟩
  exact ha
```

`expand at h`로 집합의 곱의 정의와 순서쌍의 성분을 계산하면
`h : a ∈ S ∧ b ∈ T`가 된다.
이어 `unpack`으로 두 증명을 꺼낸다.
집합의 정의를 펼치는 계산과 논리곱의 증명을 나누는 추론은 각각 별도의 단계이다.

패턴 매칭으로 정의한 함수도 이미 주어진 순서쌍에 대입하면 계산할 수 있다.

```savedLean
def pairMap
    {A B C D : Type}
    (f : A → C)
    (g : B → D)
    (p : A × B) :
    C × D :=
  let (a, b) := p
  (f a, g b)
example {A B C D : Type}
    (f : A → C) (g : B → D) (a : A) (b : B) (c : C) (d : D)
    (hf : f a = c)
    (hg : g b = d) :
    pairMap f g
    (a, b) =
    (c, d) := by
  expand
  ext
  · exact hf
  · exact hg
```

`expand` 이후에는 `(f a, g b) = (c, d)`가 목표이다.
두 성분의 등식은 `ext`로 각각 증명한다.

## 합동성
%%%
tag := "tactic-congruence"
file := "congruence"
%%%

`congr`는 같은 함수나 연산을 적용한 식의 등식을
그 인수들의 등식으로 바꾸어 증명한다.
기본형은 이 과정을 반복하며 `congr : n`으로 비교의 깊이를 제한한다.
{ref "functions-congruence"}[함수값의 등식]에서는
`congr : 1`로 바깥 함수를 한 번만 제거하여 주어진 점별 등식을 사용했다.

```savedLean
example
    (f g : Nat → Nat) (x y : Nat) :
    f (g (x + y)) = f (g (y + x)) := by
  congr : 2
  exact Nat.add_comm x y
```

`congr : 2`는 공통으로 적용한 `f`와 `g`를 차례로 제거하여
`x + y = y + x`를 새 목표로 삼는다.
깊이를 제한하지 않으면 덧셈의 인수까지 비교하여
일반적으로 증명할 수 없는 `x = y`와 `y = x`를 요구할 수 있다.
`congr`로 얻은 조건은 원래 등식의 충분조건이므로
이미 사용할 등식이 있는 수준에서 비교를 멈추어야 한다.

## 등식의 확인과 사용
%%%
tag := "tactic-equality"
file := "equality"
%%%

등식의 증명에서는 정의에 따른 계산과 이미 증명한 정리에 따른 식의 변환을 구별한다.
`rfl`은 정의와 계산으로 양변이 같아지는 등식을 증명하고,
`rw [h]`는 등식 `h`를 사용하여 한 식을 다른 식으로 바꾼다.

```savedLean
def keep (n : Nat) : Nat := n
example (n : Nat) : keep n = n := by
  rfl

example
    (n m : Nat)
    (h : n = m) :
    n + 1 = m + 1 := by
  rw [h]
```

첫 등식은 `keep n`의 정의에 따라 성립한다.
둘째 등식에서는 `h`로 `n`을 `m`으로 바꾸면 양변이 같아진다.
등식의 반대 방향을 사용하려면 `rw [← h]`로 쓴다.

가정 안의 식도 같은 방법으로 바꿀 수 있다.

```savedLean
example (n m : Nat)
    (h : n = m)
    (hn : n + 1 = 3) :
    m + 1 = 3 := by
  rw [h] at hn
  exact hn

example (a b : Nat)
    (h : b = a) :
    a = b := by
  symm
  exact h

example
    (a b : Nat)
    (h : b = a) :
    a = b := by
  symm at h
  exact h
```

`rw [h] at hn`은 `hn`의 명제를 `m + 1 = 3`으로 바꾼다.
`symm`은 목표 `a = b`를 `b = a`로 바꾸므로 둘째 예제에서 `h`를 바로 사용할 수 있다.
`symm at h`는 가정의 등식도 같은 방향으로 바꾸어 `h : a = b`를 얻는다.

논리적으로 동치인 명제도 `rw`로 바꿀 수 있다.
`h : P ↔ Q`에 대한 `rw [← h]`는 목표 `Q`를 `P`로 바꾼다.

```savedLean
example
    (P Q : Prop)
    (h : P ↔ Q)
    (hP : P) :
    Q := by
  rw [← h]
  exact hP
```

정의의 이름을 적은 `rw [정의 이름]`도 그 정의식을 따라 식을 바꾼다.
여러 등식을 차례로 적용할 때는 `rw [h1, h2]`처럼 나열하며,
등식이 완성되면 `rw`가 증명을 마칠 수 있다.

정리에 필요한 조건이 아직 주어지지 않았다면 그 조건도 증명할 목표로 남는다.
다음 정리 `Nat.mod_eq_of_lt`는 `a < m`일 때 `a % m = a`임을 나타낸다.

```savedLean
example
    (a m : Nat)
    (h : a < m) :
    a % m = a := by
  rw [Nat.mod_eq_of_lt]
  exact h
```

재작성한 등식의 양변은 같아져 자동으로 증명되지만
정리를 사용하기 위한 조건 `a < m`은 남아 있으므로 `exact h`로 확인한다.

## 간단한 식의 정리
%%%
tag := "tactic-simp"
file := "simplification"
%%%

`simp`는 정리 규칙으로 등록된 정리들을 사용하여 식을 정리한다.
정수에서는 `Int.zero_mul`로 `0 * a`를 `0`으로,
`Int.add_zero`로 `b + 0`을 `b`로 바꾼다.
`0 + b`를 `b`로 바꾸는 `Int.zero_add`도 등록되어 있으므로 다음 등식이 증명된다.

```savedLean
example (a b : Int) :
    0 * a + (b + 0) = b := by
  simp
```

`simp at h`는 같은 정리 규칙을 가정 `h`에 사용한다.
아래에서는 가정의 왼쪽 식이 `b`로 정리되어 `h : b = c`를 얻는다.

```savedLean
example (a b c : Int)
    (h : 0 * a + (b + 0) = c) :
    b = c := by
  simp at h
  exact h
```

`dsimp`는 정의에 따른 계산을 수행하고 `simp`는 등록된 정리로도 식을 바꾼다.
사용할 등식을 직접 고르려면 `rw [등식]`을 쓴다.
본문의 첫 예제는 {ref "preliminaries-simp"}[정수의 식 정리]에 있다.

## 등식의 연쇄
%%%
tag := "tactic-calc"
file := "calc"
%%%

`calc`는 여러 등식을 이어서 처음과 끝의 등식을 증명하는 표기이다.
각 줄에서는 해당 등식을 증명하며 `_`는 앞줄의 오른쪽 식을 이어받는다.

```savedLean
example
    (A : Type) (x y z : A)
    (hxy : x = y)
    (hyz : y = z) :
    x = z := by
  calc
    x = y := by exact hxy
    _ = z := by exact hyz
```

이 표기를 처음 소개하는 예제는 {ref "preliminaries-calc"}[등식의 연쇄]를 참고하라.

## 전체 등식과 비교 조건
%%%
tag := "tactic-equality-comparison-rules"
file := "comparison-rules"
%%%

`ext`와 `indisc`은 전체 등식과 비교 조건을 서로 다른 방향으로 연결한다.
본문에서는 주로 목표의 등식을 비교 문제로 바꾸는 `ext`와
등식 가정에서 비교 조건을 꺼내는 `indisc at h`를 사용한다.
예를 들어 순서쌍의 등식을 목표로 하는 `ext`는 두 성분의 등식을 요구하고,
그 순서쌍의 등식을 가정으로 하는 `indisc at h`는 두 성분의 등식을 제공한다.
두 전술의 기본형은 한 겹을 비교하며 새로 얻은 성분까지 비교하려면 한 번 더 적용한다.

이미 주어진 등식으로 목표나 가정의 식을 바꾸려면 `rw`를 사용하면 된다.
`indisc`으로 얻는 비교도 등식에 따른 재작성으로 증명할 수 있으며,
그 비교 조건에 이름을 붙여 따로 사용하려는 경우에는 `indisc`가 편리하다.
가정에서 전체 등식을 얻는 `ext at`과 목표에서 전체 등식을 요구하는 `indisc`도 아래에서 함께 살펴본다.

### 전체 등식의 도출: ext
%%%
tag := "tactic-extensionality"
file := "extensionality"
%%%

`ext`는 외연성 정리에 따라 대상의 등식에 필요한 비교를 새 목표로 삼는다.
비교 조건을 모두 증명하면 처음의 등식도 증명되므로,
순서쌍에서는 각 성분을, 함수에서는 임의의 원소에서 함수값을 비교하면 된다.
`ext at`은 이미 갖고 있는 비교 증명들로 전체 등식의 증명을 만드는 용법이다.

*보기* 순서쌍이 같음을 보이려면 두 성분이 각각 같음을 보인다.

```savedLean
example (a b c d : Nat)
    (h1 : a = c)
    (h2 : b = d) :
    (a, b) = (c, d) := by
  have h : (a, b) = (c, d) := by
    ext with first second
    case first => exact h1
    case second => exact h2

  exact h

example (a b c d : Nat)
    (h1 : a = c)
    (h2 : b = d) :
    (a, b) = (c, d) := by
  ext at h1 h2 with h
  exact h
```

첫 증명의 `ext`는 두 성분의 등식을 각각 요구한다.
둘째 증명의 `ext at h1 h2 with h`는 같은 두 증명으로
`h : (a, b) = (c, d)`를 만들므로 앞의 `have` 블록에 해당한다.

대상에 따라 비교 조건은 다음과 같다.

:::table +header (align := left)
*
  * 전체 등식
  * 필요한 비교
  * 목표에서의 명령
*
  * `f = g`
  * 임의의 `x`에서 `f x = g x`
  * `ext x`
*
  * `S = T`
  * 임의의 `x`에서 `x ∈ S ↔ x ∈ T`
  * `ext x`
*
  * `(a, b) = (c, d)`
  * `a = c`와 `b = d`
  * `ext`
*
  * `s = t`, `s t : Elem S`
  * `s.val = t.val`
  * `ext`
*
  * `i = j`, `i j : Fin n`
  * `i.val = j.val`
  * `ext`
*
  * `parityClass a = parityClass b`
  * 대표원 사이의 합동 관계 `a ≡ b [ZMOD 2]`
  * `ext`
*
  * `cardinal A = cardinal B`
  * `SameCardinality A B`
  * `ext`
:::

함수와 집합에서는 외연성을 사용하고,
몫타입에서는 부분타입에 담긴 동치류의 등식과 대표원 사이의 관계를 연결한다.
증명한 비교 정리가 교재 전술에 연결되어 있으므로 같은 명령으로 사용할 수 있다.
몫의 용법은 대표원이 드러난 원소에 적용한다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x, f x = g x) :
    f = g := by
  ext x
  exact h x

example (A : Type) (S T : Ample.Set A)
    (h : ∀ x, x ∈ S ↔ x ∈ T) :
    S = T := by
  ext x
  exact h x

example (A : Type) (S : Ample.Set A)
    (s t : Ample.Elem S)
    (h : s.val = t.val) :
    s = t := by
  ext
  exact h

example
    (n : Nat)
    (i j : Fin n)
    (h : i.val = j.val) :
    i = j := by
  ext
  exact h

example
    (a b : Int)
    (h : Ample.Congruent 2 a b) :
    Ample.parityClass a = Ample.parityClass b := by
  ext
  exact h

example
    (A B : Type)
    (h : Ample.SameCardinality A B) :
    Ample.cardinal A = Ample.cardinal B := by
  ext
  exact h
```

#### 비교의 깊이
%%%
tag := "tactic-equality-strategy"
file := "equality-strategy"
%%%

`ext`는 기본적으로 비교 규칙을 한 번 적용한다.
예를 들어 `(s, s) = (t, t)`에서 `s t : Fin n`이면
순서쌍을 비교하여 두 목표 `s = t`를 남기고 각 번호의 값까지 비교하지는 않는다.

```savedLean
example
    (n : Nat) (s t : Fin n)
    (h : s = t) :
    (s, s) = (t, t) := by
  ext
  · exact h
  · exact h

example
    (n : Nat) (s t : Fin n)
    (h : s.val = t.val) :
    (s, s) = (t, t) := by
  ext : 2 with first second
  case first => exact h
  case second => exact h
```

둘째 예제의 `ext : 2`는 순서쌍과 각 번호를 차례로 비교하여
두 목표 `s.val = t.val`을 남긴다.
`ext!`로 비교를 반복해도 이 예제에서는 같은 목표를 얻는다.
`ext : 1`은 기본형 `ext`와 같으며,
`indisc : 2 at h`와 `congr : 2`도 같은 깊이 표기를 사용한다.
깊이는 각 비교 경로에서 적용할 규칙 수를 제한한다.
두 성분을 동시에 비교했다고 깊이를 두 번 사용한 것은 아니다.

집합에서는 `funext`와 `propext`를 조합해 증명한 `set_ext`를 하나의 비교 규칙으로 사용한다.
따라서 집합의 등식에서 모든 원소 조건의 동치로 바꾸는 것이 비교 한 번에 해당한다.
변수를 도입하거나 직접 만든 원소의 성분을 계산하는 과정은 비교 깊이에 더하지 않는다.

`funext x`는 함수값의 등식으로 함수의 등식을 증명하는 원리를 직접 사용하는 전술이다.
명제의 동치로 명제의 등식을 얻는 원리는 `propext`이다.
이 두 원리를 처음 설명한 뒤에는 집합과 함수의 비교에 `ext`를 공통으로 사용한다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x, f x = g x) :
    f = g := by
  funext x
  exact h x

example
    (P Q : Prop)
    (h : P ↔ Q) :
    P = Q := by
  apply propext
  exact h
```

대상의 정의를 계산할 때는 `expand`를,
이미 주어진 등식에 따라 식을 바꿀 때는 `rw`를 사용한다.
이 명령들은 대상의 비교 조건을 새로 요구하는 `ext`와 역할이 다르다.

### 비교 조건의 도출: indisc
%%%
tag := "tactic-indisc"
file := "indisc"
%%%

`indisc`은 전체 등식으로부터 비교 조건을 얻는 규칙을 사용한다.
`indisc at h`는 가정 `h`의 등식에서 함수값이나 성분의 비교를 한 겹 꺼낸다.
`with`를 사용하면 원래 등식을 유지하며 비교의 증명에 새 이름을 붙이고,
생략하면 새 증명이 원래 가정을 대신한다.
목표에 `indisc`를 사용하면 그 비교에 충분한 전체 등식을 새 목표로 삼는다.

#### 함수와 집합
%%%
tag := "tactic-indisc-functions"
file := "indisc-functions"
%%%

목표 `f x = g x`는 두 함수가 같음을 보이면 성립한다.
`indisc`은 이 추론에 따라 `f = g`를 새 목표로 삼는다.
가정 `h : f = g`로 함수값의 등식만 증명하려면 `rw [h]`로 바로 마칠 수도 있다.

```savedLean
example (A B : Type)
    (f g : A → B) (x : A)
    (h : f = g) :
    f x = g x := by
  indisc
  exact h

example (A B : Type)
    (f g : A → B) (x : A)
    (h : f = g) :
    f x = g x := by
  indisc x at h with valueEquality
  exact valueEquality
```

둘째 예제에서는 `h : f = g`를 유지하고 `valueEquality : f x = g x`를 얻는다.
`x`는 함수에 넣을 원소이고 `at h`는 사용할 등식 가정이다.
`indisc at h`처럼 원소를 지정하지 않으면 `∀ x, f x = g x`를 얻는다.

함수 전체의 등식을 얻으려면 모든 원소에서 함수값이 같아야 한다.
따라서 `ext at`에 사용하는 비교 가정은 원소 하나에서의 등식이 아니라 다음과 같은 전칭명제이다.

```savedLean
example (A B : Type)
    (f g : A → B)
    (h : ∀ x, f x = g x) :
    f = g := by
  ext at h with equality
  exact equality
```

집합에서도 전체 등식으로 각 원소 조건의 동치를 얻을 수 있다.
다음 증명에서 `hmem`의 타입은 `x ∈ S ↔ x ∈ T`이다.

```savedLean
example (A : Type)
    (S T : Ample.Set A)
    (x : A)
    (h : S = T)
    (hx : x ∈ S) :
    x ∈ T := by
  indisc x at h with hmem
  apply hmem.mp
  exact hx
```

`hmem.mp`로 목표 `x ∈ T`에 필요한 `x ∈ S`를 요구하고 `hx`로 증명을 마친다.

#### 성분과 원소 값
%%%
tag := "tactic-indisc-components"
file := "indisc-components"
%%%

순서쌍의 등식은 두 성분의 등식을 제공한다.
`with ha hb`는 이 두 증명에 각각 이름을 붙이며 원래 등식 `h`도 유지한다.

```savedLean
example
    (a b c d : Nat)
    (h : (a, b) = (c, d)) :
    a + b = c + d := by
  indisc at h with ha hb
  rw [ha, hb]

example
    (n : Nat) (i j : Fin n)
    (h : i = j) :
    i.val + 1 = j.val + 1 := by
  indisc at h
  rw [h]
```

첫 예제에서는 `ha : a = c`와 `hb : b = d`를 대입한다.
둘째 예제에서는 `indisc at h`가 가정의 이름을 유지하며 `h : i.val = j.val`를 얻는다.
부분타입에서도 원소의 등식으로 그 값의 등식을 얻는다.

`indisc at h`는 성분 자체의 등식까지 얻는다.
성분이 다시 순서쌍이나 `Fin`의 원소라면 새 등식에 `indisc`를 한 번 더 사용할 수 있다.
`indisc : 2 at h`는 두 겹을 비교하고, `indisc! at h`는 비교를 반복하며 원래 등식과 중간 결과도 남긴다.
`indisc at *`는 현재 가정들에 각각 한 겹의 비교를 적용하며 반복형은 `indisc! at *`이다.
반복 비교에서 `with`로 이름을 붙이면 마지막 비교 결과의 순서대로 이름을 적는다.

#### 몫의 관계
%%%
tag := "tactic-indisc-quotients"
file := "indisc-quotients"
%%%

대표원으로 만든 몫 원소들의 등식에서는 그 대표원 사이의 동치관계를 얻는다.
짝수·홀수의 동치류에서는 아래처럼 법 `2`에 대한 합동 관계를 얻는다.

```savedLean
example (a b : Int)
    (h : Ample.parityClass a = Ample.parityClass b) :
    Ample.Congruent 2 a b := by
  indisc at h with congruence
  exact congruence

example
    (a b : Int)
    (h : Ample.Congruent 2 a b) :
    Ample.parityClass a = Ample.parityClass b := by
  ext at h with equality :
      Ample.parityClass a = Ample.parityClass b
  exact equality
```

첫 명령은 `parityClass_eq_iff`의 정방향으로 관계를 얻고,
둘째 명령은 그 역방향으로 몫 원소의 등식을 얻는다.
합동 관계만으로는 어떤 이름의 몫 원소를 사용할지 정해지지 않으므로
둘째 예제에서는 결과의 등식을 명시한다.

목표가 합동 관계일 때도 `indisc (Ample.parityClass a = Ample.parityClass b)`로
그 관계에 충분한 몫의 등식을 새 목표로 삼을 수 있다.
함수의 비교와 달리 여기서 비교하는 것은 대표원 사이의 관계이다.

### 확장 용법: 여러 목표의 결합
%%%
tag := "tactic-combine-goals"
file := "combine-goals"
%%%

두 목표 `P`와 `Q`를 논리곱으로 묶을 때는 `unpack goals`를 사용하고,
두 성분의 등식을 전체 등식으로 묶을 때는 `indisc goals`를 사용한다.

```savedLean
example (a b c d : Nat)
    (h : (a, c) = (b, d)) :
    a = b ∧ c = d := by
  constructor with first second
  indisc goals first second with pair
  exact h
```

`indisc` 이후의 목표는 `(a, c) = (b, d)`이다.
이 등식의 두 성분을 비교하면 원래의 두 목표 `a = b`와 `c = d`를 얻으므로
가정 `h`로 새 목표를 증명하면 처음의 논리곱도 증명된다.
새 목표의 이름 `pair`를 사용하려면 `case pair => ...`로 시작할 수 있다.

목표 결합은 같은 가정 아래의 독립적인 목표에 적용한다.
서로 다른 경우의 가정을 갖거나 아직 정하지 않은 값에 의존하는 목표는 함께 묶지 않는다.
선택하지 않은 목표는 그대로 남으며,
변환을 정당화하는 증명을 만들지 못하면 목표도 바뀌지 않는다.

`unpack goals first second`의 기본 결과는 두 명제의 논리곱이며,
두 목표가 자료형의 원소를 요구하면 그 두 타입의 곱을 결과 타입으로 삼는다.
다른 구조로 묶으려면 명령 끝에 `: 결과 타입`을 적는다.
`unpack goals`는 한 단계의 필드를 비교하고 `rcases goals`는 중첩된 묶음도 분해한다.
이 용법은 생성자가 하나인 구조에서 필요한 필드를 꺼낼 수 있는 경우를 지원한다.
논리합의 서로 다른 분기는 동시에 주어진 성분처럼 묶지 않는다.

# 확장 용법의 공통 문법
%%%
tag := "tactic-rule-structure"
file := "rule-structure"
%%%

앞의 예제에서 배운 전술을 목표와 가정에 사용하는 방향을 함께 정리하자.
가정에는 주어진 대상이나 증명을 두고 목표에는 구성하거나 증명할 것을 적는다.
`r : P → Q`를 가정에 적용하면 `P`의 증명으로 `Q`의 증명을 얻고,
목표에 적용하면 `Q`를 얻는 데 필요한 `P`를 새 목표로 삼는다.

`apply`, `constructor`, `unpack`, `ext`와 `indisc`의 두 용법도 이 기준으로 구분한다.
아래 표에서 목표의 화살표는 증명해야 할 명제가 바뀌는 방향이고,
가정의 화살표는 주어진 증명으로 새 증명을 얻는 방향이다.

:::table +header (align := left)
*
  * 규칙
  * 목표에서의 사용
  * 가정에서의 사용
*
  * 함의의 적용
  * `apply r`: 결론 `Q` → 전제 `P`
  * `apply r at hP`: `P`의 증명 → `Q`의 증명
*
  * 논리곱의 구성
  * `constructor`: `P ∧ Q` → 두 목표 `P`, `Q`
  * `constructor at hP hQ`: 두 증명 → `P ∧ Q`의 증명
*
  * 논리곱의 분해
  * `unpack goals first second`: 두 목표 → `P ∧ Q`
  * `unpack h`: `P ∧ Q`의 증명 → 두 증명
*
  * 등식의 판정
  * `ext`: 전체 등식 → 비교 조건
  * `ext at h1 h2`: 비교 조건의 증명 → 전체 등식
*
  * 등식에서의 비교
  * `indisc`: 비교 조건 → 전체 등식
  * `indisc at h`: 전체 등식 → 비교 조건의 증명
:::

`rw`, `change`, `dsimp`와 `expand`는 표현을 바꾸는 명령이다.
이 명령들은 목표에서도 가정에서도 같은 방향으로 표현을 바꾸며,
`rw [← h]`처럼 방향을 지정하면 그 지정도 양쪽에 똑같이 적용된다.

변환을 마친 뒤에는 남은 등식의 양변이 정의상 같은지 확인하여
반사성으로 증명할 수 있는 목표를 자동으로 마친다.
`at h`는 표현을 바꿀 가정을 지정하며 이 종료 검사는 같은 단계의 현재 목표에도 적용된다.
기존에 대기하던 다른 분기의 목표에는 적용하지 않는다.
자동 검사는 미정인 원소의 값을 새로 선택하지 않으므로
원소 선택에 따라 달라지는 조건은 독자가 증명할 목표로 남는다.


## 항목의 선택과 명명
%%%
tag := "tactic-select-items"
file := "select-items"
%%%

`apply`, `constructor`, `ext`와 `indisc`에서는 `at` 뒤에 사용할 가정을 적는다.
`unpack h`, `cases h`, `rcases h`에서는 인수 `h`가 사용할 가정을 가리킨다.
목표 여러 개를 선택할 때는 `goals` 뒤에 그 이름을 적는다.
`with` 뒤에는 새 증명이나 목표의 이름을 적으며,
목표에 붙인 이름은 `case`로 선택한다.
`apply`에서는 Lean이 만든 목표의 순서대로 이름을 붙이며,
`with`를 적는다고 목표의 순서가 바뀌지는 않는다.

```savedLean
example
    (P Q R : Prop)
    (r : P → Q → R)
    (hp : P)
    (hq : Q) :
    R := by
  apply r with first second
  case first => exact hp
  case second => exact hq
```

`r`는 두 전제를 차례로 받으므로 `with first second`가 두 목표를 각각 명명한다.
전제가 논리곱 하나이면 그 한 전제를 분해하는 패턴을 적는다.

```savedLean
example
    (P Q R : Prop)
    (r : (P ∧ Q) → R)
    (hp : P)
    (hq : Q) :
    R := by
  apply r with ⟨first, second⟩
  case first => exact hp
  case second => exact hq
```

두 증명 모두 `P`와 `Q`를 보이지만 정리의 인수 구조는 다르다.
나란한 이름은 독립된 두 전제의 이름이고,
`⟨first, second⟩`는 전제 하나의 내부를 분해하는 패턴이다.
`unpack h with ⟨hp, hq⟩`는 가정 하나의 곱 구조에서 꺼낼 성분의 이름을 지정한다.
`rcases h with ⟨hp, ⟨hq, hr⟩⟩`는 중첩된 묶음까지 분해하는 패턴이다.
나란한 인수의 목록과 곱 구조 하나를 나타내는 꺾쇠괄호를 구별하여 읽으라.

다른 전제를 증명하면서 값이 정해질 수 있는 인수는 뒤로 미룬다.
예를 들어 다음 증명에서 `apply Exists.intro`는
원소를 고르는 `Nat` 목표보다 그 원소의 조건인 `?value = 7`을 먼저 제시한다.

```savedLean
example :
    ∃ n : Nat, n = 7 := by
  apply Exists.intro with certificate value
  case certificate => rfl
```

`certificate`는 `?value = 7`, `value`는 `Nat` 목표의 이름이다.
명시적으로 쓴 `rfl`이 첫 등식을 증명하면서 원소도 `7`로 정하므로 두 목표가 모두 해결된다.
어떤 목표가 해결되어 사라져도 남은 목표에 붙인 이름은 바뀌지 않는다.

# 실패 사례와 수정
%%%
tag := "tactic-failures"
file := "failures"
%%%


전술이 실패하면 현재 가정과 목표의 형태를 먼저 확인하라.
아래의 실패 예제는 오류를 확인하기 위한 코드이며 완성된 증명이 아니다.
각 예제 뒤에는 같은 상황에서 사용할 수 있는 증명을 제시한다.

## 논리합과 곱의 분해
%%%
tag := "tactic-failure-unpack"
file := "unpack"
%%%


`h : P ∨ Q`는 두 명제 중 어느 하나의 증명을 담는다.
따라서 논리곱처럼 두 성분을 동시에 꺼내려 하면 실패한다.

```lean +error -keep
theorem failure_unpack_or (P Q : Prop)
    (h : P ∨ Q) :
    Q ∨ P := by
  unpack h with ⟨hP, hQ⟩
```

이때 오류는 서로 다른 생성자가 경우를 나타낸다는 점을 알린다.
`cases h`로 두 경우를 나누면 각 경우에 주어진 증명으로 결론을 얻는다.

```savedLean
example (P Q : Prop)
    (h : P ∨ Q) :
    Q ∨ P := by
  cases h with
  | inl hP =>
      right
      exact hP

  | inr hQ =>
      left
      exact hQ
```

## 함수의 한 값과 전체 등식
%%%
tag := "tactic-failure-ext"
file := "function-equality"
%%%


한 원소에서 함수값이 같다는 사실만으로 두 함수가 같음을 얻을 수는 없다.
`ext at h`로 전체 등식을 만들려면 모든 원소에서의 비교가 필요하다.

```lean +error -keep
theorem failure_one_value (f g : Nat → Nat)
    (h : f 0 = g 0) :
    f = g := by
  ext at h : f = g
```

다음 증명에서는 `h`의 명제가 전칭명제이므로 함수의 전체 등식을 얻는다.

```savedLean
example (f g : Nat → Nat)
    (h : ∀ x, f x = g x) :
    f = g := by
  ext at h
  exact h
```

## 서로 다른 가정 아래의 목표
%%%
tag := "tactic-failure-context"
file := "contexts"
%%%


목표를 나눈 뒤 한 목표에서 `intro`로 가정을 도입하면 두 목표는 서로 다른 가정을 갖는다.
이 교재의 목표 결합은 이 상태를 그대로 묶는 용법을 지원하지 않는다.

```lean +error -keep
theorem failure_contexts (P Q : Prop)
    (h : P ∧ Q) :
    (True → P) ∧ (True → Q) := by
  constructor with first second
  intro ht
  unpack goals first second
```

이때는 분기별 가정을 도입하기 전에 함의 자체를 묶거나 각 목표를 따로 증명한다.
다음은 두 목표를 따로 증명한 것이다.

```savedLean
example (P Q : Prop)
    (h : P ∧ Q) :
    (True → P) ∧ (True → Q) := by
  unpack h with ⟨hP, hQ⟩
  constructor
  · intro ht
    exact hP

  · intro ht
    exact hQ
```

서로 다른 가정을 함의로 옮기는 등 별도의 논증을 하면 더 일반적인 결합도 가능하다.
현재 명령은 같은 문맥의 독립적인 목표를 묶는 범위로 제한한다.
원소 선택에 의존하는 목표라면 먼저 원소를 정한 뒤 남은 목표를 확인하라.

## 결과 타입의 지정
%%%
tag := "tactic-failure-result"
file := "result-types"
%%%


`left at hP with h`를 쓰면 `hP : P`로 논리합의 왼쪽을 구성한다.
오른쪽 명제를 현재 목표나 후속 추론에서 정할 수 없으면 `alternative`라는 목표가 남는다.
이는 명제의 증명이 아니라 아직 정하지 않은 명제 자체를 요구한다.
원하는 논리합을 알고 있다면 다음과 같이 결과를 명시하라.

```savedLean
example (P Q : Prop)
    (hP : P) :
    True := by
  left at hP with h : P ∨ Q
  trivial
```

`ext at h1 h2 with h : p = q`처럼 전체 등식을 명시하는 방법도 같은 역할을 한다.
명시한 결과와 가정의 타입이 맞지 않으면 가정과 목표를 바꾸지 않고 실패한다.

# 계산과 자동화
%%%
tag := "tactic-domain-automation"
file := "automation"
%%%

자동 표현 정리는 목표와 가정의 표기를 정해진 규칙에 따라 바꾸고,
`decide`·`arith`·`card`는 각각의 범위에서 현재 목표의 증명을 찾는다.
이 둘의 역할을 구별한 뒤 각 명령이 사용하는 사실과 적용 범위를 확인하자.
새 사실에 이름을 붙일 때는 `have h : 명제 := by` 아래에서 계산 전술을 사용한다.

## 자동화의 범위와 추론 확인
%%%
tag := "tactic-automation-tracing"
file := "tracing"
%%%


자동화가 실패하면 필요한 가정이 빠졌거나 등록된 규칙과 탐색 범위로 결론을 연결하지 못했을 수 있다.
예를 들어 나눗셈에서는 분모의 부호와 영이 아닌 조건을 확인하라.
실패 자체로 목표의 부정을 얻는 것은 아니다.

:::table +header (align := left)
*
  * 명령
  * 사용하는 지식
  * 직접 제시할 논증
*
  * `arith`
  * 자연수·정수의 산술과 등록된 곱·몫·나머지·약수 규칙
  * 귀납법, 수학적 경우 구분, 증인의 선택
*
  * `card`
  * 이미 증명한 크기 관계와 유한성·무한성 정리
  * 새로운 단사·전단사의 구성
:::

필요할 때 `set_option trace.Ample.arith true in`을 선언 앞에 적으면
완성된 산술 증명에 사용된 등록 정리와 그 조건, 사용한 가정을 확인할 수 있다.
`trace.Ample.card`도 같은 방식으로 켠다.
다음 옵션은 바로 뒤의 정리에서만 적용된다.

```savedLean
set_option trace.Ample.arith true in
example (a m : Nat)
    (h : a < m) :
    a % m = a := by
  arith
```

출력의 `Rule`은 완성된 증명에 들어 있는 등록 정리이고 `condition`은 그 적용에 사용한 조건이다.
`Hypothesis`는 증명에서 사용한 현재 가정이다.
정리 적용 대신 계산 엔진이 처리한 경우에는 `Method`로 계산 방법을 표시한다.
실패한 탐색 후보는 성공 이유로 출력하지 않으며 계산 엔진 내부의 모든 단계를 설명하는 기능은 아니다.

## 교재 관례와 Lean의 용법
%%%
tag := "tactic-ample-conventions"
file := "conventions"
%%%


함의의 도입과 적용, 정의에 따른 계산은 Lean의 기본 증명 원리를 그대로 사용한다.
교재에서는 반복되는 비교와 전향 추론에 일정한 인터페이스를 제공한다.

:::table +header (align := left)
*
  * 교재의 관례
  * 확인할 점
*
  * `ext`, `indisc`
  * 기본형은 한 겹을 비교한다. `ext!`, `indisc!`는 비교를 반복하며 `ext : 2`, `indisc : 2 at h`로 깊이를 지정한다.
*
  * `congr`
  * 기본형은 공통 함수의 인수를 반복하여 비교한다. `congr : 2`로 깊이를 제한한다.
*
  * `expand`
  * 필요한 교재 정의 한 층을 펼쳐 계산하고 `expand!`는 펼치기를 반복한다. 정의를 지정할 때는 `dsimp [정의]`도 사용할 수 있다.
*
  * 변환 뒤의 종료
  * 같은 단계에서 남긴 반사적 등식을 자동으로 마친다. 미정인 원소를 선택하거나 다른 대기 목표를 처리하지 않는다.
*
  * `at`, `goals`, `with`
  * 기존 가정, 기존 목표, 새 이름과 패턴을 각각 지정한다. 적용 가능한 형태는 이 부록의 해당 용법에서 확인한다.
*
  * 설정
  * 교재 전술은 `open Ample`, 자동 표현 정리는 `open scoped Ample.Auto`로 사용한다.
:::

다른 Lean 문서를 읽을 때는 그 문서가 가져오는 모듈과 설정도 확인하라.
교재 전술의 확장은 기본 논리 정리를 사용하여 증명항을 만들며 Lean이 그 증명을 검사한다.

## 자동 표현 정리
%%%
tag := "tactic-auto-normalization"
file := "auto-normalization"
%%%

풀이 파일 맨 위에 `import AlgebraBook.Tactic.Auto`를 추가하고
아래 선언을 한 번 적으면 보통의 `by` 증명에서 표현 정리가 자동으로 이루어진다.
증명 시작과 전술의 각 단계 전후에 목표와 가정을 정리하므로
새로 도입한 원소 조건에도 같은 규칙이 적용된다.

```savedLean -show
namespace AutoExamples
open Ample
```

```savedLean
open scoped Ample.Auto
```

자동으로 정리하는 표현은 다음과 같다.

- `fun`으로 직접 적은 술어의 원소 조건
- 함수 안에서 `let`으로 정의한 함수의 값과 순서쌍의 성분
- 직접 구성한 부분타입과 `Fin` 원소들의 등식에 관한 가정
- 자연수와 정수에서 부등식의 부정
- 고전논리를 사용하는 범위에서 명제의 이중 부정

일반적인 원소 표기 `x ∈ S`는 그대로 유지한다.
집합 `S`의 정의를 드러내려면 `expand`, `dsimp` 등을 명시적으로 사용하며
`x ∈ (fun n => 2 ≤ n)`처럼 술어를 직접 적은 경우에는 함수 적용을 계산하여 `2 ≤ x`로 정리한다.

예를 들어 정수에 관한 가정 `h : ¬ a < 0`은 `h : 0 ≤ a`로 정리된다.
따라서 다음 증명에서 `exact h` 직전의 가정은 이미 목표와 같다.

```savedLean
example
    (a : Int)
    (h : ¬ a < 0) :
    0 ≤ a := by
  exact h
```

`open scoped Classical`을 선언한 범위에서는
목표와 가정의 `¬¬ P`도 `P`로 정리된다.
이 부록에서도 같은 선언을 사용하므로 아래 증명이 시작되면 가정은 `h : P`이다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  exact h
```

`by_cases`나 `by_contra`로 논증을 시작한 뒤에도 해당 목표와 그 하위 목표에서
같은 규칙을 사용하며 새로 도입한 가정에도 이중 부정 제거를 적용한다.
고전논리를 지정하기 전에는 `¬¬ P`를 그대로 유지하므로
{ref "sets-classical-logic"}[이중 여집합과 고전논리]에서 살펴본 추론 단계를 직접 적을 수 있다.

자동 정리는 등록된 표현 변환과 계산을 수행한다.
직접 구성한 원소들의 등식을 정리할 때는 원래 등식을 유지하고 값의 등식을 추가한다.
함의의 가정을 도입하거나 두 방향을 증명하는 단계에는
앞에서 배운 `intro`, `constructor` 등을 사용하고
원소나 성분의 등식을 비교하는 단계에는 `ext`를 사용한다.

특정 증명에서 원래 표기를 확인하려면
그 선언 앞에 `set_option ample.autoNormalize false in`을 적을 수 있다.

```savedLean -show
end AutoExamples
```

## 명제의 판정
%%%
tag := "tactic-functions-and-computation"
file := "functions-and-computation"
%%%

`decide`는 계산으로 참·거짓을 판정할 수 있는 명제를 증명한다.
예를 들어 `3 < 5`는 두 수가 정해져 있으므로 계산하여 확인할 수 있다.

```savedLean
example : 3 < 5 := by
  decide
```

임의의 자연수 `x`에 관한 `2 ≤ x + 2`를 보일 때는
변수의 값을 계산하는 대신 자연수의 성질을 사용해야 한다.
이러한 산술은 {ref "tactic-arith"}[`arith`]로 확인할 수 있다.
`decide`와 정의에 따른 계산을 사용하는 `rfl`은
각각 명제의 판정과 등식의 확인이라는 역할로 구별한다.



## 산술 계산
%%%
tag := "tactic-arith"
file := "arithmetic"
%%%

`arith`는 교재의 산술 전술로, 선형 산술과 다항식 등식에 더하여
자연수와 정수의 몫·나머지에 관한 정리들을 사용한다.
이 전술은 {ref "preliminaries-arith"}[자연수와 정수의 마지막 절]에서 처음 소개한다.
풀이 파일에서 `import AlgebraBook.Tactic.Arithmetic`와 `open Ample`를 사용하면 활성화된다.
자연수와 정수 이후의 교재 모듈은 이 전술을 포함한다.

`arith`가 계산에 사용하는 기본 지식은 자연수와 정수의 산술이다.
현재 처리하는 계산은 다음과 같다.

:::table +header (align := left)
*
  * 계산의 종류
  * 처리하는 내용
*
  * 선형 등식과 부등식
  * 덧셈·뺄셈·상수배가 들어 있는 조건의 확인과 모순 도출
*
  * 다항식 등식
  * 자연수와 정수의 결합법칙·교환법칙·분배법칙에 따른 등식의 확인
*
  * 곱의 부등식
  * 곱셈의 단조성과 부호 조건에 관한 등록된 정리의 적용
*
  * 몫과 나머지
  * 경계 조건, 몫·나머지의 재구성, 같은 나머지에서 얻는 연산의 관계
*
  * 나누어떨어짐
  * Lean의 기본 나누어떨어짐과 나머지가 $`0`이라는 조건의 연결
*
  * 산술 값을 가진 원소
  * 원소 조건에 나타난 산술식과 `Fin`의 값·경계 조건의 계산
:::

먼저 등록된 표현 정리 규칙으로 원소 표기와 지역 정의의 계산을 정리한다.
이어 가정으로 등식·부등식을 확인하고, 필요한 경우 목표에 맞는 산술 정리를 적용하여
그 정리의 전제도 같은 방법으로 증명한다.
성공하면 현재 목표의 증명이 완성되며 이렇게 얻은 증명도 Lean이 검사한다.

이 과정에서는 가정으로 주어진 사실의 사용과 등식의 대입 같은 공통 추론도 수행한다.
예를 들어 `h : x = y`가 주어졌다면 $`f(x)=f(y)`도 확인할 수 있다.
군의 연산 법칙처럼 다른 구조에서 가져와야 하는 성질은 산술 규칙에 포함하지 않는다.
직접 정의한 조건의 계산이 필요하면 `expand`로 정의를 펼친 뒤 `arith`를 사용할 수 있다.

본문에서는 존재명제의 원소 선택을 `exists`로, 함수·집합의 외연성 비교를 `ext`로 명시한다.
부분타입과 `Fin`의 원소는 필드 이름을 적어 구성한다.
변수의 곱이 들어간 복잡한 부등식이나 등록된 정리만으로 연결되지 않는 계산에서는
중간 등식이나 부등식을 직접 제시해야 할 수 있다.

자연수 $`n`에 대해서도 $`2n\ne5`이다.

```savedLean
example
    (n : Nat) :
    2 * n ≠ 5 := by
  arith
```

분배법칙과 교환법칙을 사용하는 등식은 다음과 같이 계산할 수 있다.
`calc`에 적은 등식마다 `by arith`로 그 계산을 확인한다.

```savedLean
example
    (m k : Nat) :
    m * (1 + k) = m + k * m := by
  calc
    m * (1 + k) = m * 1 + m * k := by arith
    _ = m + k * m := by arith
```

자연수의 뺄셈이 들어간 식에서는 필요한 경계 조건도 가정에 두어야 한다.
아래에서는 `1 ≤ n`에 따라 `(n - 1) + 1 = n`이 성립하므로
이를 분배법칙과 함께 사용하여 등식을 확인한다.

```savedLean
example
    (m n : Nat)
    (hn : 1 ≤ n) :
    m * n = m + (n - 1) * m := by
  arith
```

`arith`는 교재에 모아 둔 산술 정리에서 목표에 맞는 정리를 선택한 뒤
그 정리에 필요한 조건도 산술 계산으로 확인한다.
`Fin`의 원소가 만족하는 경계 조건은 이 과정에서 함께 사용한다.

예를 들어 `i : Fin m`과 `j : Fin n`이면 각각 $`i < m`과 $`j < n`이므로
$`i + jm < (j + 1)m ≤ nm = mn`이다.
이를 이용하면 두 번호를 하나로 조합한 $`i + jm`의 범위와 몫을 확인할 수 있다.

```savedLean
example
    (m n : Nat) (i : Fin m) (j : Fin n) :
    i.val + j.val * m < m * n := by
  arith

example
    (m n : Nat) (i : Fin m) (j : Fin n) :
    (i.val + j.val * m) / m = j.val := by
  arith
```

자연수의 나눗셈에서는 모든 자연수 $`n`에 대하여 $`3/n\leq3`이다.
정수의 나눗셈에서도 $`3/n\leq3`이 성립한다. Lean은 $`0`으로 나눈 몫을 $`0`으로 정하므로 두 예제 모두 나누는 수에 별도 조건이 필요하지 않다.
나누는 수가 변수인 경우에는 몫의 경계에 관한 정리를 사용하여 확인한다.

```savedLean
example (n : Nat) : 3 / n ≤ 3 := by
  arith

example (n : Int) : 3 / n ≤ 3 := by
  arith

example
    (n m : Nat)
    (h : n * m = 3)
    (hn : n ≠ 0)
    (hm : 3 < m) :
    False := by
  arith
```

셋째 예제에서는 $`n\geq1`이므로 $`m\leq nm=3`을 얻으며
이 결론이 가정 $`3<m`과 모순이다.
이처럼 `arith`는 이미 등장한 곱과 몫에 관한 성질을 가정에서 사용하며
새 조건을 제시하는 `suffices`의 연결에서도 같은 정리를 사용한다.

몫과 나머지가 모두 같으면 원래 수도 같다.
이 성질과 나머지의 경계 조건, 몫·나머지의 재구성에 필요한 정리도 연결되어 있다.

```savedLean
example (x y m : Nat)
    (h : x % m = y % m ∧ x / m = y / m) :
    x = y := by
  arith
```

정수의 합과 차, 곱에 나머지를 취하는 계산에도 같은 전술을 사용할 수 있다.
아래에서는 두 쌍의 정수가 각각 같은 나머지를 가지므로 그 곱도 같은 나머지를 갖는다.

```savedLean
example (a b c d n : Int)
    (ha : a % n = b % n)
    (hc : c % n = d % n) :
    (a * c) % n = (b * d) % n := by
  arith
```

자연수의 거듭제곱과 정수의 부호를 바꾼 나머지,
나누어떨어짐과 나머지가 $`0`이라는 조건의 연결도 지원한다.
자연수의 뺄셈은 결과가 음수가 되면 $`0`이 되므로
정수의 차에 적용하는 나머지 법칙을 그대로 사용할 수 없다.

### 원소 조건과 산술
%%%
tag := "tactic-membership-arithmetic"
file := "membership-arithmetic"
%%%

부분타입의 원소를 만들거나 그 값으로 계산할 때에는 집합의 원소 조건과 부등식을 함께 사용한다.
`arith`는 목표와 가정의 원소 표기를 조건으로 정리한 뒤 산술 계산을 수행한다.

```savedLean
def tactic_element_from_three (n : Nat) :
    Ample.Elem (fun k : Nat => 3 ≤ k) :=
  { val := n + 3, property := by arith }
example
    (s : Ample.Elem (fun n : Nat => 2 ≤ n)) :
    s.val - 2 + 2 = s.val := by
  have hy :=
    s.property
  arith
```

첫 예제에서는 값 $`n+3`과 조건 $`3\leq n+3`의 증명을 함께 담는다.
둘째 증명에서는 `s.property`의 원소 조건을 $`2\leq s.val`로 정리하여
자연수의 뺄셈에서 $`(s.val-2)+2=s.val`임을 확인한다.

### 부등식의 부정
%%%
tag := "tactic-order-negation"
file := "order-negation"
%%%

정수에서 $`\neg(a<b)`는 $`b\leq a`와 동치이고
$`\neg(a\leq b)`는 $`b<a`와 동치이다.
자연수에서도 같은 관계가 성립하며 `arith`는 이러한 가정으로 부등식을 확인할 수 있다.

```savedLean
example
    (a : Int)
    (h : ¬ a < 0) :
    0 ≤ a := by
  arith

example
    (a : Int)
    (h : ¬ 0 ≤ a) :
    a < 0 := by
  arith
```

`a ≥ 0`은 `0 ≤ a`와 같은 표기이며 증명 화면에서는 보통 후자로 표시된다.

## 집합의 크기
%%%
tag := "tactic-card"
file := "cardinality"
%%%

`card`는 {ref "cardinality-card-tactic"}[크기 비교의 자동화]에서 소개한 전술이다.
현재 가정과 집합의 크기 절에서 증명한 기본 정리로
기수의 등식과 부등식, 원소 수의 유일성과 유한성·무한성을 연결한다.
주어진 등식과 부등식을 먼저 이어 원소 수의 조건이나 다른 크기 관계에 사용한다.
`cardinal A = cardinal B`와 `SameCardinality A B` 사이의 전환에도 사용할 수 있다.

```savedLean
example (A B : Type) (n : Nat)
    (hAB : Ample.cardinal A = Ample.cardinal B)
    (hA : Ample.cardinal A = n) :
    Ample.cardinal B = n := by
  card
```

`AlgebraBook.Cardinality`를 가져오고 `open Ample`를 쓰면 이 전술과 등록한 기본 정리를 사용할 수 있다.
산술식의 계산은 `arith`로 확인하고
새로운 전단사가 필요하면 함수를 구성하여 직접 증명한다.

```savedLean
end TacticExamples
```
