import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Functions
import AlgebraBook.Tactic.Arithmetic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "자연수와 정수" =>

%%%
tag := "mathematical-preliminaries"
file := "preliminaries"
%%%

함수와 집합의 증명에 이어 자연수의 귀납법과 정수의 계산을 익히자.
짝수와 홀수가 서로 같을 수 없음을 귀납법으로 증명하고,
정수의 나누어떨어짐과 합동에서 등식을 사용하는 방법을 살펴본다.
기본 성질과 연습문제를 마친 뒤에는 반복되는 산술 계산을 `arith`에 맡긴다.

```savedImport
import AlgebraBook.Functions
import AlgebraBook.Tactic.Arithmetic
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

# 자연수와 귀납법
%%%
tag := "preliminaries-induction"
file := "induction"
%%%

앞에서 `rfl`로 $`2+3=5`와 같은 등식을 증명했다.
그렇다면 모든 자연수에 대해 성립하는 $`0+n=n`도 같은 방법으로 보일 수 있을까?
다음 증명은 `rfl`에서 실패한다.

```tryLean +error -keep
example (n : Nat) : 0 + n = n := by
  rfl
```

Lean의 자연수 덧셈은 두 번째 인수가 $`0`인지 어떤 수에 $`1`을 더한 값인지에 따라 계산된다.
임의의 자연수 `n`에 대해서는 어느 경우인지 정해져 있지 않으므로
정의를 계산하는 것만으로 `0 + n`을 `n`으로 바꿀 수 없다.
이 등식을 직접 증명하기 위해 자연수의 귀납법을 사용하자.

모든 자연수는 $`0`에서 시작하여 $`1`을 반복해서 더하면 얻을 수 있다.
이 성질을 이용하여 모든 자연수에 관한 명제를 증명하는 방법이 수학적 귀납법이다.

*수학적 귀납법* 모든 자연수 $`n`에 대하여 $`P(n)`을 보이려면 다음 두 단계를 증명하면 된다.

1. $`P(0)`이 성립한다.
2. 임의의 자연수 $`n`에 대하여 $`P(n)`을 가정하면 $`P(n+1)`이 성립한다.

두 번째 단계에서 가정하는 $`P(n)`을 *귀납 가정*이라고 한다.
Lean에서는 `induction n`으로 $`0`의 경우와 $`n+1`의 경우를 나누며
두 번째 경우에 귀납 가정을 사용할 수 있다.
`Nat.succ n`은 자연수 `n` 다음의 수, 곧 `n + 1`을 뜻한다.

*보기* 모든 자연수 $`n`에 대하여 $`0+n=n`임을 귀납법으로 증명하자.
먼저 $`n=0`이면 $`0+0=0`이다.
$`0+n=n`을 가정하면 $`0+(n+1)=(0+n)+1=n+1`이므로 다음 자연수에서도 등식이 성립한다.
이때 첫 등식은 두 번째 인수에 따라 계산하는 Lean의 자연수 덧셈 정의를 사용한다.
`Nat.add_succ`는 이 계산을 등식 `a + Nat.succ b = Nat.succ (a + b)`로 나타낸 정리이다.

```savedLean
theorem zero_add_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ]
      -- 목표: Nat.succ (0 + n) = Nat.succ n
      rw [ih]
```

`zero`는 $`n=0`인 경우이며 목표가 `0 + 0 = 0`이므로 `rfl`로 증명한다.
`succ n ih`에서는 귀납 가정에 `ih`라는 이름을 붙여 `ih : 0 + n = n`을 얻는다.
이때 목표 `0 + Nat.succ n = Nat.succ n`을 덧셈의 정의에 따라 펼치면
`Nat.succ (0 + n) = Nat.succ n`이 된다.
`rw [Nat.add_succ]`로 이 계산을 적용한 뒤 `rw [ih]`를 쓰면 양변이 같아져 증명이 끝난다.

# 짝수와 함수의 상
%%%
tag := "preliminaries-even-induction"
file := "parity"
%%%

*정의* $`n=2k`인 자연수 $`k`가 존재하면 자연수 $`n`을 *짝수*라고 한다.

```savedLean
def IsEvenNat : Nat → Prop :=
  fun n => ∃ k : Nat, n = 2 * k
```

$`5`가 짝수가 아님을 증명하려면 모든 자연수 $`m`에 대하여 $`2m\ne5`임을 보이면 된다.
그런데 $`m`에 대한 귀납법을 곧바로 사용하면 다음 단계에서 어려움이 생긴다.
$`2(m+1)=5`를 가정하여 얻은 등식은 $`2m=3`이므로
귀납 가정 $`2m\ne5`를 이 등식에 적용할 수 없다.
오른쪽의 수가 $`2`만큼 줄어든 경우에도 귀납 가정을 사용할 수 있도록
$`2m\ne2n+1`을 모든 자연수 $`n`에 대하여 함께 증명하자.

*정리* 모든 자연수 $`m`, $`n`에 대하여 $`2m\ne2n+1`이다.

*증명* $`m`에 대한 귀납법을 사용한다.
$`m=0`이면 왼쪽은 $`0`이고 오른쪽은 양수이므로 같을 수 없다.

이제 모든 자연수 $`n`에 대하여 $`2m\ne2n+1`이라고 가정하고
$`2(m+1)=2n+1`에서 모순을 얻자.
$`n=0`이면 $`2m+2=1`이므로 양변에서 $`1`을 빼서 양수 $`2m+1`이 $`0`과 같다는 모순을 얻는다.
$`n=r+1`이면 양변에서 $`2`를 빼서 $`2m=2r+1`을 얻으며 이는 귀납 가정에 어긋난다.

Lean에서 `Nat.succ.inj`는 `Nat.succ a = Nat.succ b`의 증명으로부터 `a = b`의 증명을 얻는 정리이다.
즉 양변에 더한 $`1`을 지우는 단계에 해당하며 두 번 사용하면 $`2`를 지울 수 있다.
아래의 `cases n`은 자연수를 $`0`과 다음 자연수의 두 경우로 나눈다.
`induction`과 달리 경우를 나누기만 하므로 새로운 귀납 가정은 생기지 않는다.

```savedLean
theorem even_ne_odd (m : Nat) :
    ∀ n : Nat, 2 * m ≠ 2 * n + 1 := by
  induction m with
  | zero =>
      intro n h
      -- 0과 다음 자연수가 같다는 가정에서 모순을 얻는다.
      expand at h
      contradiction

  | succ m ih =>
      intro n h
      -- 오른쪽의 n이 0인지 양수인지 나눈다.
      cases n with
      | zero =>
          expand at h

          -- 양변의 1을 소거하면 양수와 0이 같아진다.
          have hZero : Nat.succ (2 * m) = 0 := by
            exact Nat.succ.inj h

          contradiction

      | succ n =>
          expand at h

          -- 양변의 2를 소거하면 귀납 가정에 어긋나는 등식이 된다.
          apply ih n
          exact Nat.succ.inj (Nat.succ.inj h)
```

`∀ n`을 목표에 둔 채 `induction m`을 쓰면
귀납 가정은 `ih : ∀ n, 2 * m ≠ 2 * n + 1`이 된다.
각 경우의 `intro n h`는 자연수 `n`을 택하고 두 식이 같다는 가정을 도입한다.
`expand at h`는 가정 `h`에 들어 있는 정의를 펼치고 계산한다.
여기서는 자연수의 곱셈과 덧셈을 계산하여 양변에 더한 $`1`을 `Nat.succ`로 드러낸다.

$`m=0`인 경우에는 `0 = Nat.succ (2 * n)`에서 모순을 얻는다.
$`m+1`의 경우에는 `cases n`으로 다시 나누며,
$`n=0`이면 `Nat.succ.inj h`로 `Nat.succ (2 * m) = 0`을 얻는다.
이처럼 $`0`과 다음 자연수가 같다는 가정은 `contradiction`으로 처리할 수 있다.
마지막 `succ n`에서는 수학적 증명의 $`r`에 `n`이라는 이름을 붙인다.
`apply ih n`으로 목표를 `2 * m = 2 * n + 1`로 바꾼 뒤
`Nat.succ.inj`를 두 번 사용하여 `h`에서 이 등식을 얻는다.

*보기* $`5`는 짝수가 아니다.
짝수라고 가정하면 $`5=2k`인 자연수 $`k`가 존재한다.
그런데 앞의 정리에 $`m=k`, $`n=2`를 넣으면 $`2k\ne5`이므로 모순이다.

```savedLean
theorem five_not_even : ¬ IsEvenNat 5 := by
  intro h
  unpack h with ⟨k, hk⟩

  -- 2k = 5는 짝수와 홀수가 같을 수 없다는 정리에 어긋난다.
  apply even_ne_odd k 2
  exact hk.symm
```

`h : IsEvenNat 5`는 정의에 따라 `∃ k : Nat, 5 = 2 * k`의 증명이므로
`unpack`으로 자연수 `k`와 등식 `hk`를 얻는다.
`apply even_ne_odd k 2`로 모순을 보이는 데 필요한 등식 `2 * k = 5`를 목표로 삼고,
`hk`의 양변을 바꾼 증명 `hk.symm`을 제시한다.

## 함수의 상과 짝수
%%%
tag := "preliminaries-double-image"
%%%

이제 앞에서 미뤄 둔 $`5 \notin \operatorname{double}(\mathbb{N})`을 보이자.
`double n = 2 * n`이므로 모든 함수값이 짝수임을 먼저 확인하면 된다.

```savedLean
theorem double_is_even (n : Nat) :
    IsEvenNat (double n) := by
  exists n

theorem five_not_in_double_image :
    5 ∉ image double (whole Nat) := by
  intro hy
  rcases hy with ⟨n, hn, hEq⟩

  -- 5가 상에 속한다면 5가 짝수라는 결론을 얻는다.
  apply five_not_even
  have hEven : IsEvenNat (double n) := by
    exact double_is_even n

  rw [hEq] at hEven
  exact hEven
```

첫 증명에서는 `exists n`으로 짝수의 정의에 필요한 자연수를 택한다.
남은 등식 `double n = 2 * n`은 `double`의 정의에 따라 성립한다.

두 번째 증명에서는 `hy : 5 ∈ image double (whole Nat)`를 가정하고 모순을 보인다.
가정의 명제를 펼치면 `∃ n, n ∈ whole Nat ∧ double n = 5`이므로
`rcases`로 자연수 `n`과 등식 `hEq : double n = 5`를 얻는다.
앞의 정리 `five_not_even`은 `IsEvenNat 5 → False`의 증명이므로
`apply five_not_even`을 쓰면 목표가 `IsEvenNat 5`로 바뀐다.

이를 보이기 위해 `double_is_even n`으로 `hEven : IsEvenNat (double n)`을 얻은 뒤
`rw [hEq] at hEven`으로 가정 안의 `double n`을 `5`로 바꾼다.
이제 `hEven`이 바로 `IsEvenNat 5`의 증명이므로 `exact hEven`으로 증명을 마친다.

*보기* `double : Nat → Nat`는 전사함수가 아니다.
전사라면 $`5`도 함수값으로 나타나야 하지만 방금 증명한 결과에 어긋난다.

```savedLean
theorem double_not_surjective : ¬ Surjective double := by
  intro hf
  unpack hf 5 with ⟨n, hn⟩
  apply five_not_in_double_image
  exists n
```

`hf 5`는 `double n = 5`인 자연수 `n`이 존재한다는 증명이다.
여기서 얻은 `n`을 상의 원소 조건에 사용하면 $`5`가 `double`의 상에 속하여 모순이 생긴다.
함수 절의 `doubleToEvens_bijective`와 비교하면 공역의 역할을 볼 수 있다.
함수값은 똑같이 $`2n`이어도 공역을 자연수 전체로 정하면 전사가 아니고,
짝수의 집합으로 정하면 전단사이다.

# 정수와 나누어떨어짐
%%%
tag := "preliminaries-divisibility"
file := "divisibility"
%%%

이제 수의 범위를 정수로 넓혀 보자.
정수의 집합은 $`\mathbb{Z}`로 쓰며 Lean에서는 `Int`로 나타낸다.
정수끼리는 작은 수에서 큰 수를 빼도 그 결과를 정수로 나타낼 수 있다.
정수의 계산을 등식으로 이어 쓰는 방법을 익힌 뒤
앞에서 사용한 배수의 개념을 임의의 정수로 넓히자.

## 등식의 계산
%%%
tag := "preliminaries-calc"
%%%

정수의 식을 계산할 때는 덧셈과 곱셈의 법칙으로 여러 등식을 이어 쓴다.
예를 들어 $`(a+0)+b=a+b=b+a`는 $`a+0=a`라는 성질과 덧셈의 교환법칙을 차례로 사용한 계산이다.
Lean에서는 각각 `Int.add_zero`와 `Int.add_comm`으로 이 두 성질을 사용하며
등식을 이어 쓰는 표기 `calc`로 다음과 같이 적는다.
등식의 추이성에 따라 각 단계의 등식을 증명하면 처음 식과 마지막 식의 등식이 성립한다.

```savedLean
example
    (a b : Int) :
    (a + 0) + b = b + a := by
  calc
    (a + 0) + b = a + b := by rw [Int.add_zero]
    _ = b + a := by rw [Int.add_comm]
```

각 줄의 `:=` 왼쪽에는 등식을, 오른쪽에는 그 등식의 증명을 적는다.
첫 줄에서는 `Int.add_zero`로 `a + 0`을 `a`로 바꾸고
둘째 줄에서는 `Int.add_comm`으로 `a + b = b + a`를 보인다.
둘째 줄의 `_`는 앞줄의 오른쪽 식 `a + b`를 이어받으므로
두 줄을 연결하면 처음 목표인 `(a + 0) + b = b + a`를 얻는다.

{anchor "preliminaries-simp"}[]간단한 식은 익숙한 계산 법칙으로 한꺼번에 정리할 수도 있다.
예를 들어 $`0a+(b+0)`에서는 $`0a=0`, $`b+0=b`, $`0+b=b`를 사용하면 $`b`가 남는다.
Lean의 `simp`는 정리 규칙으로 등록된 정리들을 사용하여 이러한 식을 정리하는 전술이다.
위의 세 법칙에 해당하는 `Int.zero_mul`, `Int.add_zero`, `Int.zero_add`도 등록되어 있으므로
다음 등식은 `simp`로 증명할 수 있다.

```savedLean
example (a b : Int) :
    0 * a + (b + 0) = b := by
  simp
```

`simp`는 등록된 규칙에 따라 왼쪽 식을 `b`로 바꾸고 양변이 같음을 확인하여 증명을 마친다.
`dsimp`가 정의에 따른 계산을 수행한다면 `simp`는 이처럼 이미 증명된 정리도 사용한다.
특정한 등식을 골라 식을 바꾸려면 앞에서 배운 `rw [등식]`을 사용한다.

## 나누어떨어짐
%%%
tag := "preliminaries-defining-divisibility"
%%%

짝수의 정의에서는 $`2`의 배수라는 조건을 사용했다.
이제 임의의 정수의 배수를 나타내는 관계를 정의하자.

*정의* 정수 $`a`, $`b`에 대하여 $`b = ak`인 정수 $`k`가 존재하면
$`a`가 $`b`를 *나눈다*고 하며 $`a \mid b`로 나타낸다.

```savedLean
def Divides : Int → Int → Prop :=
  fun a b => ∃ k : Int, b = a * k
local infix:50 (priority := high) " ∣ " => Divides
```

기호 `∣`는 `Divides`에 연결했으며 `\mid`로 입력한다.
`a ∣ b`를 보이려면 `b = a * k`를 만족하는 정수 `k`를 제시하면 된다.
이 정의는 $`a=0`인 경우도 포함한다. 이때 $`0\mid b`이면 $`b=0\cdot k=0`이다.
정수의 짝수도 이 관계로 표현할 수 있다. 정수 $`a`가 어떤 정수의 두 배라는 조건은
`2 ∣ a`이며, 이때는 음의 정수도 포함한다.

*보기* $`54=6\cdot9`이므로 $`6 \mid 54`이다.

```savedLean
example :
    6 ∣ 54 := by
  exists 9
```

*정리* 모든 정수 $`a`에 대하여 $`a \mid a`이다.

*증명* $`a=a\cdot1`이므로 정수 $`1`을 택하면 된다.
Lean에서는 이 등식을 정수 곱셈의 법칙 `Int.mul_one`으로 확인한다.

```savedLean
theorem divides_refl (a : Int) : a ∣ a := by
  exists 1
  rw [Int.mul_one]
```

`exists 1`을 쓰면 목표가 `a = a * 1`이 되며
`rw [Int.mul_one]`으로 오른쪽을 `a`로 바꾸면 증명이 끝난다.

{anchor "preliminaries-divisibility-properties"}[]*정리* $`a \mid b`이고 $`a \mid c`이면 $`a \mid b+c`이다.

*증명* 가정에 따라 $`b=ak`, $`c=al`인 정수 $`k`, $`l`을 택하면
$`b+c=ak+al=a(k+l)`이므로 곱하는 정수로 $`k+l`을 사용할 수 있다.

마지막 등식에는 분배법칙을 사용했으며 Lean에서는 `Int.mul_add`로 이 법칙을 쓴다.

```savedLean
theorem divides_add (a b c : Int)
    (hab : a ∣ b)
    (hac : a ∣ c) :
    a ∣ b + c := by
  unpack hab with ⟨k, hk⟩
  unpack hac with ⟨l, hl⟩

  -- 각 배수의 계수를 더하여 합의 계수를 만든다.
  exists (k + l)
  calc
    b + c = a * k + a * l := by rw [hk, hl]
    _ = a * (k + l) := by rw [Int.mul_add]
```

`unpack`으로 두 가정에서 `hk : b = a * k`와 `hl : c = a * l`을 얻는다.
`exists (k + l)`로 목표를 `b + c = a * (k + l)`로 바꾼 뒤
`calc`의 첫 줄에서 두 등식을 사용하고 둘째 줄에서 분배법칙으로 식을 묶는다.

*정리* $`a \mid b`이고 $`b \mid c`이면 $`a \mid c`이다.

*증명* $`b=ak`, $`c=bl`인 정수 $`k`, $`l`을 택하면 $`c=(ak)l=a(kl)`이므로
곱하는 정수로 $`kl`을 사용한다.
이때 괄호를 옮기는 데 필요한 곱셈의 결합법칙은 Lean에서 `Int.mul_assoc`이다.

```savedLean
theorem divides_trans (a b c : Int)
    (hab : a ∣ b)
    (hbc : b ∣ c) :
    a ∣ c := by
  unpack hab with ⟨k, hk⟩
  unpack hbc with ⟨l, hl⟩

  -- 두 배수의 계수를 곱하여 c를 a의 배수로 나타낸다.
  exists (k * l)
  calc
    c = b * l := by exact hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by rw [Int.mul_assoc]
```

*보기* 정수 $`a`가 $`6`의 배수이고 정수 $`b`가 $`10`의 배수이면 $`a+b`는 $`2`의 배수이다.

*풀이* $`2\mid6`과 $`6\mid a`에서 추이성으로 $`2\mid a`를 얻는다.
같은 방법으로 $`2\mid10`과 $`10\mid b`에서 $`2\mid b`를 얻으면,
앞의 덧셈에 관한 정리로 $`2\mid a+b`를 결론 내릴 수 있다.

```savedLean
example (a b : Int)
    (ha : 6 ∣ a)
    (hb : 10 ∣ b) :
    2 ∣ a + b := by
  have hTwoSix : 2 ∣ 6 := by exists 3
  have hTwoTen : 2 ∣ 10 := by exists 5
  have hTwoA : 2 ∣ a := by
    exact divides_trans 2 6 a hTwoSix ha

  have hTwoB : 2 ∣ b := by
    exact divides_trans 2 10 b hTwoTen hb

  exact divides_add 2 a b hTwoA hTwoB
```

수를 직접 택하는 부분은 $`6=2\cdot3`과 $`10=2\cdot5`를 확인하는 두 줄이다.
$`a`, $`b`가 어떤 수인지는 몰라도 `divides_trans`와 `divides_add`에
주어진 나누어떨어짐을 사용하면 합에 관한 결론을 얻는다.

# 나머지와 합동
%%%
tag := "preliminaries-congruence"
file := "congruence"
%%%

$`23=3\cdot7+2`이고 $`-5=(-1)\cdot7+2`이므로 두 정수는 $`7`로 나누었을 때 같은 나머지를 갖는다.
두 등식을 빼면 $`23-(-5)=(3-(-1))\cdot7`이므로 두 정수의 차이는 $`7`의 배수이다.
이처럼 같은 나머지를 갖는 정수들을 차이가 주어진 정수의 배수라는 조건으로 묶어 보자.

Lean에서는 자연수와 정수의 몫을 `a / n`, 나머지를 `a % n`으로 쓴다.
정수에서 $`n>0`이면 $`a=nq+r`이고 $`0\leq r<n`인 몫 $`q`와 나머지 $`r`을 구한다.
위 두 수의 나머지를 Lean으로 확인하면 다음과 같다.

```savedLean
example :
    (23 : Int) / 7 = 3 ∧ (23 : Int) % 7 = 2 := by
  decide

example :
    (-5) / 7 = -1 ∧ (-5) % 7 = 2 := by
  decide
```

두 등식 모두 나머지가 $`2`라는 사실을 확인한다.
이러한 관계를 나눗셈의 계산 대신 배수의 존재로 표현하면 다음 정의를 얻는다.

*정의* 정수 $`n`을 고정하자.
$`a=b+nk`인 정수 $`k`가 존재하면 $`a`와 $`b`가 $`n`을 법으로 *합동*이라고 하며
$`a\equiv b\pmod n`으로 나타낸다.

이 조건은 앞에서 정의한 나누어떨어짐으로 $`n\mid(a-b)`라고 쓸 수 있다.
나머지를 비교할 때는 $`n>0`으로 두지만 배수에 의한 정의는 $`n=0`이나 음의 정수에도 적용할 수 있다.
아래의 세 성질도 법의 부호와 관계없이 성립한다.

```savedLean
def Congruent (n : Int) : Int → Int → Prop :=
  fun a b => ∃ k : Int, a = b + n * k
local notation:50 a " ≡ " b " [ZMOD " n "]" =>
  Congruent n a b
```

법 `n`을 정하면 `Congruent n`의 타입은 `Int → Int → Prop`이다.
앞의 술어가 원소 하나에 명제를 대응시켰던 것처럼,
여기서는 두 정수 `a`, `b`에 합동이라는 명제를 대응시킨다.
수학식 $`a\equiv b\pmod{n}`을 Lean에서는 `a ≡ b [ZMOD n]`으로 쓴다.
기호 `≡`는 `\==`로 입력한다.

*보기* $`23=2+7\cdot3`이므로 $`23\equiv2\pmod7`이다.
`exists 3`으로 정수를 제시하면 남은 등식은 계산으로 확인된다.

```savedLean
theorem preliminaries_congruent_twenty_three_two :
    23 ≡ 2 [ZMOD 7] := by
  exists 3
```

합동의 법 $`n`을 고정하면 다음 세 성질이 성립한다.

1. 모든 정수 $`a`에 대하여 $`a\equiv a\pmod n`이다.
2. $`a\equiv b\pmod n`이면 $`b\equiv a\pmod n`이다.
3. $`a\equiv b\pmod n`이고 $`b\equiv c\pmod n`이면 $`a\equiv c\pmod n`이다.

첫째 성질에서는 $`a=a+n\cdot0`이므로 정수 $`0`을 택한다.
둘째 성질에서는 $`a=b+nk`를 $`b=a+n(-k)`로 정리하여 $`-k`를 택한다.
셋째 성질에서는 $`a=b+nk`와 $`b=c+nl`을 이어서 $`a=c+n(l+k)`를 얻으므로 $`l+k`를 택하면 된다.

```savedLean
theorem congruent_refl (n a : Int) : a ≡ a [ZMOD n] := by
  exists 0
  rw [Int.mul_zero, Int.add_zero]

theorem congruent_symm (n a b : Int)
    (h : a ≡ b [ZMOD n]) :
    b ≡ a [ZMOD n] := by
  unpack h with ⟨k, hk⟩
  exists (-k)
  rw [hk, Int.mul_neg, Int.add_neg_cancel_right]

theorem congruent_trans (n a b c : Int)
    (hab : a ≡ b [ZMOD n])
    (hbc : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  unpack hab with ⟨k, hk⟩
  unpack hbc with ⟨l, hl⟩
  exists (l + k)
  rw [hk, hl, Int.mul_add, Int.add_assoc]
```

각 증명의 마지막 `rw`는 선택한 정수가 조건을 만족하는지 확인한다.
첫 증명에서는 `Int.mul_zero`로 $`n\cdot0`을 $`0`으로 바꾸고
`Int.add_zero`로 $`a+0`을 $`a`로 바꾼다.
둘째 증명에서는 `Int.mul_neg`로 $`n(-k)`를 $`-(nk)`로 바꾼 뒤
`Int.add_neg_cancel_right`로 $`(b+nk)-(nk)=b`를 확인한다.
마지막 증명에서는 앞에서 쓴 분배법칙으로 $`n(l+k)=nl+nk`를 얻고
덧셈의 결합법칙 `Int.add_assoc`로 괄호를 정리한다.

*보기* 이 절 첫머리의 두 정수 $`23`, $`-5`가 $`7`을 법으로 합동임을 보이자.
$`23\equiv2\pmod7`은 이미 증명했다.
$`-5=2+7\cdot(-1)`에서 $`-5\equiv2\pmod7`을 얻고 그 방향을 바꾸면
$`23\equiv2\equiv-5\pmod7`로 두 합동을 연결할 수 있다.

```savedLean
theorem congruent_neg_five_two : -5 ≡ 2 [ZMOD 7] := by
  exists (-1)

theorem congruent_twenty_three_neg_five :
    23 ≡ -5 [ZMOD 7] := by
  apply congruent_trans 7 23 2 (-5)
  · exact preliminaries_congruent_twenty_three_two
  · exact congruent_symm 7 (-5) 2 congruent_neg_five_two
```

추이성의 중간 정수는 $`2`이다.
두 번째 목표는 `2 ≡ -5 [ZMOD 7]`이므로 방금 얻은 합동에 대칭성을 사용한다.
따라서 두 정수의 차이를 새로 계산하지 않고 앞의 합동들을 이어서 결론을 얻는다.

## 법이 0이나 1인 합동
%%%
tag := "preliminaries-congruence-zero-and-one"
%%%

합동을 배수에 관한 조건으로 정의했으므로 법을 $`0`이나 $`1`로 두어도 명제가 된다.
이 두 경우에 어떤 관계를 얻는지 정의를 펼쳐 확인하자.

*보기* $`a\equiv b\pmod{0}`일 필요충분조건은 $`a=b`이다.

*풀이* 합동의 정의에서 $`a=b+0\cdot k`는 $`a=b`가 된다.
거꾸로 $`a=b`이면 정수 $`k=0`을 택하여 합동의 조건을 만족시킬 수 있다.

```savedLean
example
    (a b : Int) :
    a ≡ b [ZMOD 0] ↔ a = b := by
  constructor
  · intro h
    -- 합동의 조건에서 0의 배수를 지우면 a = b이다.
    unpack h with ⟨k, hk⟩
    rw [Int.zero_mul, Int.add_zero] at hk
    exact hk

  · intro h
    -- 차이가 0이므로 합동에 필요한 정수로 0을 택한다.
    exists 0
    rw [Int.mul_zero, Int.add_zero]
    exact h
```

정방향에서는 `Int.zero_mul`로 $`0\cdot k=0`을 사용하고
역방향에서는 `Int.mul_zero`로 $`0\cdot0=0`을 사용한다.
두 방향 모두 곱셈과 덧셈을 정리하면 등식 $`a=b`를 얻는다.

*보기* 임의의 두 정수 $`a`, $`b`에 대하여 $`a\equiv b\pmod{1}`이다.

*풀이* $`a=b+1\cdot(a-b)`이므로 합동의 정의에서 정수 $`a-b`를 택하면 된다.

```savedLean
example
    (a b : Int) :
    a ≡ b [ZMOD 1] := by
  exists (a - b)
  rw [Int.one_mul, Int.add_comm b, Int.sub_add_cancel]
```

`Int.one_mul`로 $`1\cdot(a-b)`를 $`a-b`로 바꾸고
덧셈의 교환법칙으로 $`b+(a-b)`를 $`(a-b)+b`로 바꾼다.
마지막에는 `Int.sub_add_cancel`로 $`(a-b)+b=a`를 사용한다.

따라서 법이 $`0`이면 같은 정수끼리만 합동이며 법이 $`1`이면 모든 정수가 서로 합동이다.

# 연습문제
%%%
tag := "preliminaries-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* 모든 자연수 $`n`에 대하여 $`1+n=n+1`임을 귀납법으로 증명하라.

```savedLean -keep
theorem exercise_one_add_induction
    (n : Nat) :
    1 + n = n + 1 := by
  sorry
```


*문제 2* 모든 정수 $`a`에 대하여 $`a\mid0`임을 증명하라.

```savedLean -keep
theorem exercise_divides_zero (a : Int) : a ∣ 0 := by
  sorry
```


*문제 3* $`a\equiv b\pmod n`이면 $`a+t\equiv b+t\pmod n`임을 증명하라.

```savedLean -keep
theorem exercise_congruent_add_right
    (n a b t : Int)
    (h : a ≡ b [ZMOD n]) :
    a + t ≡ b + t [ZMOD n] := by
  sorry
```


*문제 4* $`37\equiv2\pmod7`을 증명한 뒤,
이 결과와 본문의 `preliminaries_congruent_twenty_three_two`를 사용하여
$`37\equiv23\pmod7`을 증명하라.

```savedLean -keep
theorem exercise_congruent_thirty_seven_two :
    37 ≡ 2 [ZMOD 7] := by
  sorry

theorem exercise_congruent_thirty_seven_twenty_three :
    37 ≡ 23 [ZMOD 7] := by
  sorry
```

*문제 5* (짝수의 합)

(1) 짝수 두 개의 합은 짝수임을 정의로 증명하라.
(2) 첫 결과와 `double_is_even`을 사용하여 $`a`가 짝수이면
$`a+\operatorname{double}(7)`도 짝수임을 보이라.
분배법칙은 `Nat.mul_add`로 사용할 수 있다.

```savedLean -keep
theorem exercise_even_add (a b : Nat)
    (ha : IsEvenNat a)
    (hb : IsEvenNat b) :
    IsEvenNat (a + b) := by
  sorry

theorem exercise_even_add_double (a : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a + double 7) := by
  sorry
```

*문제 6* (짝수의 배수)

$`a`가 짝수이면 모든 자연수 $`b`에 대하여 $`ab`도 짝수임을 증명하라.
곱셈의 결합법칙 `Nat.mul_assoc`을 사용할 수 있다.
이 결과로 $`\operatorname{double}(3)\cdot b`가 짝수임을 보이라.

```savedLean -keep
theorem exercise_even_mul (a b : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a * b) := by
  sorry

theorem exercise_double_mul_even (b : Nat) :
    IsEvenNat (double 3 * b) := by
  sorry
```

*문제 7* (서로를 나누는 정수)

$`3\mid-3`과 $`-3\mid3`을 각각 증명하라.
이어서 $`3\ne-3`을 확인하여 정수에서는 $`a\mid b`이고 $`b\mid a`여도
$`a=b`를 결론지을 수 없음을 보이라.

```savedLean -keep
theorem exercise_divisibility_sign :
    (3 ∣ -3) ∧ ((-3) ∣ 3) := by
  sorry

theorem exercise_three_ne_negative_three :
    (3 : Int) ≠ -3 := by
  sorry
```

*문제 8* (법의 배수와 합동)

(1) $`a\equiv b\pmod{nd}`이면 $`a\equiv b\pmod n`임을 증명하라.
(2) $`20\equiv2\pmod6`을 직접 증명한 뒤 첫 결과를 사용하여
$`20\equiv2\pmod3`을 보이라.

```savedLean -keep
theorem exercise_congruent_divisor (n d a b : Int)
    (h : a ≡ b [ZMOD n * d]) :
    a ≡ b [ZMOD n] := by
  sorry

theorem exercise_twenty_mod_six : 20 ≡ 2 [ZMOD 6] := by
  sorry

theorem exercise_twenty_mod_three : 20 ≡ 2 [ZMOD 3] := by
  sorry
```

# 산술 계산의 자동화
%%%
tag := "preliminaries-arith"
file := "arithmetic-automation"
%%%

앞에서는 자연수에 관한 귀납법으로 $`5`가 짝수가 아님을 증명했다.
이후의 증명에서는 이런 산술 계산을 전술 `arith`로 확인할 수 있다.
`arith`는 자연수와 정수의 덧셈·뺄셈·상수배에 관한 등식과 부등식,
다항식의 등식, 등록된 곱셈·몫·나머지·나누어떨어짐의 성질을 사용한다.
증명의 가정에 있는 등식과 부등식도 함께 사용하여 목표를 확인한다.

*보기* 모든 정수 $`n`에 대하여 $`2n\ne5`이다.

```savedLean
example
    (n : Int) :
    2 * n ≠ 5 := by
  arith
```

`arith`는 $`2n=5`를 만족하는 정수가 없음을 확인하여 증명을 마친다.
앞에서 한 단계씩 사용한 덧셈의 법칙도 같은 전술로 처리할 수 있다.

```savedLean
example
    (a b : Int) :
    (a + 0) + b = b + a := by
  arith
```

이 증명에서도 $`a+0=a`와 $`a+b=b+a`라는 덧셈의 법칙을 사용한다.
전술의 사용 범위와 더 많은 예는 {ref "tactic-arith"}[부록의 산술식 계산]에 정리했다.



나머지의 등식 $`a\bmod m=a`를 증명하려면 $`a<m`임을 보이는 것으로 충분하다.
이처럼 원래 목표를 얻을 수 있는 조건을 먼저 증명할 때는 `suffices`를 사용한다.
아래의 `suffices bound : a < m by arith`에서는
`by arith`가 `bound : a < m`으로부터 나머지의 등식을 얻는 연결 증명이다.
이 연결을 확인한 뒤에는 `a < m` 자체가 새 목표로 남는다.

```savedLean
example
    (a m : Nat)
    (h : a < m) :
    a % m = a := by
  suffices bound : a < m by arith
  exact h
```

새 목표 `a < m`은 주어진 `h`로 증명한다.
`by` 뒤에서는 “`bound`가 성립하면 원래 목표를 얻는다”를 증명한다.
그 뒤의 본문에서는 `bound`로 사용하려던 조건 `a < m` 자체를 증명한다.

## 대칭성을 이용한 경우의 환원
%%%
tag := "preliminaries-wlog"
file := "without-loss-of-generality"
%%%

두 자연수 중 작은 수를 `min a b`, 큰 수를 `max a b`로 나타내자.
이 두 수의 합은 `a + b`이다.
`a ≤ b`이면 작은 수가 `a`이고 큰 수가 `b`이므로 바로 확인할 수 있으며,
반대 경우에는 두 수의 자리를 바꾸어 같은 논증을 사용한다.

전술 `wlog`는 한 경우를 가정하여 증명을 진행하고,
나머지 경우를 그 경우로 환원하는 증명을 별도로 요구한다.
아래의 `wlog hab : a ≤ b generalizing a b with ordered`는
먼저 `a ≤ b`인 경우의 결과를 `ordered`라는 가정으로 두고 나머지 경우를 증명하게 한다.
그 뒤에 `a ≤ b`인 경우를 직접 증명한다.

여기서 `generalizing a b`는 `ordered`가 현재의 두 수에만 한정되지 않도록
`a`, `b`를 일반화한다. 즉, 임의의 자연수 `u`, `v`에 대하여
`u ≤ v`이면 `min u v + max u v = u + v`라는 결과를 사용할 수 있다.
따라서 `u`에 `b`를, `v`에 `a`를 넣어 순서를 바꾼 두 수에도 적용할 수 있다.

이 예제에서는 {ref "tactic-auto-normalization"}[자동 표현 정리]를 켜고 진행하자.
그러면 `a ≤ b`가 아닌 경우의 가정 `¬ a ≤ b`는 `b < a`로 표시된다.

```savedLean
open scoped Ample.Auto
```

```savedLean
example (a b : Nat) :
    min a b + max a b = a + b := by
  wlog hab : a ≤ b generalizing a b with ordered
  · -- b < a이므로 b ≤ a를 얻고, 순서를 바꾸어 ordered를 사용한다.
    have hba : b ≤ a := by arith
    rw [Nat.min_comm a b, Nat.max_comm a b]
    rw [Nat.add_comm a b]
    exact ordered b a hba

  · -- a ≤ b인 경우에는 작은 수와 큰 수가 각각 a와 b이다.
    rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
```

첫 목표에는 `hab : b < a`와
`ordered : ∀ u v, u ≤ v → min u v + max u v = u + v`가 주어진다.
`arith`로 `b < a`에서 `hba : b ≤ a`를 얻고,
교환법칙으로 목표를 `min b a + max b a = b + a`로 바꾼다.
이제 `ordered b a hba`가 그 등식의 증명이므로 첫 목표를 마칠 수 있다.
둘째 목표에는 `hab : a ≤ b`가 있으며,
`Nat.min_eq_left hab`와 `Nat.max_eq_right hab`로 각각의 값을 정리한다.

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
