import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Permutations
import AlgebraBook.Tactic.Group

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "군 계산의 자동화" =>

%%%
tag := "group-automation"
file := "automation"
%%%

군의 기본 법칙을 사용한 계산에는 결합법칙으로 괄호를 옮기고 역원과 항등원을 소거하는 단계가 반복된다. 이제 이 계산을 `group_calc G`로 확인하자. 여기서 `G`는 계산에 사용할 군 구조이다.

```savedImport
import AlgebraBook.Groups.Permutations
import AlgebraBook.Tactic.Group
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Course
variable {A : Type}
```

# 곱과 역원
%%%
tag := "group-automation-products"
file := "products"
%%%

`group_calc G`는 앞에서 증명한 결합법칙으로 괄호를 옮기고
곱의 역원을 각 역원의 곱으로 바꾼 뒤 항등원과 이웃한 역원 쌍을 소거한다.

*보기* $`(ab)(b^{-1}c)=ac`이다.
결합법칙으로 $`bb^{-1}`를 묶으면 항등원이 되어 소거된다.

```savedLean
example (G : Group A)
    (a b c : A) :
    G.op (G.op a b) (G.op (G.inv b) c) =
      G.op a c := by
  group_calc G
```

*보기* $`((ab)c)^{-1}=c^{-1}(b^{-1}a^{-1})`이다.
곱의 역원 법칙을 두 번 적용하여 원소의 순서를 뒤집는다.

```savedLean
example (G : Group A)
    (a b c : A) :
    G.inv (G.op (G.op a b) c) =
      G.op (G.inv c) (G.op (G.inv b) (G.inv a)) := by
  group_calc G
```

이 계산에서는 결합법칙과 역원의 법칙만 사용한다.
임의의 두 원소를 교환하는 규칙은 사용하지 않으므로 일반 군에도 적용할 수 있다.

# 거듭제곱과 지수의 계산
%%%
tag := "group-automation-powers"
file := "powers"
%%%

같은 원소의 거듭제곱에는 앞에서 증명한 지수 법칙을 적용하고,
지수에 남는 자연수와 정수의 계산에는 `arith`를 사용한다.

*보기* $`a^ma^n=a^{n+m}`이다.
지수 법칙으로 왼쪽을 $`a^{m+n}`으로 바꾼 뒤 $`m+n=n+m`을 사용한다.

```savedLean
example (G : Group A) (a : A)
    (m n : Nat) :
    G.op (power G a m) (power G a n) =
      power G a (n + m) := by
  group_calc G
```

*보기* 정수 $`z`에 대하여 $`a^{z-z}=e`이다.
지수를 $`0`으로 계산하면 영제곱의 정의를 적용할 수 있다.

```savedLean
example (G : Group A) (a : A)
    (z : Int) :
    integerPower G a (z - z) = G.id := by
  group_calc G
```

두 원소의 곱을 거듭제곱할 때는 그 두 원소가 가환한다는 가정이 필요하다. 이 가정이 주어지면 `power_op_of_comm`의 조건을 확인하여 계산한다.

```savedLean
example (G : Group A)
    (a b : A)
    (hab : G.op a b = G.op b a)
    (n : Nat) :
    power G (G.op a b) n =
      G.op (power G a n) (power G b n) := by
  group_calc G
```

# 충분한 조건과 사용 범위
%%%
tag := "group-automation-suffices"
file := "sufficient-conditions"
%%%

소거법칙이나 귀납법으로 먼저 필요한 등식을 얻은 뒤 나머지 군 계산을 자동으로 처리할 수도 있다. 아래에서는 $`ca=cb`에서 $`a=b`를 얻으면 $`ab^{-1}=e`를 계산할 수 있다.

```savedLean
example (G : Group A)
    (a b c : A)
    (h : G.op c a = G.op c b) :
    G.op a (G.inv b) = G.id := by
  suffices hab : a = b by
    rw [hab]
    group_calc G

  exact op_left_cancel G c a b h
```

`suffices`의 연결 증명에서는 `hab`로 두 원소를 같게 바꾸고 역원을 소거한다.
이후 남은 `a = b`는 주어진 `h`에 왼쪽 소거법칙을 적용하여 얻는다.

`group_calc G`가 사용하는 군의 지식은 결합법칙, 항등원과 역원, 앞에서 증명한 거듭제곱 법칙이다. 현재 가정의 등식과 지수에 관한 산술 조건도 사용하며, `G`를 지정하면 그 구조의 법칙으로 계산한다. 새로운 군이나 함수를 구성하거나 귀납법의 가정을 고르는 단계는 독자가 적는다.

산술 전술 `arith`에는 군의 법칙을 추가하지 않는다. `group_calc G`가 지수의 계산에 `arith`를 사용하는 순서이며, 군의 정의와 성질을 처음 증명하는 앞 절에서는 이 자동화를 사용하지 않는다. 풀이 파일에서는 `AlgebraBook.Tactic.Group`를 가져오고 `open Course`를 적으면 사용할 수 있다.

```savedLean
end Course
```
