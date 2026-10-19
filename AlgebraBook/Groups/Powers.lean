import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Calculations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "거듭제곱" =>

%%%
tag := "group-powers"
file := "powers"
%%%

하나의 원소를 여러 번 연산한 결과를 거듭제곱으로 나타내자. 자연수 지수에서는 귀납법으로 법칙을 증명하고, 역원을 사용하여 정수 지수로 범위를 넓힌다. 같은 원소의 거듭제곱끼리의 계산과 서로 다른 원소의 계산을 구별하며 지수 법칙에 필요한 가정을 확인한다.

```savedImport
import AlgebraBook.Groups.Calculations
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Course
variable {A B : Type}
```

# 자연수 지수
%%%
tag := "group-natural-powers"
file := "natural-powers"
%%%

*정의* 군의 원소 $`a`와 자연수 $`n`에 대하여 $`a^0=e`, $`a^{n+1}=a^na`로 정한 원소를 $`a`의 $`n`제곱이라고 한다.

이 정의에 따라 $`a^1=ea=a`, $`a^2=aa`, $`a^3=(aa)a`이다. Lean에서도 $`0`과 $`n+1`인 경우를 나누어 재귀함수를 정의한다.

```savedLean
def power (G : Group A) (a : A) : Nat → A
  | 0 => G.id
  | n + 1 => G.op (power G a n) a

theorem power_zero (G : Group A) (a : A) :
    power G a 0 = G.id := by rfl
theorem power_succ (G : Group A) (a : A) (n : Nat) :
    power G a (n + 1) = G.op (power G a n) a := by rfl
theorem power_one (G : Group A) (a : A) :
    power G a 1 = a := by
  rw [power_succ, power_zero, G.id_left]
```

`power G a n`은 군 구조 `G`에서 구한 $`a^n`이다. 정의의 두 경우는 자연수의 생성자에 대응하며, 뒤의 경우에서 `power G a n`을 먼저 구한 뒤 `a`를 오른쪽에 연산한다. `power_one`에서는 $`a^1=ea=a`라는 계산을 적었다.

곱셈 표기를 쓰는 범위에서는 이 정의를 `^`에 연결할 수 있다. 아래의 보기는 그 표기를 사용하여 세제곱을 확인한다.

```savedLean
variable (G : Group A)
local infixr:80 (priority := high) " ^ " => power G

theorem power_three_notation (a : A) :
    a ^ 3 =
  G.op (G.op a a) a := by
  rw [power_succ, power_succ, power_one]
```

표기 연결의 인수에 `G`가 들어 있으므로 현재 사용하는 군의 연산으로 거듭제곱을 계산한다. 아래의 일반 정리에서는 군과 지수의 타입을 함께 확인할 수 있도록 `power G a n`을 사용한다.

# 지수의 덧셈과 곱셈
%%%
tag := "group-power-laws"
file := "exponent-laws"
%%%

*정리* 자연수 $`n,m`에 대하여 $`a^{n+m}=a^na^m`이다.

*증명* $`n`을 고정하고 $`m`에 대한 귀납법을 사용하자. $`m=0`이면 양변이 모두 $`a^n`이다. $`m`에서의 등식을 가정하면

$$`a^{n+(m+1)}=a^{n+m}a=(a^na^m)a=a^n(a^ma)=a^na^{m+1}`

이므로 다음 경우도 성립한다.

```savedLean
theorem power_add (G : Group A) (a : A) (n m : Nat) :
    power G a (n + m) =
      G.op (power G a n) (power G a m) := by
  induction m with
  | zero => rw [Nat.add_zero, power_zero, G.id_right]
  | succ m ih =>
      rw [Nat.add_succ, power_succ, power_succ, ih, G.assoc]
```

`succ m ih`에서 `ih`는 $`a^{n+m}=a^na^m`의 증명이다. `Nat.add_succ`로 지수를 $`(n+m)+1`로 바꾼 뒤 정의, 귀납 가정과 결합법칙을 차례로 사용한다.

특히 $`n+1=1+n`이므로 $`a^{n+1}=aa^n`도 성립한다. 또한 $`n+m=m+n`을 사용하면 같은 원소의 두 거듭제곱은 서로 가환한다.

```savedLean
theorem power_succ_left (G : Group A) (a : A) (n : Nat) :
    power G a (n + 1) = G.op a (power G a n) := by
  have h : n + 1 = 1 + n := by arith
  rw [h, power_add, power_one]

theorem power_comm (G : Group A) (a : A) (n m : Nat) :
    G.op (power G a n) (power G a m) =
      G.op (power G a m) (power G a n) := by
  rw [← power_add, ← power_add]
  rw [Nat.add_comm n m]
```

*정리* $`a^{nm}=(a^n)^m`이다. 이번에도 $`m`에 대한 귀납법을 사용하며 $`n(m+1)=nm+n`에서 앞의 덧셈 법칙을 적용한다.

```savedLean
theorem power_mul (G : Group A) (a : A) (n m : Nat) :
    power G a (n * m) = power G (power G a n) m := by
  induction m with
  | zero => rw [Nat.mul_zero, power_zero, power_zero]
  | succ m ih =>
      rw [Nat.mul_succ, power_add, power_succ, ih]
```

*정리* $`(a^n)^{-1}=(a^{-1})^n`이다.

*증명* $`n=0`이면 양변이 항등원이다.
$`n`에서의 등식을 가정하면 곱의 역원 법칙에 따라 다음과 같이 계산한다.

$$`(a^{n+1})^{-1}=(a^na)^{-1}=a^{-1}(a^n)^{-1}
=a^{-1}(a^{-1})^n=(a^{-1})^{n+1}.`

마지막 등식에는 왼쪽에서 한 번 연산하는 형태의 법칙 `power_succ_left`를 사용한다.

```savedLean
theorem inv_power (G : Group A) (a : A) (n : Nat) :
    G.inv (power G a n) = power G (G.inv a) n := by
  induction n with
  | zero => rw [power_zero, power_zero, inv_id]
  | succ n ih =>
      rw [power_succ, inv_op, ih, ← power_succ_left]
```

# 가환하는 두 원소
%%%
tag := "group-commuting-powers"
file := "commuting-elements"
%%%

서로 다른 원소 $`a,b`에서는 $`(ab)^2=abab`이고 $`a^2b^2=aabb`이다. 가운데의 $`b`와 $`a`를 교환할 수 있으면 두 식이 같아진다. 이 가정을 일반 지수에도 적용해 보자.

먼저 $`ab=ba`이면 $`ab^n=b^na`임을 귀납법으로 보인다.

```savedLean
theorem op_power_comm (G : Group A) (a b : A)
    (hab : G.op a b = G.op b a)
    (n : Nat) :
    G.op a (power G b n) = G.op (power G b n) a := by
  induction n with
  | zero => rw [power_zero, G.id_left, G.id_right]
  | succ n ih =>
      -- 귀납 가정과 ab = ba를 차례로 사용한다.
      rw [power_succ, ← G.assoc, ih, G.assoc, hab,
        ← G.assoc]
```

*정리* $`ab=ba`이면 모든 자연수 $`n`에 대하여 $`(ab)^n=a^nb^n`이다.

귀납 단계에서는 $`(a^nb^n)(ab)`에서 $`b^n`과 $`a`를 바꾼 뒤 같은 원소끼리 묶는다. 이 교환을 정당화하는 것이 방금 증명한 보조정리이다.

```savedLean
theorem power_op_of_comm (G : Group A) (a b : A)
    (hab : G.op a b = G.op b a)
    (n : Nat) :
    power G (G.op a b) n =
      G.op (power G a n) (power G b n) := by
  induction n with
  | zero => rw [power_zero, power_zero, power_zero,
    G.id_left]
  | succ n ih =>
      -- 귀납 가정으로 앞의 n번 곱을 두 거듭제곱으로 나눈다.
      rw [power_succ, ih, power_succ, power_succ]

      -- b의 거듭제곱과 a를 교환한 뒤 같은 원소끼리 묶는다.
      calc
        G.op (G.op (power G a n) (power G b n)) (G.op a b) =
            G.op (power G a n) (G.op (G.op (power G b n)
              a) b) := by
          rw [G.assoc, ← G.assoc (power G b n) a b]
        _ = G.op (power G a n) (G.op (G.op a (power G b
          n)) b) := by
          rw [← op_power_comm G a b hab n]
        _ = G.op (G.op (power G a n) a) (G.op (power G b
          n) b) := by
          rw [G.assoc a, ← G.assoc]
```

군 전체가 아벨군이면 임의의 두 원소에 이 정리를 사용할 수 있다. 일반 군에서 이 가정을 생략하면 성립하지 않는 예는 {ref "permutation-power-counterexample"}[순열의 거듭제곱]에서 직접 계산한다.

# 정수 지수
%%%
tag := "group-integer-powers"
file := "integer-powers"
%%%

*정의* 자연수 지수에서 이미 정한 값을 유지하고 양의 자연수 $`n`에 대하여 $`a^{-n}=(a^n)^{-1}`로 정한다.

Lean의 정수는 `Int.ofNat n`과 `Int.negSucc n`으로 나뉜다. 첫째는 자연수 $`n`을 정수로 다룬 것이고 둘째는 $`-(n+1)`이다. `Int.negSucc 0`은 $`-1`이므로 이 두 경우는 겹치지 않는다.

```savedLean
def integerPower (G : Group A) (a : A) : Int → A
  | .ofNat n => power G a n
  | .negSucc n => G.inv (power G a (n + 1))

theorem integerPower_nat (G : Group A) (a : A) (n : Nat) :
    integerPower G a (n : Int) = power G a n := by rfl
theorem integerPower_zero (G : Group A) (a : A) :
    integerPower G a 0 = G.id := by rfl
theorem integerPower_negSucc (G : Group A) (a : A)
    (n : Nat) :
    integerPower G a (Int.negSucc n) =
      G.inv (power G a (n + 1)) := by rfl
```

`integerPower G a z`는 정수 지수 $`a^z`이다.
자연수 지수의 `power G a n`과 이름을 구별하였으며,
음수 지수에서는 해당 자연수 거듭제곱의 역원을 구한다.

정수 지수에서도 $`a^{z+1}=a^za`가 성립함을 먼저 보이자. 음수 지수에서는 $`a^{-(n+2)}a=(a^{n+2})^{-1}a`에서 역원의 법칙을 적용하여 $`(a^{n+1})^{-1}`를 얻는다.

```savedLean
theorem integerPower_succ (G : Group A) (a : A) (z : Int) :
    integerPower G a (z + 1) =
      G.op (integerPower G a z) a := by
  cases z with
  | ofNat n => exact power_succ G a n
  | negSucc n =>
      cases n with
      | zero =>
          -- 지수가 -1이면 역원과 원소의 곱을 확인한다.
          have hz : Int.negSucc 0 + 1 = 0 := by rfl
          rw [hz]
          rw [integerPower_zero, integerPower_negSucc,
            power_one, G.inv_left]

      | succ n =>
          -- 더 작은 음수 지수에서는 역원의 곱을 풀어 소거한다.
          have hz : Int.negSucc (n + 1) + 1 =
              Int.negSucc n := by arith
          rw [hz, integerPower_negSucc,
            integerPower_negSucc]
          rw [power_succ_left G a (n + 1), inv_op,
            G.assoc, G.inv_left, G.id_right]
```

`negSucc`의 `zero` 경우는 $`a^{-1}a=e`이고, `succ n` 경우는 방금 계산한 음수 지수의 관계이다. 정수의 등식은 `arith`로 확인하고 군의 식은 앞의 법칙으로 직접 계산한다.

이 한 단계의 관계에 자연수에 대한 귀납법을 적용하면 정수 지수에 음이 아닌 정수를 더하는 법칙을 얻는다.

```savedLean
theorem integerPower_add_nat (G : Group A) (a : A)
    (z : Int) (n : Nat) :
    integerPower G a (z + (n : Int)) =
      G.op (integerPower G a z) (power G a n) := by
  induction n with
  | zero => rw [Int.ofNat_zero, Int.add_zero, power_zero,
    G.id_right]

  | succ n ih =>
      -- 지수에 자연수를 하나 더하는 형태로 바꾸어 귀납 가정을 쓴다.
      have hz : z + ((n + 1 : Nat) : Int) =
          (z + (n : Int)) + 1 := by arith
      rw [hz, integerPower_succ, ih, power_succ, G.assoc]
```

*정리* 모든 정수 $`z,w`에 대하여 $`a^{z+w}=a^za^w`이다.

*증명* $`w`가 음이 아니면 앞의 보조정리를 적용한다.
$`w=-(n+1)`이면 비교할 두 식의 오른쪽에 $`a^{n+1}`을 곱하자.
왼쪽은 지수에 $`n+1`을 더하면 $`a^z`가 되고,
오른쪽도 역원을 소거하면 $`a^z`가 된다.

$$`a^{z-(n+1)}a^{n+1}=a^z
=\bigl(a^z(a^{n+1})^{-1}\bigr)a^{n+1}.`

오른쪽 소거법칙에 따라 처음의 두 식도 같다.

```savedLean
theorem integerPower_add (G : Group A) (a : A) (z w : Int) :
    integerPower G a (z + w) =
      G.op (integerPower G a z) (integerPower G a w) := by
  cases w with
  | ofNat n => exact integerPower_add_nat G a z n
  | negSucc n =>
      rw [integerPower_negSucc]

      -- 오른쪽에 같은 거듭제곱을 곱하여 비교한다.
      apply op_right_cancel G (power G a (n + 1))
      calc
        G.op (integerPower G a (z + Int.negSucc n))
            (power G a (n + 1)) =
            integerPower G a
              ((z + Int.negSucc n) + ((n + 1 : Nat) : Int))
              := by rw [integerPower_add_nat]

        -- 더한 지수와 음수 지수가 상쇄된다.
        _ = integerPower G a z := by
          have hz : (z + Int.negSucc n) +
              ((n + 1 : Nat) : Int) = z := by arith
          rw [hz]

        -- 오른쪽에도 서로 역원인 두 원소의 곱을 넣는다.
        _ = G.op (integerPower G a z)
            (G.op (G.inv (power G a (n + 1)))
              (power G a (n + 1))) := by
          rw [G.inv_left, G.id_right]
        _ = G.op
            (G.op (integerPower G a z)
              (G.inv (power G a (n + 1))))
            (power G a (n + 1)) := by rw [G.assoc]
```

이 증명은 `op_right_cancel`로 원래의 등식을 더 쉽게 비교할 수 있는 등식으로 바꾼다. 새 등식의 양변을 계산한 뒤 마지막 줄에서 결합법칙으로 괄호를 맞춘다.

또한 $`a^{-z}a^z=a^0=e`이므로 역원의 유일성을 사용하면 $`a^{-z}=(a^z)^{-1}`이다. 따라서 뺄셈에 대한 지수 법칙도 얻는다.

```savedLean
theorem integerPower_neg (G : Group A) (a : A) (z : Int) :
    integerPower G a (-z) = G.inv (integerPower G a z) := by
  apply inverse_unique G (integerPower G a z)
  rw [← integerPower_add]
  have hz : -z + z = 0 := by arith
  rw [hz, integerPower_zero]

theorem integerPower_sub (G : Group A) (a : A) (z w : Int) :
    integerPower G a (z - w) =
      G.op (integerPower G a z)
        (G.inv (integerPower G a w)) := by
  have hzw : z - w = z + -w := by arith
  rw [hzw, integerPower_add, integerPower_neg]
```

*정리* 정수 지수에서도 $`a^{zw}=(a^z)^w`이다.

*증명* 먼저 $`w`가 자연수이면 $`w`에 대한 귀납법과 지수의 덧셈 법칙을 사용한다.
$`w=-(n+1)`이면 $`zw=-(z(n+1))`이므로
양변을 각각 $`a^{z(n+1)}`와 $`(a^z)^{n+1}`의 역원으로 바꾼다.
이 두 원소는 자연수인 경우의 결과에 따라 같으므로 역원도 같다.

```savedLean
theorem power_integerPower (G : Group A) (a : A) (z : Int)
  (n : Nat) :
    power G (integerPower G a z) n =
      integerPower G a (z * (n : Int)) := by
  induction n with
  | zero => rw [Int.ofNat_zero, Int.mul_zero, power_zero,
    integerPower_zero]

  | succ n ih =>
      rw [power_succ, ih]

      -- 군의 곱셈에 맞추어 정수 지수를 두 항의 합으로 정리한다.
      have hz : z * ((n + 1 : Nat) : Int) =
          z * (n : Int) + z := by arith
      rw [hz, integerPower_add]

theorem integerPower_mul (G : Group A) (a : A) (z w : Int) :
    integerPower G a (z * w) = integerPower G
      (integerPower G a z) w := by
  cases w with
  | ofNat n => exact (power_integerPower G a z n).symm
  | negSucc n =>
      -- 음수 지수를 역원으로 바꾸어 자연수 지수의 결과를 쓴다.
      rw [integerPower_negSucc, power_integerPower]
      have hz : z * Int.negSucc n =
          -(z * ((n + 1 : Nat) : Int)) := by arith
      rw [hz, integerPower_neg]
```

# 덧셈군에서의 거듭제곱
%%%
tag := "group-powers-additive-example"
file := "additive-example"
%%%

정수의 덧셈군에서는 항등원이 $`0`이고 연산이 덧셈이다. 따라서 이 군에서 $`a^n`은 $`a`를 $`n`번 더한 $`na`이며 음수 지수는 음의 정수배에 해당한다.

*보기* 정수의 덧셈군에서 원소 $`2`의 세제곱은 $`6`, 지수 $`-2`에서의 값은 $`-4`이다. 두 보기 모두 정의에 따른 계산으로 확인할 수 있다.

```savedLean
example :
    power intAdditionGroup 2 3 = 6 := by
  rfl

example :
    integerPower intAdditionGroup 2 (-2) = -4 := by
  rfl
```

# 두 원소 군의 거듭제곱
%%%
tag := "group-two-element-powers"
file := "boolean-powers"
%%%

*보기* 비항등원 $`u`는 $`u^2=e`이므로 $`u^3=u`, $`u^4=e`이다. 실제로 정의를 따라 계산하면 두 값이 번갈아 나온다.

```savedLean
theorem bool_power_two :
    power twoElementGroup true 2 =
  false := by
  rfl
```


```savedLean
example :
    power twoElementGroup true 3 =
  true := by rfl
example :
    power twoElementGroup true 4 =
  false := by rfl
```

일반적인 짝수·홀수 지수의 관계도 거듭제곱 법칙에서 얻는다. 예를 들어 $`u^{2n}=(u^2)^n=e^n`이며, 홀수 지수에서는 여기에 $`u`를 한 번 더 연산한다.


# 연습문제
%%%
tag := "group-powers-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* 항등원의 모든 자연수 거듭제곱이 항등원임을 증명하라.

```savedLean -keep
theorem exercise_power_identity (G : Group A) (n : Nat) :
    power G G.id n = G.id := by
  sorry
```


*문제 2* 모든 원소의 제곱이 항등원이면 군이 아벨군임을 증명하라.

```savedLean -keep
theorem exercise_square_identity_abelian (G : Group A)
    (h : ∀ a : A, G.op a a = G.id) :
    IsAbelian G := by
  sorry
```

*힌트* 각 원소가 자기 자신의 역원임을 먼저 확인한 뒤 곱의 역원을 두 가지 방법으로 나타내라.


*문제 3* $`a`와 $`b`가 가환하면 자연수 $`n`에 대하여 $`a^n`과 $`b`도 가환함을 증명하라.

```savedLean -keep
theorem exercise_power_commuting_element
    (G : Group A) (a b : A)
    (hab : G.op a b = G.op b a)
    (n : Nat) :
    G.op (power G a n) b = G.op b (power G a n) := by
  sorry
```



*문제 4* 비항등원의 짝수 지수와 홀수 지수의 값을 증명하라. 문제 1의 항등원 거듭제곱 결과를 사용할 수 있다.

```savedLean -keep
theorem exercise_bool_power_even (n : Nat) :
    power twoElementGroup true (2 * n) = false := by
  sorry

theorem exercise_bool_power_odd (n : Nat) :
    power twoElementGroup true (2 * n + 1) = true := by
  sorry
```


*문제 5* 두 원소 군의 모든 원소에 대하여 역원이 원래 원소와 같음을 보이고, 세제곱도 원래 원소임을 증명하라.

```savedLean -keep
theorem exercise_bool_inverse (b : Bool) :
    twoElementGroup.inv b = b := by
  sorry

theorem exercise_bool_cube (b : Bool) :
    power twoElementGroup b 3 = b := by
  sorry
```


```savedLean
end Course
```
