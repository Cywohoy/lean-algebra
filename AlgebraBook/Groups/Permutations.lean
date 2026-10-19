import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Groups.Products

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "순열군" =>

%%%
tag := "group-permutations"
file := "permutations"
%%%

한 집합에서 자기 자신으로 가는 전단사들을 합성하여 군을 만들자. 함수의 합성과 역함수의 성질을 사용하여 군의 법칙을 확인한 뒤 세 문자를 바꾸는 순열을 직접 계산한다. 합성 순서가 달라지면 결과도 달라지는 예에서 비가환성을 확인한다.

```savedImport
import AlgebraBook.Groups.Products
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Course
variable {A B : Type}
```


# 순열과 그 같음
%%%
tag := "group-permutation-definition"
file := "definition"
%%%

*정의* 집합 $`A`에서 자기 자신으로 가는 전단사함수를 $`A`의 *순열*이라고 한다.

순열에는 함수와 그 전단사성의 증명이 함께 필요하므로 앞에서 배운 부분타입으로 모을 수 있다.

```savedLean
def Permutation (A : Type) := { f : A → A // Bijective f }
```

`p : Permutation A`에서 `p.val : A → A`가 함수이고 `p.property`가 그 전단사성의 증명이다.
부분타입의 원소는 그 값으로 비교하므로 두 순열이 같음을 보이려면 두 함수가 같음을 보이면 된다.
`ext`는 이 함수의 등식에서 멈추고,
`ext x : 2`는 함수의 비교까지 이어서 임의의 원소 `x`에서 값이 같음을 목표로 삼는다.

```savedLean -show
@[ext] theorem permutation_ext {p q : Permutation A}
    (h : p.val = q.val) : p = q := by
  apply Subtype.ext
  exact h
```


# 합성을 연산으로 하는 군
%%%
tag := "group-permutation-operations"
file := "composition"
%%%

*정리* $`A`의 순열들은 함수의 합성을 연산으로 하여 군을 이룬다.

항등원은 항등함수이며 역원은 역함수이다. 항등함수와 합성이 전단사라는 사실은 함수 절에서 이미 증명했으므로 그 결과로 각 순열을 구성하자. 두 순열 $`p,q`의 곱은 $`p\circ q`로 정한다. 따라서 원소 $`x`에는 먼저 오른쪽의 $`q`를 적용하고 이어서 $`p`를 적용한다.

```savedLean
def permutationIdentity (A : Type) : Permutation A :=
  { val := identity A, property := identity_bijective A }
def permutationCompose (p q : Permutation A) :
    Permutation A :=
  { val := compose p.val q.val
    property := by
      apply bijective_compose
      · exact q.property
      · exact p.property }

noncomputable def permutationInverse
    (p : Permutation A) : Permutation A :=
  { val := inverseMap p.val p.property
    property := inverseMap_bijective p.val p.property }
```

`permutationInverse`는 앞에서 구성한 `inverseMap`을 사용하므로 `noncomputable`로 정의한다.
역함수의 두 법칙은 `inverseMap_left`와 `inverseMap_spec`에서 얻는다.

이 세 구성으로 군을 정의하자. 결합법칙과 항등원 법칙에서는 임의의 원소에서 함수값을 계산하며, 역원 법칙에서는 두 역함수 정리를 사용한다.

```savedLean
noncomputable def permutationGroup (A : Type) :
    Group (Permutation A) where
  op := permutationCompose
  id := permutationIdentity A
  inv := permutationInverse

  assoc := by
    intro p q r
    ext x : 2
    rfl

  id_left := by
    intro p
    ext x : 2
    rfl

  id_right := by
    intro p
    ext x : 2
    rfl

  inv_left := by
    intro p
    ext x : 2
    exact inverseMap_left p.val p.property x

  inv_right := by
    intro p
    ext x : 2
    exact inverseMap_spec p.val p.property x
```

`inv_left`에서 남는 등식은 $`p^{-1}(p(x))=x`이고 `inv_right`에서는 $`p(p^{-1}(x))=x`이다. 앞 절의 추상적인 군의 역원 법칙이 함수에서는 역함수의 두 성질에 해당한다.

# 세 문자의 전치
%%%
tag := "group-three-transpositions"
file := "transpositions"
%%%

세 문자는 `Fin 3`의 원소 $`0,1,2`로 나타내자. 두 문자의 위치를 서로 바꾸고 다른 문자는 그대로 두는 순열을 *전치*라고 한다.

먼저 원소 하나를 보내는 함수를 정의한다. $`x=a`이면 $`b`로, $`x=b`이면 $`a`로 보내고 그 밖의 원소는 그대로 둔다.

```savedLean
def swapThree (a b x : Fin 3) : Fin 3 :=
  if x = a then b else if x = b then a else x
```

이 함수는 같은 교환을 두 번 하면 원래 원소로 돌아간다. 이를 증명하려면 원소가 첫째 문자, 둘째 문자, 나머지 문자인 경우를 나누면 된다. 두 문자가 같을 때도 정의한 함수는 항등함수이다.

각 경우의 함수값을 먼저 정리하자.
`h : P`일 때 `ite_eq_left h`는 `if P then a else b`의 값이 `a`라는 등식의 증명이고,
`h : ¬ P`일 때 `ite_eq_right h`는 그 값이 `b`라는 등식의 증명이다.
아래에서는 각 경우의 가정을 이 정리에 넣고 `rw`로 `if` 식을 바꾼다.

```savedLean
theorem swapThree_left (a b : Fin 3) :
    swapThree a b a = b := by
  rw [swapThree, ite_eq_left rfl]

theorem swapThree_right (a b : Fin 3)
    (hba : b ≠ a) :
    swapThree a b b = a := by
  rw [swapThree, ite_eq_right hba, ite_eq_left rfl]

theorem swapThree_other (a b x : Fin 3)
    (hxa : x ≠ a)
    (hxb : x ≠ b) :
    swapThree a b x = x := by
  rw [swapThree, ite_eq_right hxa, ite_eq_right hxb]

theorem swapThree_twice (a b x : Fin 3) :
    swapThree a b (swapThree a b x) = x := by
  by_cases hxa : x = a
  -- x가 a이면 b로 옮겼다가 다시 a로 돌아온다.
  · rw [hxa, swapThree_left]
    by_cases hba : b = a
    · rw [hba, swapThree_left]
    · rw [swapThree_right a b hba]

  -- 나머지는 x가 b인 경우와 어느 쪽도 아닌 경우로 나눈다.
  · by_cases hxb : x = b

    · have hba : b ≠ a := by
        intro h
        apply hxa
        exact hxb.trans h

      rw [hxb, swapThree_right a b hba, swapThree_left]

    · rw [swapThree_other a b x hxa hxb,
        swapThree_other a b x hxa hxb]
```

*정리* 이 교환 함수는 전단사이다.

단사성에서는 $`s(x)=s(y)`의 양변에 같은 교환을 한 번 더 적용하면 $`x=y`를 얻는다. 전사성에서는 주어진 $`y`에 대하여 $`s(y)`를 원소로 택하면 된다.

```savedLean
theorem swapThree_bijective (a b : Fin 3) :
    Bijective
  (swapThree a b) := by
  constructor
  -- 같은 상에 교환을 한 번 더 적용하면 원래 원소가 같다.
  · intro x y hxy
    calc
      x = swapThree a b (swapThree a b x) := by rw
        [swapThree_twice]
      _ = swapThree a b (swapThree a b y) := by rw [hxy]
      _ = y := by rw [swapThree_twice]

  -- y를 한 번 교환한 원소가 y의 원상이다.
  · intro y
    exists (swapThree a b y)
    exact swapThree_twice a b y
```

이제 $`0,1`을 바꾸는 전치와 $`1,2`를 바꾸는 전치를 순열의 원소로 구성한다.

```savedLean
def transposition01 : Permutation (Fin 3) :=
  { val := swapThree 0 1
    property := swapThree_bijective 0 1 }

def transposition12 : Permutation (Fin 3) :=
  { val := swapThree 1 2
    property := swapThree_bijective 1 2 }
```


# 합성 순서와 비가환성
%%%
tag := "group-permutation-noncommutative"
file := "noncommutativity"
%%%

$`p=(0\ 1)`, $`q=(1\ 2)`라고 하자. 이 표기는 괄호 안의 두 문자를 바꾸는 전치를 나타낸다. 합성 $`p\circ q`는 $`0`을 먼저 $`0`으로 보낸 뒤 $`1`로 보내며, $`q\circ p`는 $`0`을 먼저 $`1`로 보낸 뒤 $`2`로 보낸다.

```savedLean
example :
    (permutationCompose transposition01
      transposition12).val 0 = 1 := by
  rfl

example :
    (permutationCompose transposition12
      transposition01).val 0 = 2 := by
  rfl
```

*정리* 세 문자 위의 순열군은 아벨군이 아니다.

아벨군이라고 가정하면 위의 두 합성이 같은 순열이어야 하므로 $`0`에서의 값도 같아야 한다. `indisc`로 순열의 등식에서 함수의 등식을 얻고, 원소 $`0`을 지정하여 함수값의 등식을 얻으면 $`1=2`라는 모순이다.

```savedLean
theorem permutationGroup_three_not_abelian :
    ¬ IsAbelian (permutationGroup (Fin 3)) := by
  intro h
  -- 합성 순서를 바꾸었을 때 원소 0의 상이 달라진다.
  have hMaps := h transposition01 transposition12
  indisc at hMaps with hFunctions
  indisc (0 : Fin 3) at hFunctions with hZero
  indisc at hZero with hValues

  have hBad : 1 = 2 := hValues
  contradiction
```

`hValues`는 두 함수값에 담긴 자연수가 같다는 증명이다.
그 값은 각각 $`1`과 $`2`이므로 `hBad : (1 : Nat) = 2`를 얻고 `contradiction`으로 마친다.

# 순열의 거듭제곱
%%%
tag := "permutation-power-counterexample"
file := "powers"
%%%

앞의 두 전치를 합성한 순열은 $`0\mapsto1\mapsto2\mapsto0`으로 세 문자를 순서대로 옮긴다. 이와 같은 순열을 *3순환*이라고 하며 $`(0\ 1\ 2)`로 나타낸다.

```savedLean
def threeCycle : Permutation (Fin 3) :=
  permutationCompose transposition01 transposition12
example : threeCycle.val 1 = 2 := by rfl
example : threeCycle.val 2 = 0 := by rfl
```

*보기* 일반 군에서는 $`(ab)^2=a^2b^2`라고 할 수 없다. 위의 $`p,q`에 대해서는 $`(pq)^2`가 $`0`을 $`2`로 보내지만 $`p^2q^2`는 $`0`을 그대로 둔다. 두 순열이 같다고 가정하여 그 원소에서 비교하면 모순이다.

```savedLean
theorem permutation_square_op_failure :
    power (permutationGroup (Fin 3))
      (permutationCompose transposition01 transposition12)
        2 ≠
    permutationCompose (power (permutationGroup (Fin 3))
      transposition01 2)
      (power (permutationGroup (Fin 3))
        transposition12 2) := by
  intro h
  -- 두 순열이 같다면 원소 0에서의 함수값도 같아야 한다.
  indisc at h with hFunctions
  indisc (0 : Fin 3) at hFunctions with hZero
  indisc at hZero with hValues

  -- 두 계산값은 각각 2와 0이므로 모순이다.
  have hBad : 2 = 0 := hValues
  contradiction
```

따라서 곱의 거듭제곱을 각 거듭제곱의 곱으로 바꾸려면 앞에서처럼 두 원소가 가환한다는 조건을 확인해야 한다. 순열의 예에서는 함수값을 계산하여 그 가정의 역할을 직접 확인할 수 있다.

# 연습문제
%%%
tag := "group-permutation-exercises"
file := "exercises"
%%%

*문제 1* 전치 `transposition01`의 제곱은 항등순열임을 증명하라.

```savedLean -keep
theorem exercise_transposition_square :
    power (permutationGroup (Fin 3)) transposition01 2 =
      permutationIdentity (Fin 3) := by
  sorry
```

*문제 2* 3순환 `threeCycle`의 세제곱은 항등순열임을 증명하라.

```savedLean -keep
theorem exercise_threeCycle_cube :
    power (permutationGroup (Fin 3)) threeCycle 3 =
      permutationIdentity (Fin 3) := by
  sorry
```

*힌트* `Fin 3`의 원소의 값은 $`0,1,2` 중 하나이다. 각 값에서 순열을 계산하라.

*문제 3* 앞 문제의 결과를 사용하여 `threeCycle`의 역순열은 그 제곱임을 증명하라.

```savedLean -keep
theorem exercise_threeCycle_inverse :
    (permutationGroup (Fin 3)).inv threeCycle =
      power (permutationGroup (Fin 3)) threeCycle 2 := by
  sorry
```


```savedLean
end Course
```

