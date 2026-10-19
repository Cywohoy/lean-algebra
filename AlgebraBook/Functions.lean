import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Sets

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "함수" =>

%%%
tag := "functions"
file := "functions"
%%%

이 절에서는 함수의 정의역과 공역에서 출발하여 상과 역상, 단사·전사·전단사를 다룬다.
앞 절에서 배운 집합의 원소 조건과 함수의 외연성을 사용하면서
상과 전사성에 나타나는 존재명제를 증명하고 사용하는 방법을 익힌다.
이어서 집합에 속하는 원소만 정의역이나 공역으로 삼는 부분타입을 소개하고
합성함수와 역함수의 성질을 증명한다.

```savedComment
함수: 정의역과 공역, 상과 역상, 단사·전사·전단사, 부분타입, 합성함수와 역함수.
집합의 정의와 표기는 앞 절의 AlgebraBook.Sets에서 가져온다.
연습문제의 sorry는 독자가 채울 빈 증명이다.
```

```savedImport
import AlgebraBook.Sets
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample

variable {A B C D : Type}
```

여러 타입 사이의 함수를 다루기 위해 `variable`로 `A`, `B`, `C`, `D`를 미리 선언했다.
Lean은 각 정의나 정리에 사용된 타입만 그 정의나 정리의 인수로 넣는다.

# 정의역과 공역
%%%
tag := "functions-domain-and-codomain"
file := "domain-and-codomain"
%%%

*정의* 집합 $`A`의 각 원소 $`x`에 집합 $`B`의 원소 $`f(x)` 하나를 대응시키는 것을
$`A`에서 $`B`로 가는 *함수*라고 한다.
이때 $`A`를 *정의역*, $`B`를 *공역*이라고 하며 $`f : A \to B`로 나타낸다.

수학에서 함수의 정의역과 공역으로 삼는 대상을 Lean에서는 타입 `A`와 `B`로 나타내고,
함수의 타입을 `A → B`로 쓴다.
이 타입의 함수를 정의하려면 `A`의 모든 원소에 대해 `B`의 값 하나를 정해야 한다.
따라서 `f : A → B`와 `x : A`가 주어지면 `f x : B`를 얻는다.
집합 `S : Set A`에 속하는 원소만 정의역으로 삼는 방법은
{ref "functions-elements"}[집합 위의 함수]에서 다룬다.

*보기* 자연수 $`n`을 $`2n`에 대응시키는 함수를 정의하자.

```savedLean
def double (n : Nat) : Nat := 2 * n
```

`double`의 정의역과 공역은 모두 `Nat`이며 `double 3`의 값은 $`6`이다.
정의역의 자연수를 모두 넣어 보면 함수값으로 $`0, 2, 4, \ldots`를 얻는다.
이 값들을 모은 집합은 공역인 자연수 전체의 부분집합으로, 짝수인 자연수들로 이루어져 있다.

{anchor "functions-identity"}[]`double`은 값을 두 배로 바꾸는 함수이다.
값을 그대로 돌려주는 함수를 항등함수라고 한다.

*정의* 집합 $`A`의 각 원소를 그 자신에 대응시키는 함수를
$`A`의 *항등함수*라고 하며 $`\operatorname{id}_A`로 나타낸다.

```savedLean
def identity (A : Type) : A → A :=
  fun x => x
```

Lean에서는 `identity A`가 $`\operatorname{id}_A`이다.
정의에 따라 `identity A x = x`이므로 이 등식은 `rfl`로 증명한다.

```savedLean
example
    (x : A) :
    identity A x = x := by
  rfl
```

## 함수값과 함수의 같음
%%%
tag := "functions-equality"
%%%

원소의 등식 $`x=y`를 알고 있다면 함수값도 같아서 $`f(x)=f(y)`이다.
앞 절에서 배운 `rw`로 목표의 `x`를 `y`로 바꾸면 이 등식을 증명할 수 있다.

```savedLean
example
    (f : A → B) (x y : A)
    (hxy : x = y) :
    f x = f y := by
  rw [hxy]
```

`rw [hxy]`는 등식 `hxy`에 따라 목표의 `x`를 `y`로 바꾼다.
그 결과 목표가 `f y = f y`가 되면 `rw`가 양변이 같다는 것까지 확인하여 증명을 마친다.

함수의 등식 $`f=g`도 같은 방법으로 사용할 수 있다.
아래에서 `rw [hfg]`로 `f`를 `g`로 바꾸면 목표가 `g x = g x`가 되어 증명이 끝난다.

```savedLean
example
    (f g : A → B)
    (hfg : f = g)
    (x : A) :
    f x = g x := by
  rw [hfg]
```

반대로 모든 원소에서 함수값이 같다는 가정으로 함수의 같음을 보일 때는
앞 절에서 배운 {ref "sets-proving-set-equality"}[`ext`]로 원소별 등식을 보인다.

두 함수가 다름을 보일 때는 값이 다른 원소 하나를 찾으면 된다.
함수가 같다고 가정하면 그 원소에서도 값이 같아야 하므로 모순이 생기기 때문이다.
Lean에서는 함수가 다르다는 명제를 `f ≠ g`, 곧 `¬ (f = g)`로 쓴다.

# 상과 역상
%%%
tag := "functions-images-and-preimages"
file := "images-and-preimages"
%%%

앞의 `double`에서는 자연수 전체의 함수값을 모았다.
이제 정의역의 부분집합 $`S`를 정하고 $`S`에 속하는 원소들의 함수값만 모아 보자.

## 상과 존재명제
%%%
tag := "functions-image"
%%%

*정의* 함수 $`f : A \to B`와 집합 $`S \subseteq A`에 대하여
$`S`의 원소들의 함수값을 모은 집합을 $`S`의 *상*이라고 하며 $`f(S)`로 나타낸다.
즉, $`f(S) = \{f(x) : x \in S\}`이다.
여기서 $`f(S)`는 원소 하나에서의 함수값 $`f(x)`와 구별해야 한다.
함수 `f : A → B`는 `A`의 원소를 받으므로 집합 `S : Set A`를 그대로 인수로 넣을 수 없다.
집합의 각 원소에 `f`를 적용한 값들을 모으는 별도의 정의가 필요하다.

$`y \in f(S)`라는 것은 $`x \in S`이고 $`f(x) = y`인 원소 $`x`가 존재한다는 뜻이다.
따라서 상의 원소 조건은 두 조건의 논리곱과 존재명제 `∃ x, ...`로 나타낸다.

```savedLean
def image (f : A → B) (S : Set A) : Set B :=
  fun y => ∃ x, x ∈ S ∧ f x = y
```

정의역 전체의 상 $`f(A)`를 나타낼 때는 `S`에 전체집합을 넣어 `image f (whole A)`로 쓴다.

*보기* $`6`은 함수 `double`의 상에 속한다.
실제로 자연수 $`3`은 정의역에 속하고 $`\operatorname{double}(3) = 6`이다.

목표를 정의에 따라 펼치면 `∃ n, n ∈ whole Nat ∧ double n = 6`이다.
이런 존재명제는 조건을 만족하는 원소를 제시하여 증명하며
전술 `exists 3`으로 원소 `n`을 $`3`으로 택할 수 있다.

```savedLean
example :
    6 ∈ image double (whole Nat) := by
  exists 3
```

원소를 택한 뒤 확인할 조건은 `3 ∈ whole Nat`와 `double 3 = 6`이다.
첫째 조건은 전체집합의 정의로, 둘째 조건은 계산으로 확인되므로 이 예제에서는 `exists`가 증명까지 마친다.

{anchor "functions-image-monotonicity"}[]*정리* $`S \subseteq T`이면 $`f(S) \subseteq f(T)`이다.

*증명* 임의의 원소 $`y \in f(S)`를 택하자.
상의 정의에 따라 $`x \in S`이고 $`f(x) = y`인 원소 $`x`가 존재한다.
$`S \subseteq T`에 따라 이 원소는 $`T`에도 속하므로 $`y \in f(T)`이다.

Lean에서는 먼저 `intro y hy`로 임의의 원소 `y`와 가정 `hy : y ∈ image f S`를 도입한다.
이 가정의 명제를 정의에 따라 펼치면 `∃ x, x ∈ S ∧ f x = y`이므로
`hy`는 조건에 맞는 원소가 존재한다는 증명이다.

`rcases`를 쓰면 존재명제의 증명에서 원소와 조건의 증명을 꺼낼 수 있다.
아래의 `rcases hy with ⟨x, hxS, hxy⟩`는 원소를 `x`로 두고
`x ∈ S`와 `f x = y`의 증명에 각각 `hxS`, `hxy`라는 이름을 붙인다.
이 패턴에서는 먼저 존재명제에서 원소와 그 원소에 관한 증명을 꺼내고,
그 증명에 담긴 논리곱을 다시 두 조건으로 나눈다.
여기서 `x`는 임의로 정한 원소가 아니라 가정 `hy`가 존재를 보장하는 원소이다.
이후의 추론에서는 함께 얻은 두 조건을 사용할 수 있다.
여기서 `⟨`와 `⟩`는 각각 `\<`, `\>`로 입력한다.

```savedLean
theorem image_mono (f : A → B) (S T : Set A)
    (hST : S ⊆ T) :
    image f S ⊆ image f T := by
  intro y hy
  rcases hy with ⟨x, hxS, hxy⟩

  -- 같은 원소 x를 더 큰 집합 T에서도 사용할 수 있다.
  exists x
  constructor
  · apply hST
    exact hxS

  · exact hxy
```

이제 `y ∈ image f T`를 보이기 위해 `exists x`로 같은 원소를 택하면
목표 `x ∈ T ∧ f x = y`가 남는다.
`constructor`로 두 조건을 나누고 첫째 조건에는 포함 관계 `hST`와 가정 `hxS`를 사용한다.
둘째 조건은 `rcases`에서 얻은 등식 `hxy`로 증명한다.

{anchor "functions-not-in-image"}[]상에 속하지 않음을 보일 때는 앞에서 배운 부정의 증명 방법을 사용하자.
상에 속한다고 가정한 뒤 조건에 맞는 원소를 꺼내 모순을 얻으면 된다.

*보기* 모든 자연수를 $`0`에 대응시키는 함수의 상에는 $`1`이 속하지 않는다.
상에 속한다고 가정하면 함수값이 $`1`인 자연수 $`n`이 존재하지만
함수의 정의에 따라 그 값은 $`0`이므로 $`0=1`이라는 모순이 생긴다.

```savedLean
example :
    1 ∉ image (fun _ : Nat => 0) (whole Nat) := by
  intro hy
  rcases hy with ⟨n, hn, hEq⟩
  contradiction
```

`intro hy`로 상에 속한다고 가정하면 목표는 `False`가 된다.
`rcases`로 자연수 `n`과 `hn : n ∈ whole Nat`, 함수값에 관한 등식 `hEq`를 얻는다.
이때 `hEq`는 정의에 따라 `0 = 1`의 증명이므로 `contradiction`으로 모순을 얻는다.

앞의 `double`에서도 $`5`가 상에 속한다고 가정하면 $`2n=5`인 자연수 $`n`을 얻게 된다.
이 등식에서 모순을 얻는 방법은 {ref "preliminaries-double-image"}[짝수와 함수의 상]에서 다룬다.

## 역상
%%%
tag := "functions-preimage"
%%%

상을 구할 때는 정의역의 집합에서 출발하여 그 원소들의 함수값을 모았다.
이번에는 공역의 집합을 먼저 정하고 함수값이 그 집합에 속하는 정의역의 원소들을 모아 보자.

*정의* 함수 $`f : A \to B`와 집합 $`T \subseteq B`에 대하여
함수값이 $`T`에 속하는 원소들을 모은 집합을 $`T`의 *역상*이라고 하며 $`f^{-1}(T)`로 나타낸다.
즉, $`f^{-1}(T) = \{x \in A : f(x) \in T\}`이다.

역상에 속한다는 조건은 `f x ∈ T`이므로 이 술어로 집합을 정의하자.

```savedLean
def preimage (f : A → B) (T : Set B) : Set A :=
  fun x => f x ∈ T
```

*보기* 함수 `double`에 의한 양의 자연수의 집합의 역상에는 $`1`이 속한다.
실제로 $`\operatorname{double}(1)=2>0`이므로 역상의 원소 조건을 만족한다.

```savedLean
example :
    1 ∈ preimage double positives := by
  expand
  expand
  expand
  decide
```

`x ∈ preimage f T`는 `f x ∈ T`를 뜻하므로 이 예제의 목표는 `double 1 ∈ positives`, 곧 `0 < 2`이다.
`expand`를 거듭 사용하여 역상과 양수 조건의 정의를 펼친 뒤 `decide`로 부등식을 확인한다.

역상 $`f^{-1}(T)`를 정의하려면 함수 $`f`와 공역의 부분집합 $`T`만 있으면 된다.
기호에 $`-1`이 들어 있어도 역함수를 구할 필요는 없으며
위와 같이 원래 함수의 값이 $`T`에 속하는지만 확인한다.

{anchor "functions-preimage-of-image"}[]집합 $`S`의 상 $`f(S)`를 구한 뒤 다시 역상 $`f^{-1}(f(S))`를 구하면 어떤 집합을 얻을까?
$`x\in S`이면 $`f(x)\in f(S)`이므로 $`x\in f^{-1}(f(S))`이다.
따라서 원래 집합의 원소는 모두 이 역상에 들어 있다.

*보기* 모든 함수 $`f`와 정의역의 부분집합 $`S`에 대하여 $`S\subseteq f^{-1}(f(S))`이다.

```savedLean
theorem subset_preimage_image (f : A → B) (S : Set A) :
    S ⊆ preimage f (image f S) := by
  intro x hx
  exists x
```

`intro x hx` 뒤의 목표는 `f x ∈ image f S`이며
정의를 펼치면 `∃ y, y ∈ S ∧ f y = f x`이다.
`exists x`로 원소를 택하면 `hx`와 등식 `f x = f x`로 두 조건이 확인된다.

*보기* 위 포함 관계에서 두 집합이 항상 같지는 않다.
모든 자연수를 $`0`에 보내는 함수와 집합 $`S=\{0\}`을 생각하자.
이때 $`f(S)=\{0\}`이고 모든 자연수의 함수값이 $`0`이므로 $`f^{-1}(f(S))=\mathbb{N}`이다.
특히 원래 집합에 없던 $`1`도 역상에 속한다.

```savedLean
example :
    1 ∈ preimage (fun _ : Nat => 0)
    (image (fun _ : Nat => 0) (fun n => n = 0)) := by
  exists 0
```

$`f(1)`이 $`f(S)`에 속함을 보이려면 $`S` 안에서 같은 함수값을 갖는 원소를 찾으면 된다.
그 원소로 $`0`을 택하면 $`0\in S`이고 $`f(0)=f(1)`이다.
원래 집합 밖의 원소도 집합 안의 원소와 같은 함수값을 가지면 이 역상에 들어간다.

# 단사, 전사, 전단사
%%%
tag := "functions-mapping-properties"
file := "mapping-properties"
%%%

서로 다른 원소가 서로 다른 함수값을 갖는 조건을 *단사성*이라고 하고
공역의 모든 원소가 함수값으로 나타나는 조건을 *전사성*이라고 한다.
이 두 성질을 차례로 정의하고 항등함수 등의 예에서 확인하자.

## 단사함수
%%%
tag := "functions-injectivity"
%%%

*정의* 함수 $`f : A \to B`가 임의의 $`x, y \in A`에 대하여
$`f(x) = f(y)`이면 $`x = y`라는 조건을 만족할 때
$`f`를 *단사함수*라고 한다.

이는 서로 다른 원소들이 서로 다른 값에 대응한다는 조건이다.
앞에서 $`x=y`이면 $`f(x)=f(y)`임을 보였으므로
단사함수에서는 $`x=y`와 $`f(x)=f(y)`가 서로 동치이다.

```savedLean
def Injective : (A → B) → Prop :=
  fun f => ∀ x y, f x = f y → x = y
```

`Injective`는 함수 `f`에 “`f`가 단사이다”라는 명제를 대응시키는 술어이다.
인수가 `A → B` 타입의 함수이므로 술어 전체의 타입은 `(A → B) → Prop`이다.

*보기* 항등함수는 단사이다.
$`\operatorname{id}_A(x) = \operatorname{id}_A(y)`라는 가정이 곧 $`x = y`이므로
이 가정을 그대로 사용하면 된다.

```savedLean
theorem identity_injective (A : Type) :
    Injective (identity A) := by
  intro x y hxy
  exact hxy
```

*보기* 모든 자연수를 $`0`에 대응시키는 함수는 단사가 아니다.
이 함수가 단사라고 가정하면 $`0`과 $`1`에서 함수값이 같다는 사실로부터 $`0 = 1`을 얻어 모순이다.

```savedLean
example :
    ¬ Injective (fun _ : Nat => 0) := by
  intro h
  have h01 : 0 = 1 := by
    apply h 0 1
    rfl

  contradiction
```

`have`로 `0 = 1`을 보이는 부분을 시작한 뒤 `apply h 0 1`을 쓰면
단사성의 전제인 두 함수값의 등식이 새 목표가 된다.
두 값은 모두 $`0`이므로 `rfl`로 이 목표를 해결하여 `h01 : 0 = 1`을 얻는다.
바깥의 목표 `False`로 돌아오면 `contradiction`이 이 등식에서 모순을 얻어 증명을 마친다.

*보기* 함수 $`\operatorname{double}(n)=2n`은 단사이다.
$`2x=2y`에서 양변의 양수인 인수 $`2`를 소거하면 $`x=y`를 얻는다.
자연수의 이 소거법칙은 `Nat.mul_left_cancel`로 사용할 수 있다.
이 정리는 `0 < n`과 `n * x = n * y`의 증명을 받아 `x = y`의 증명을 제공한다.

```savedLean
theorem double_injective : Injective double := by
  intro x y hxy
  apply Nat.mul_left_cancel (n := 2) (by decide)
  exact hxy
```

여기서는 공통 인수 `n`을 `2`로 지정하고 `by decide`로 양수 조건을 확인했다.
남은 목표는 `2 * x = 2 * y`이며 `hxy`가 바로 이 등식의 증명이다.

앞에서는 상의 역상이 원래 집합보다 커질 수 있음을 보았다.
그 예제에서는 원래 집합 밖의 원소도 집합 안의 원소와 같은 함수값을 가졌다.
함수가 단사이면 이런 일이 없으므로 다음 등식을 얻는다.

*정리* $`f`가 단사이면 모든 집합 $`S`에 대하여 $`f^{-1}(f(S))=S`이다.

*증명* $`x\in f^{-1}(f(S))`이면 어떤 $`y\in S`에 대하여 $`f(y)=f(x)`이다.
단사성에 따라 $`y=x`이므로 $`x\in S`이다.
반대 포함 관계는 앞에서 증명한 `subset_preimage_image`이다.

```savedLean
theorem preimage_image_of_injective (f : A → B)
    (hf : Injective f)
    (S : Set A) :
    preimage f (image f S) = S := by
  apply set_eq_of_subset
  · intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    have hyx : y = x := by
      exact hf y x hxy

    rw [← hyx]
    exact hy

  · exact subset_preimage_image f S
```

`hx`는 `∃ y, y ∈ S ∧ f y = f x`라는 존재명제의 증명이므로
`rcases`로 원소 `y`, 원소 조건 `hy`, 함수값의 등식 `hxy`를 얻는다.
`hf`로 얻은 `hyx`를 오른쪽에서 왼쪽으로 사용하면 목표 `x ∈ S`가 `y ∈ S`로 바뀐다.
`rw [← hyx]`의 `←`는 이처럼 등식을 반대 방향으로 사용하라는 뜻이며 `\l`로 입력한다.

*보기* $`\{2,3\}`의 상은 $`\{4,6\}`이다. 이 상의 역상을 구하면 원래 집합 $`\{2,3\}`을 얻는다.
두 번째 사실은 `double`의 단사성에서 바로 따른다.
앞 절의 `twoThree`와 방금 증명한 `double_injective`를 위 정리에 사용하자.

```savedLean
example :
    preimage double (image double twoThree) = twoThree := by
  exact preimage_image_of_injective double
    double_injective twoThree
```

이 증명은 역상의 원소 조건을 다시 풀지 않고 단사함수에 관한 일반 정리를 사용한다.

## 전사함수
%%%
tag := "functions-surjectivity"
%%%

앞의 `double`처럼 상이 공역의 일부인 함수도 있고 항등함수처럼 상과 공역이 같은 함수도 있다.
두 번째 경우를 나타내는 조건이 전사성이다.

*정의* 함수 $`f : A \to B`에 대하여
모든 $`y \in B`가 어떤 $`x \in A`의 함수값 $`f(x)`일 때
$`f`를 *전사함수*라고 한다.

Lean에서는 공역의 원소 `y`를 먼저 두고 `f x = y`인 원소 `x`의 존재를 요구한다.
따라서 `∀ y, ∃ x, ...`의 순서로 쓰며 원소 `x`는 `y`에 따라 달라질 수 있다.
예를 들어 자연수의 항등함수에서는 $`y=0`에 대해 $`x=0`을,
$`y=1`에 대해 $`x=1`을 택한다.
순서를 바꾸어 `∃ x, ∀ y, f x = y`라고 쓰면
하나의 `x`에서 얻는 함수값이 공역의 모든 원소와 같아야 하므로 전혀 다른 조건이 된다.

```savedLean
def Surjective : (A → B) → Prop :=
  fun f => ∀ y, ∃ x, f x = y
```

*보기* 항등함수는 전사이다.
임의의 원소 $`y \in A`에 대하여 $`x = y`를 택하면
$`\operatorname{id}_A(x) = y`이므로 원하는 원소가 존재한다.

```savedLean
theorem identity_surjective (A : Type) :
    Surjective (identity A) := by
  intro y
  exists y
```

`intro y` 이후의 목표는 `∃ x, identity A x = y`이므로
`exists y`로 원소 `x`를 `y`로 선택한다.
남은 등식은 정의에 따라 `y = y`가 되므로 이 단계에서 증명도 끝난다.

## 전단사함수
%%%
tag := "functions-bijectivity"
%%%

이제 단사성과 전사성을 함께 만족하는 함수를 살펴보자.

*정의* 단사이면서 전사인 함수를 *전단사함수*라고 한다.

전사성에 따라 공역의 각 원소 $`y`에 대해 $`f(x)=y`인 원소 $`x`가 존재하고
단사성에 따라 그러한 원소는 하나뿐이다.
Lean에서는 두 조건을 논리곱으로 묶어 전단사성을 정의한다.

```savedLean
def Bijective : (A → B) → Prop :=
  fun f => Injective f ∧ Surjective f
```

```savedLean -show
namespace Bijective

theorem injective
    {f : A → B} (hf : Bijective f) : Injective f :=
    hf.left

theorem surjective
    {f : A → B} (hf : Bijective f) : Surjective f :=
    hf.right

end Bijective
```

`hf : Bijective f`가 주어지면 `hf.injective`로 단사성의 증명을,
`hf.surjective`로 전사성의 증명을 꺼내 사용할 수 있다.

*보기* 항등함수는 전단사이다.
단사성과 전사성을 앞에서 각각 증명했으므로 `constructor`로 나뉜 목표에 두 정리를 사용하면 된다.

```savedLean
theorem identity_bijective (A : Type) :
    Bijective (identity A) := by
  constructor
  · exact identity_injective A
  · exact identity_surjective A
```

# 집합 위의 함수
%%%
tag := "functions-elements"
file := "elements"
%%%

앞에서 정의한 `double`은 자연수를 받아 자연수를 돌려준다.
그런데 함수값 $`2n`은 언제나 짝수이므로 공역을 짝수인 자연수들의 집합으로 정할 수도 있다.
이처럼 정의역이나 공역을 집합으로 정할 때 어떤 조건을 확인해야 하는지 살펴보고
그 조건을 함수의 타입에 반영하는 방법을 익히자.

{anchor "functions-codomain-condition"}[]짝수인 자연수들의 집합을 $`E`라고 하자.
$`n\mapsto 2n`을 함수 $`\mathbb{N}\to E`로 정의하려면
각 자연수 $`n`에 대하여 함수값 $`2n`이 $`E`에 속함을 보여야 한다.
짝수의 정의는 어떤 자연수의 두 배로 나타낼 수 있다는 것이므로
여기서는 그 자연수로 $`n`을 택하면 된다.

Lean에서는 우선 앞에서 정의한 `double : Nat → Nat`을 사용하고
함수값이 짝수 집합에 속한다는 사실을 따로 증명하자.
짝수 집합을 `evens`로 정의하면 증명할 명제는 `double n ∈ evens`이다.

```savedLean
def evens : Set Nat := fun n => ∃ k : Nat, n = 2 * k
theorem double_mem_evens (n : Nat) :
    double n ∈ evens := by
  exists n
```

목표의 원소 조건은 `∃ k : Nat, double n = 2 * k`이다.
`exists n`으로 $`k=n`을 택하면 `double`의 정의에 따라 등식이 성립한다.
이제 `double`은 함수값을 정하고 `double_mem_evens`는 그 값이 `evens`에 속함을 보인다.

{anchor "functions-domain-condition"}[]정의역이 부분집합이면 그 집합의 원소라는 조건도 사용할 수 있다.
예를 들어 양의 자연수의 집합 $`S=\{n\in\mathbb{N}:0<n\}`에서
$`T=\{m\in\mathbb{N}:2<m\}`로 가는 함수를 $`n\mapsto n+2`로 정의하자.
$`n\in S`이면 $`0<n`이므로 양변에 $`2`를 더하여 $`2<n+2`를 얻는다.
따라서 함수값은 $`T`에 속한다.
여기서 정의역의 조건을 빼면 $`n=0`일 때 함수값이 $`2`여서 $`T`에 속하지 않는다.

앞에서 정의한 `positives`가 $`S`에 해당한다.
$`T`를 `aboveTwo`로 정의하고 먼저 모든 자연수에서 $`n+2`를 계산하는 함수 `shiftTwo`를 만들자.
그 값이 `aboveTwo`에 속한다는 정리에는 `n ∈ positives`를 가정으로 넣는다.

```savedLean
def aboveTwo : Set Nat := fun n => 2 < n
def shiftTwo (n : Nat) : Nat := n + 2
theorem shiftTwo_mem_aboveTwo (n : Nat)
    (hn : n ∈ positives) :
    shiftTwo n ∈ aboveTwo := by
  apply Nat.add_lt_add_right (k := 2)
  exact hn
```

목표는 정의에 따라 `2 < n + 2`이고 가정 `hn`은 `0 < n`의 증명이다.
앞서 배운 `Nat.add_lt_add_right`를 더할 수 `2`와 함께 적용하면
목표가 `0 < n`으로 바뀌므로 `exact hn`으로 증명을 마친다.

일반적으로 $`f:A\to B`와 집합 $`S\subseteq A`, $`T\subseteq B`가 주어졌을 때
$`f`의 값을 이용하여 $`S`에서 $`T`로 가는 함수를 만들려면
$`x\in S`일 때 $`f(x)\in T`임을 보여야 한다.
지금처럼 함수와 이 조건의 증명을 따로 적을 수도 있고
각 원소를 원소 조건의 증명과 묶어 정의역과 공역에 사용할 타입을 만들 수도 있다.

## 부분타입
%%%
tag := "functions-subtypes"
%%%

앞에서 보인 `double n ∈ evens`를 함수의 타입에도 담아 보자.
수학에서는 $`\mathbb{N} \to E`처럼 공역에 짝수의 집합 $`E`를 적지만,
Lean에서 다음과 같이 적으면 오류가 난다.

```tryLean +error -keep
def doubleToEvensAttempt : Nat → evens := double
```

`evens`는 자연수의 원소 조건을 나타내는 술어 `Nat → Prop`이다.
함수의 화살표 오른쪽에는 함수값의 타입이 필요하므로 이 술어를 그대로 넣을 수 없다.
짝수라는 조건을 만족하는 자연수들을 하나의 타입으로 모으려면
자연수 값과 그 값이 짝수라는 증명을 함께 담으면 된다.

정의역이 양의 자연수의 집합이라는 조건을 함수의 타입에 반영하려면
자연수 `n : Nat`와 양수라는 증명 `hn : n ∈ positives`를 함께 받으면 된다.
이 둘을 하나로 묶으면 양의 자연수를 인수 하나로 전달할 수 있으며
함수값에도 같은 방법으로 값과 공역에 속한다는 증명을 담을 수 있다.

Lean의 *부분타입* `{x : A // P x}`는 원소 `x : A`와
그 원소가 조건 `P x`를 만족한다는 증명을 함께 담는다.
집합 `S`의 원소 조건을 넣어 다음과 같이 정의하자.

```savedLean
def Elem {A : Type _} (S : Set A) := {x : A // x ∈ S}
```

```savedLean -show
attribute [implicit_reducible] Elem
```

앞에서 살펴본 `a ∈ S`는 `a : A`와 `S : Set A`가 주어지면 쓸 수 있는 명제이다.
이를 쓰는 데에는 `a`가 실제로 `S`에 속한다는 증명이 필요하지 않으며
그 명제가 성립함을 보이려면 `ha : a ∈ S`와 같은 증명을 제시해야 한다.

부분타입에서는 원소와 이 증명을 함께 담는다.
따라서 `a`를 값으로 갖는 `Elem S`의 원소를 만들려면 `ha : a ∈ S`가 필요하다.
`a ∈ S`는 참인지 거짓인지 살펴볼 명제이고, `s : Elem S`는 값 `s`가 어떤 타입에 속하는지 밝히는 표기이다.
후자의 `s`에는 이미 집합에 속한다는 증명이 들어 있다.

아래의 `{ val := 값, property := 증명 }` 표기에서는
`val`에 원소를 적고 `property`에 그 원소가 집합에 속한다는 증명을 적는다.
반대로 `s : Elem S`가 주어지면 `s.val : A`로 원소를 꺼내고
`s.property : s.val ∈ S`로 그 원소가 집합에 속함을 확인한다.
`//`는 슬래시 두 개를 그대로 입력한다.

```savedLean
def functions_element_from_membership
    (S : Set A) (a : A)
    (ha : a ∈ S) :
    Elem S :=
  { val := a, property := ha }
```

여기서 `val := a`로 원소를 정하고 `property := ha`로 그 원소가 `S`에 속한다는 증명을 담는다.
예를 들어 `0 ∈ positives`라는 명제는 쓸 수 있지만
값이 $`0`인 `Elem positives`의 원소를 만들려면 거짓인 명제 `0 < 0`의 증명이 필요하다.
이 타입을 정의역으로 삼은 `Elem positives → B`의 함수에는
자연수 값과 양수라는 증명을 함께 갖춘 원소를 인수로 넣는다.

*보기* $`1`은 양의 자연수이다.
먼저 `1 ∈ positives`의 원소 조건인 $`0<1`을 증명하고
그 증명에 `one_positive`라는 이름을 붙이자.

```savedLean
theorem one_positive : 0 < 1 := by decide
```

이제 자연수 값 $`1`과 이 증명을 묶어 `Elem positives`의 원소를 만들자.
`val`에는 `1`을, `property`에는 방금 얻은 증명 `one_positive`를 넣는다.
`0 < 1`과 `1 ∈ positives`는 정의상 같은 명제이므로 이 증명을 그대로 사용할 수 있다.

```savedLean
def oneInPositives : Elem positives :=
  { val := 1, property := one_positive }
```

값을 `val := 1`로 정했으므로 `oneInPositives.val`은 $`1`이다.
이를 등식으로 확인하면 다음과 같다.

```savedLean
example :
    oneInPositives.val = 1 := by
  rfl
```

{anchor "functions-subtype-maps"}[]이제 앞의 두 함수를 원소 조건까지 포함한 타입으로 나타내자.
자연수에서 짝수 집합으로 가는 함수의 타입은 `Nat → Elem evens`이다.
각 `n : Nat`에 대해 값 `double n`과 그 값이 짝수라는 증명 `double_mem_evens n`을 함께 돌려주면 된다.
증명 단계를 직접 적을 때는 다음과 같이 `property := by` 아래에 적는다.

```savedLean
def doubleToEvens (n : Nat) : Elem evens :=
  { val := double n
    property := by
      exact double_mem_evens n }
```

양의 자연수에서 $`2`보다 큰 자연수로 가는 함수는
`Elem positives → Elem aboveTwo`로 정의한다.
이때 인수 `s`에서 자연수 값 `s.val`과 양수라는 증명 `s.property`를 꺼내
앞의 정리 `shiftTwo_mem_aboveTwo`에 함께 넣는다.

```savedLean
def shiftTwoOnPositives (s : Elem positives) :
    Elem aboveTwo :=
  { val := shiftTwo s.val
    property := by
      exact shiftTwo_mem_aboveTwo s.val s.property }

example :
    (shiftTwoOnPositives oneInPositives).val = 3 := by
  rfl
```

`shiftTwoOnPositives`는 `s.property`로 주어진 정의역의 조건을 사용하여
함수값이 공역에 속한다는 증명을 만든다.
`oneInPositives`를 넣으면 값 $`1`과 $`0<1`의 증명이 함께 전달되며
함수값에는 $`3`과 $`2<3`의 증명이 담긴다.

일반적인 집합 $`S`, $`T`에 대해서도 함수의 타입을 `Elem S → Elem T`로 쓸 수 있다.
인수에서 `S`의 원소 값과 원소 조건의 증명을 꺼내고
함수값을 만들 때는 `T`의 원소 값과 원소 조건의 증명을 함께 제시한다.

# 원소의 비교와 유한한 번호
%%%
tag := "functions-element-equality"
file := "element-comparison"
%%%

부분타입의 원소에는 값과 증명이 함께 들어 있다.
예를 들어 양수라는 사실을 서로 다른 방법으로 증명하여 만든 두 원소가
모두 값 $`1`을 갖는다면 이 둘을 같은 양의 자연수로 취급해야 한다.

Lean에서는 같은 명제의 증명들을 같게 취급한다.
따라서 `s t : Elem S`의 값이 같으면 두 원소에 담긴 증명도 같은 명제의 증명으로 비교할 수 있다.
그 증명들은 Lean에서 같게 취급하므로 원소의 등식을 보일 때는 값만 비교하면 된다.
이 성질에 따라 값의 등식 `s.val = t.val`에서 원소의 등식 `s = t`를 얻는 정리가 `Subtype.ext`이다.
이 성질은 교재의 `ext`에 연결되어 있으므로
부분타입의 원소도 같은 전술로 비교할 수 있다.

```savedLean -show
@[ext] theorem elem_ext {A : Type _} {S : Set A} {s t : Elem S}
    (h : s.val = t.val) : s = t := by
  apply Subtype.ext
  exact h

@[simp] theorem elem_eq_iff {S : Set A}
    (s t : Elem S) :
    s = t ↔ s.val = t.val := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply elem_ext
    exact h

attribute [ample_norm_hyp] elem_eq_iff
```

`s = t`라는 목표에 `ext`를 사용하면 새 목표는 `s.val = t.val`이다.
거꾸로 `h : s = t`가 주어졌을 때는
`indisc at h`로 두 원소의 값이 같음을 얻는다.

```savedLean
example
    (S : Set A) (s t : Elem S)
    (h : s = t) :
    s.val = t.val := by
  indisc at h
  exact h
```

위 증명에서는 가정이 `h : s.val = t.val`로 바뀌므로 `exact h`로 증명을 마친다.
같은 값 비교를 사용하면 원소를 꺼내는 함수 `fun s => s.val`이 단사임을 보일 수 있다.

```savedLean
theorem elem_val_injective (S : Set A) :
    Injective (fun s : Elem S => s.val) := by
  intro s t hst
  ext
  exact hst
```

*보기* 앞에서 만든 `doubleToEvens : Nat → Elem evens`는 전단사이다.
자연수를 두 배로 하는 규칙은 `double`과 같으며 공역을 짝수 집합으로 정했다.
단사성에는 이미 증명한 `double_injective`를 사용하면 된다.
또한 공역의 원소 $`y`는 짝수이므로 $`y=2n`인 자연수 $`n`이 존재하며,
이 $`n`을 택하면 함수값이 $`y`가 되어 전사성도 얻는다.

```savedLean
theorem doubleToEvens_bijective :
    Bijective doubleToEvens := by
  constructor
  · intro x y hxy
    apply double_injective
    indisc at hxy
    exact hxy

  · intro y
    -- y의 원소 조건에서 y = 2n인 자연수 n을 얻는다.
    unpack y.property with ⟨n, hn⟩
    exists n
    ext
    exact hn.symm
```

단사성에서는 부분타입 원소의 등식을 값의 등식으로 바꾸어 `double_injective`에 사용한다.
전사성에서 `y.property`는 `∃ n, y.val = 2 * n`의 증명이다.
따라서 `exists n`으로 원소를 정하고 `ext`로 값만 비교하면
`2 * n = y.val`이 남으며 이는 `hn`의 양변을 바꾼 등식이다.
뒤의 {ref "cardinality-countable-sets"}[가산무한집합]에서는 이 전단사를 사용하여
자연수 전체와 짝수 집합의 크기를 비교한다.

## 유한한 번호: Fin
%%%
tag := "functions-fin"
%%%

함수의 정의역을 번호 $`0,1,\ldots,n-1`로 제한하려면 그 번호들로 이루어진 타입이 필요하다.
이 번호들의 집합은 $`\{k\in\mathbb{N}:k<n\}`이며
Lean에서는 이에 대응하는 타입으로 `Fin n`을 사용한다.
따라서 `Fin 3`의 원소가 나타내는 자연수는 $`0`, $`1`, $`2`이다.

Lean에 미리 정의된 `Fin`의 핵심 내용은 다음과 같다.
`structure`는 여러 자료를 하나로 묶는 선언이며
여기서는 자연수 `val`과 그 값이 `n`보다 작다는 증명 `isLt`를 묶는다.

```
structure Fin (n : Nat) where
  val : Nat
  isLt : val < n
```

즉 `Fin n`은 앞에서 본 부분타입 `{k : Nat // k < n}`과 마찬가지로
자연수와 범위 조건의 증명을 함께 담는다.
`i : Fin n`에서 `i.val : Nat`로 그 자연수를 꺼내고
`i.isLt : i.val < n`으로 범위 조건의 증명을 얻는다.
부분타입에서 조건의 증명을 꺼낼 때 쓴 `.property`에 해당하는 이름이 여기서는 `.isLt`이다.

가령 $`2<3`이므로 자연수 $`2`와 이 부등식의 증명을 묶어 `Fin 3`의 원소를 만들 수 있다.
부분타입에서와 같이 필드 이름을 적어 자연수 값과 범위 조건의 증명을 제시하자.

```savedLean
def cardinality_fin_three_last : Fin 3 :=
  { val := 2, isLt := by decide }
```

이 정의에서는 `Fin 3`의 원소 하나를 구성한다.
`val := 2`로 자연수 값을 정하고 `isLt := by decide`로 범위 조건 `2 < 3`을 확인한다.

`Fin 0`에는 $`0`보다 작은 자연수가 없으므로 원소가 없다.
따라서 `i : Fin 0`이라는 가정이 생기면 `Fin.elim0 i`로 모순에서 임의의 결론을 얻는다.
이는 앞에서 `False.elim`을 사용한 것과 같은 원리이다.


*보기* 같은 자연수 값을 갖는 두 번호는 같다. 부분타입에서와 같이 `ext`로 값의 등식을 보이면 된다.

```savedLean
example (i j : Fin n)
    (h : i.val = j.val) :
    i = j := by
  ext
  exact h
```

번호의 범위를 바꾸거나 번호를 하나씩 이동하는 방법은
{ref "cardinality-fin-conversions"}[자연수와 유한한 번호]에서 다룬다.

# 함수의 제한
%%%
tag := "functions-restriction"
file := "restrictions"
%%%

함수 $`f : A\to B`를 집합 $`S\subseteq A`의 원소에만 적용하는 함수를
$`f`의 $`S`에 대한 *제한*이라고 한다.
앞에서 `shiftTwoOnPositives`의 인수로 양의 자연수만 받았듯이,
일반적인 함수도 부분타입을 사용하여 정의역을 제한할 수 있다.
`s : Elem S`에서 원래 원소 `s.val`을 꺼내 `f`에 넣으면 이 함수를 얻는다.

```savedLean
def restrict (f : A → B) (S : Set A) : Elem S → B :=
  fun s => f s.val
example :
    restrict double positives oneInPositives = 2 := by
  rfl
```

`restrict double positives`는 양의 자연수만 받아 그 두 배를 자연수로 돌려준다.
`oneInPositives`의 자연수 값이 $`1`이므로 위 함수값은 $`2`이다.

*정리* 단사함수의 정의역을 제한한 함수도 단사이다.

*증명* 제한한 함수의 두 함수값이 같으면 원래 함수의 단사성으로 두 원소 값이 같다.
그러므로 두 부분타입의 원소도 같다.

```savedLean
theorem restrict_injective (f : A → B) (S : Set A)
    (hf : Injective f) :
    Injective (restrict f S) := by
  intro s t hst
  ext
  apply hf s.val t.val
  exact hst
```

`ext`로 원소 값을 비교한 뒤 `apply hf s.val t.val`을 쓰면 목표는 `f s.val = f t.val`이다.
이는 `hst`에서 `restrict`의 정의를 펼친 명제이므로 `exact hst`로 증명을 마친다.

## 공역의 제한
%%%
tag := "functions-codomain-image"
%%%

전사성은 공역의 모든 원소가 함수값으로 나타난다는 조건이다.
따라서 함수값은 그대로 두고 공역을 함수의 상으로 바꾸면 전사함수를 얻는다.
이때 상은 집합이므로 함수의 공역에는 그 원소 타입을 사용하자.

*보기* 함수 $`f:A\to B`로부터 $`A`에서 $`f(A)`로 가는 전사함수를 만들 수 있다.

```savedLean
def toImage (f : A → B) (x : A) :
    Elem (image f (whole A)) :=
  { val := f x
    property := by
      exists x }

theorem toImage_surjective (f : A → B) :
    Surjective (toImage f) := by
  intro y
  rcases y.property with ⟨x, hx, hxy⟩
  exists x
  ext
  exact hxy
```

`val := f x`는 함수값을 정하고 `property`는 이 값이 상에 속함을 증명한다.
이 원소 조건은 존재명제이므로 `exists x`로 원소 `x`를 제시한다.
`x ∈ whole A`와 `f x = f x`는 바로 확인되므로 함수값의 구성이 끝난다.

전사성 증명의 `y`는 상의 원소와 그 조건의 증명을 함께 담는다.
따라서 `y.property`는 `∃ x, x ∈ whole A ∧ f x = y.val`의 증명이다.
여기서 얻은 원소 `x`를 제시하고 `ext`로 원소 값만 비교하면
남은 목표는 `rcases`에서 얻은 등식 `hxy`와 같다.

# 합성함수
%%%
tag := "functions-composition"
file := "composition"
%%%

함수 $`f : A \to B`를 적용한 뒤 함수 $`g : B \to C`를 적용하면
$`A`의 원소에서 $`C`의 원소를 얻는다. 이 과정을 하나의 함수로 정의하자.

*정의* 함수 $`f : A \to B`와 $`g : B \to C`에 대하여
$`A`의 각 원소 $`x`를 $`g(f(x))`에 대응시키는 함수를 두 함수의 *합성함수*라고 한다.
이 함수를 $`g \circ f`로 쓰며 그 값은 $`(g \circ f)(x) = g(f(x))`이다.

합성하려면 먼저 적용하는 함수의 공역과 다음 함수의 정의역이 맞아야 한다.
아래의 정의에서는 `f`의 값이 `B`의 원소이므로 `g`를 적용하여 `C`의 원소를 얻는다.

```savedLean
def compose (g : B → C) (f : A → B) : A → C :=
  fun x => g (f x)
local infixr:90 (priority := high) " ∘ " => compose
```

마지막 선언은 `g ∘ f`를 `compose g f`에 연결하며 기호 `∘`는 `\circ`로 입력한다.
이 표기에서는 오른쪽의 `f`를 먼저 적용하고 그 값에 왼쪽의 `g`를 적용한다.
따라서 `(g ∘ f) x = g (f x)`는 정의를 펼쳐 `rfl`로 증명할 수 있다.

```savedLean
example
    (f : A → B) (g : B → C) (x : A) :
    (g ∘ f) x = g (f x) := by
  rfl
```

*보기* $`f(n) = n + 3`이고 $`g(n) = 2n`이면
$`(g \circ f)(4) = 2(4 + 3) = 14`이다.

```lean (name := compositionValue)
#eval (double ∘ (fun n : Nat => n + 3)) 4
```

```leanOutput compositionValue
14
```

{anchor "functions-congruence"}[]두 함수 $`g,h:A\to B`가 모든 원소에서 같은 값을 가지면
그 값에 함수 $`f:B\to C`를 적용한 결과도 같다.
목표가 `f (g x) = f (h x)`일 때 `congr : 1`을 쓰면
공통으로 적용한 `f`의 인수를 비교하는 `g x = h x`가 새 목표가 된다.

```savedLean
theorem functions_compose_of_pointwise_equal
    (f : B → C)
    (g h : A → B)
    (hgh : ∀ x, g x = h x)
    (x : A) :
    f (g x) = f (h x) := by
  congr : 1
  exact hgh x
```

`: 1`은 “인수가 같으면 함수값이 같다”는 규칙을 한 번 사용한다는 뜻이다.
남은 등식 `g x = h x`는 `hgh x`로 증명한다.
`congr`로 얻은 인수의 등식은 원래 목표를 증명하기에 충분한 조건이다.
함수가 단사라는 가정은 없으므로 이 두 등식이 반드시 동치인 것은 아니다.

앞의 결과를 모든 원소에 적용하면 두 합성함수의 등식도 얻는다.

```savedLean
theorem compose_of_pointwise_equal
    (f : B → C)
    (g h : A → B)
    (hgh : ∀ x, g x = h x) :
    f ∘ g = f ∘ h := by
  ext x
  exact functions_compose_of_pointwise_equal f g h hgh x
```

## 합성의 기본 성질
%%%
tag := "functions-associativity"
%%%

*정리* 함수 $`f : A \to B`, $`g : B \to C`, $`h : C \to D`에 대하여
$`h \circ (g \circ f) = (h \circ g) \circ f`이다.

*증명* 임의의 원소 $`x \in A`를 택하면
합성함수의 정의에 따라 두 함수의 값은 모두 $`h(g(f(x)))`이다.
두 함수가 모든 원소에서 같은 값을 가지므로 서로 같다.

```savedLean
theorem compose_assoc (f : A → B) (g : B → C)
    (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  ext x
  rfl
```

`ext x`로 임의의 원소에서 함수값을 비교하면
양변이 정의에 따라 `h (g (f x))`가 되므로 `rfl`로 증명을 마친다.

{anchor "functions-composition-with-identity"}[]*정리* 함수 $`f : A \to B`에 대하여
$`f \circ \operatorname{id}_A = f`이고 $`\operatorname{id}_B \circ f = f`이다.

*증명* 임의의 원소 $`x \in A`에 대하여
$`f`를 적용하기 전에 항등함수를 적용해도 결과는 $`f(x)`이며
$`f`를 적용한 뒤에 항등함수를 적용해도 같은 값을 얻는다.

```savedLean
theorem compose_identity (f : A → B) :
    f ∘ identity A = f := by
  ext x
  rfl

theorem identity_compose (f : A → B) :
    identity B ∘ f = f := by
  ext x
  rfl
```

첫 번째 등식에는 정의역의 항등함수 `identity A`를,
두 번째 등식에는 공역의 항등함수 `identity B`를 사용한다.

## 합성과 단사·전사
%%%
tag := "functions-composition-injectivity"
%%%

두 단사함수를 합성했을 때도 서로 다른 원소가 서로 다른 함수값을 갖는지 살펴보자.

*정리* 함수 $`f : A \to B`와 $`g : B \to C`가 모두 단사이면
합성함수 $`g \circ f`도 단사이다.

*증명* $`x, y \in A`에 대하여 $`g(f(x)) = g(f(y))`라고 하자.
$`g`가 단사이므로 $`f(x) = f(y)`이고 여기에 $`f`의 단사성을 사용하면 $`x = y`이다.
따라서 $`g \circ f`는 단사이다.

```savedLean
theorem injective_compose (f : A → B) (g : B → C)
    (hf : Injective f)
    (hg : Injective g) :
    Injective (g ∘ f) := by
  intro x y hxy
  apply hf
  apply hg
  exact hxy
```

위의 수학적 증명을 목표에서 거슬러 올라가면 Lean 코드의 순서가 된다.
`x = y`를 보이기 위해 `apply hf`로 `f x = f y`를 새 목표로 삼고
다시 `apply hg`로 목표를 `g (f x) = g (f y)`로 바꾼다.
이제 목표가 처음의 가정과 같으므로 `exact hxy`로 증명을 마친다.

{anchor "functions-composition-surjectivity"}[]전사성도 합성에서 유지된다.
이번에는 두 함수의 전사성을 차례로 사용하여 공역의 원소에 대응하는 정의역의 원소를 찾는다.

*정리* 함수 $`f : A \to B`와 $`g : B \to C`가 모두 전사이면
합성함수 $`g \circ f`도 전사이다.

*증명* 임의의 원소 $`z \in C`를 택하자.
$`g`가 전사이므로 $`g(y) = z`인 원소 $`y \in B`가 존재하고
$`f`가 전사이므로 $`f(x) = y`인 원소 $`x \in A`가 존재한다.
이때 $`(g \circ f)(x) = g(f(x)) = g(y) = z`이므로 원하는 원소를 얻는다.

Lean에서 이 원소들을 택하려면 먼저 전사성의 정의를 펼쳐 보자.
`hg : Surjective g`는 `∀ z, ∃ y, g y = z`의 증명이므로
`hg z`에 `unpack`을 사용하면 원소 `y`와 등식 `g y = z`를 얻는다.
이어서 `hf y`에 같은 방법을 쓰면 원소 `x`와 등식 `f x = y`를 얻는다.

```savedLean
theorem surjective_compose (f : A → B) (g : B → C)
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  -- g y = z인 y를 고르고, f x = y인 x를 고른다.
  unpack hg z with ⟨y, hy⟩
  unpack hf y with ⟨x, hx⟩

  -- 고른 x가 합성함수에서 z로 가는지 확인한다.
  exists x
  expand
  rw [hx]
  exact hy
```

`exists x`로 찾은 원소를 제시하고 `expand`로 합성의 정의를 펼치면 목표는 `g (f x) = z`이다.
여기서 `rw [hx]`로 `f x`를 `y`로 바꾸면 남은 목표 `g y = z`를 `hy`로 증명할 수 있다.

{anchor "functions-composition-bijectivity"}[]*정리* 전단사함수 두 개를 합성하면 전단사함수를 얻는다.

*증명* `constructor`로 목표를 단사성과 전사성으로 나누어 앞의 두 정리를 사용한다.
가정 `hf : Bijective f`에서는 `hf.injective`로 단사성의 증명을, `hf.surjective`로 전사성의 증명을 꺼내며
`hg`도 같은 방식으로 사용한다.

```savedLean
theorem bijective_compose (f : A → B) (g : B → C)
    (hf : Bijective f)
    (hg : Bijective g) :
    Bijective (g ∘ f) := by
  constructor
  · exact injective_compose f g hf.injective hg.injective
  · exact surjective_compose f g hf.surjective hg.surjective
```

# 집합의 곱과 함수
%%%
tag := "preliminaries-products"
file := "products"
%%%

두 집합에서 원소를 하나씩 택하면 순서쌍을 만들 수 있다. 순서쌍의 성분을 비교하는 방법을 익힌 뒤 두 함수를 각 성분에 적용하는 함수를 정의하자.

*정의* 집합 $`A`, $`B`의 원소를 하나씩 택하여 만든 순서쌍들의 집합을
두 집합의 *곱*이라고 하며 $`A \times B`로 나타낸다.

## 순서쌍과 인수의 구성
%%%
tag := "intro-pairs-and-currying"
file := "pairs-and-currying"
%%%

수학에서는 두 원소를 받는 함수를 $`f(x,y)`로 쓰기도 한다.
Lean에서도 두 원소를 순서쌍 `(x, y)` 하나로 묶어 함수에 넣을 수 있으며,
타입 `A`, `B`의 원소로 만든 순서쌍의 타입은 `A × B`이다.
`p : A × B`일 때 첫 번째 원소는 `p.1`, 두 번째 원소는 `p.2`로 꺼내며,
`×`는 `\times`로 입력한다.

자연수의 순서쌍 하나를 받아 두 성분의 합을 구하는 함수 `addPair`를 정의하자.

```savedLean
def addPair (p : Nat × Nat) : Nat := p.1 + p.2
```

Lean의 자연수 덧셈 함수 `Nat.add`는 앞에서 정의한 `add`와 같이 두 자연수를 차례로 받는다.
`addPair (2, 3)`을 계산하면 `Nat.add 2 3`과 같이 $`5`를 얻는다.
다만 인수를 받는 방식에 따라 두 함수의 타입은 각각
`Nat → Nat → Nat`와 `(Nat × Nat) → Nat`로 다르다.
`addPair`에는 `(2, 3)`처럼 순서쌍을 넣어야 한다.

{anchor "intro-argument-adapters"}[]`fun`으로 인수를 받는 방식을 바꿀 수도 있다.
자연수 덧셈 함수 `Nat.add`를 순서쌍에 사용하려면 순서쌍의 두 성분을 꺼내 `Nat.add`에 차례로 넣으면 된다.
이를 `fun (p : Nat × Nat) => Nat.add p.1 p.2`로 적으면
순서쌍 `p` 하나를 받는 새 함수를 얻는다.
여기에 `(2, 3)`을 넣으면 `p.1`은 `2`, `p.2`는 `3`이므로 `Nat.add 2 3`을 계산한다.

```lean (name := pairFromAddValue)
#eval (fun (p : Nat × Nat) => Nat.add p.1 p.2) (2, 3)
```

```leanOutput pairFromAddValue
5
```

반대로 순서쌍을 받는 `addPair`를 두 자연수 `x`, `y`에 사용하려면
이 둘을 `(x, y)`로 묶어 넣으면 된다.
이때 `fun` 뒤에 `x`와 `y`를 차례로 적으면
두 인수를 하나씩 받는 함수를 얻는다.

```lean (name := argumentsFromAddPairValue)
#eval (fun (x y : Nat) => addPair (x, y)) 2 3
```

```leanOutput argumentsFromAddPairValue
5
```

일반적으로도 `A → B → X` 타입의 함수를 순서쌍에 사용하려면
두 성분을 꺼내 차례로 넣고,
`(A × B) → X` 타입의 함수를 두 인수에 사용하려면 이들을 순서쌍으로 묶어 넣으면 된다.
두 타입은 서로 다르지만 이처럼 인수를 받는 방식을 바꾸어 사용할 수 있다.
이 교재에서는 주로 인수를 차례로 받는 방식으로 함수를 정의하겠다.

## 순서쌍의 비교
%%%
tag := "functions-pair-comparison"
%%%

두 순서쌍이 같으려면 각 자리의 원소가 같아야 한다.
즉 $`(a,b)=(a',b')`는 $`a=a'`이고 $`b=b'`인 것과 동치이다.

*보기* $`a=c`이고 $`b=d`이면 $`(a,b)=(c,d)`이다.
순서쌍에서도 `ext`로 두 성분을 각각 비교한다.

```savedLean
example (a c : A) (b d : B)
    (ha : a = c)
    (hb : b = d) :
    (a, b) = (c, d) := by
  ext
  · exact ha
  · exact hb
```

`ext`를 쓰면 첫 번째 목표는 `a = c`이고 두 번째 목표는 `b = d`이다.
각 목표는 주어진 가정 `ha`와 `hb`로 증명한다.

반대로 순서쌍이 같다는 가정이 주어지면 각 성분의 등식을 얻을 수 있다.
`indisc at h with ha hb`는 가정 `h : (a, b) = (c, d)`에서
`ha : a = c`와 `hb : b = d`를 얻는 전술이다.
예를 들어 두 성분의 자리를 바꾼 순서쌍도 서로 같음을 보이자.
목표의 `(b, a)`에는 등식 `h`의 왼쪽인 `(a, b)`가 그대로 나타나지 않으므로
먼저 각 성분의 등식을 얻어 대입하면 편리하다.

```savedLean
example (a c : A) (b d : B)
    (h : (a, b) = (c, d)) :
    (b, a) = (d, c) := by
  indisc at h with ha hb
  rw [ha, hb]
```

여기서 `indisc`은 원래 등식 `h`를 유지하며 성분의 등식 두 개에 각각 이름을 붙인다.
이후 `rw [ha, hb]`로 `a`를 `c`로, `b`를 `d`로 바꾸면 양변이 같아진다.
두 성분의 등식은 다른 목표나 가정에도 따로 사용할 수 있다.

`ext`와 `indisc`의 기본형은 한 겹을 비교한다.
예를 들어 `Fin m × Fin n`의 등식에 `ext`를 쓰면 두 번호의 등식이 남으며,
각 번호에서 한 번 더 `ext`를 써야 그 자연수 값을 비교한다.
가정에 `indisc at h with hi hj`를 사용해도 먼저 두 번호 자체의 등식을 얻는다.
두 겹을 한 번에 비교하려면 `ext : 2`나 `indisc : 2 at h`를,
비교할 수 있는 곳까지 반복하려면 `ext!`나 `indisc! at h`를 사용한다.

성분이나 원소의 값을 비교하는 더 많은 예는
{ref "tactic-indisc"}[부록의 등식에서의 비교]에서 살펴볼 수 있다.


집합 `S : Set A`, `T : Set B`의 곱은 `A × B` 위의 집합으로 정의한다.
순서쌍 `p`가 이 집합에 속하려면 `p.1 ∈ S`와 `p.2 ∈ T`가 모두 성립해야 한다.

```savedLean
def setProduct (S : Set A) (T : Set B) : Set (A × B) :=
  fun p => p.1 ∈ S ∧ p.2 ∈ T
```

*보기* $`a \in S`이고 $`b \in T`이면 $`(a,b) \in S \times T`이다.
원소 조건이 논리곱이므로 `constructor`로 나눈 두 목표에 주어진 증명을 사용하면 된다.

```savedLean
example
    (S : Set A) (T : Set B) (a : A) (b : B)
    (ha : a ∈ S)
    (hb : b ∈ T) :
    (a, b) ∈ setProduct S T := by
  constructor
  · exact ha
  · exact hb
```


## 성분별 함수의 단사·전사
%%%
tag := "functions-product-maps"
file := "product-maps"
%%%

합성함수에서는 한 함수의 값을 다음 함수에 넣었다.
집합의 곱에서는 두 성분에 서로 다른 함수를 적용하는 방식도 사용할 수 있다.
함수 $`f:A\to C`와 $`g:B\to D`가 주어지면
$`(a,b)\mapsto(f(a),g(b))`로 $`A\times B`에서 $`C\times D`로 가는 함수를 정의하자.

```savedLean
def productMap (f : A → C) (g : B → D) : A × B → C × D :=
  fun p => (f p.1, g p.2)
```

*보기* $`f`와 $`g`가 각각 단사이면 `productMap f g`도 단사이다.
두 함수값인 순서쌍이 같으면 각 성분이 같으므로
$`f(a)=f(a')`와 $`g(b)=g(b')`를 얻는다.
각 함수의 단사성에 따라 $`a=a'`이고 $`b=b'`이므로 원래 순서쌍들도 같다.

```savedLean
theorem productMap_injective (f : A → C) (g : B → D)
    (hf : Injective f)
    (hg : Injective g) :
    Injective (productMap f g) := by
  intro x y hxy
  -- 함수값의 두 성분을 각각 비교한다.
  indisc at hxy with hfirst hsecond
  ext
  · exact hf x.1 y.1 hfirst
  · exact hg x.2 y.2 hsecond
```

`indisc at hxy with hfirst hsecond`로 함수값의 두 성분이 같음을 얻는다.
이 두 등식에 `hf`와 `hg`를 사용하면 원래 순서쌍의 각 성분을 비교할 수 있다.

*보기* $`f`와 $`g`가 각각 전사이면 `productMap f g`도 전사이다.
공역의 원소 $`(c,d)`를 택하면 전사성에 따라 $`f(a)=c`와 $`g(b)=d`인 원소 $`a,b`가 존재한다.
그러면 $`(a,b)`에서의 함수값이 $`(c,d)`이므로 전사성을 얻는다.

```savedLean
theorem productMap_surjective (f : A → C) (g : B → D)
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (productMap f g) := by
  intro y
  -- 공역의 각 성분에 대응하는 원소를 택한다.
  unpack hf y.1 with ⟨a, ha⟩
  unpack hg y.2 with ⟨b, hb⟩
  exists (a, b)
  ext
  · exact ha
  · exact hb
```

여기서 `hf y.1`은 `∃ a, f a = y.1`의 증명이고
`hg y.2`는 `∃ b, g b = y.2`의 증명이다.
두 원소를 함께 택한 뒤 `ext`로 함수값의 두 성분을 비교하면
각 존재명제에서 얻은 등식을 그대로 사용할 수 있다.

*보기* $`f`와 $`g`가 각각 전단사이면 `productMap f g`도 전단사이다.
앞의 두 보기에서 단사성과 전사성을 각각 증명했으므로
그 결과를 사용하여 두 조건을 묶자.

```savedLean
theorem productMap_bijective (f : A → C) (g : B → D)
    (hf : Bijective f)
    (hg : Bijective g) :
    Bijective (productMap f g) := by
  constructor
  · exact productMap_injective f g hf.injective hg.injective
  · exact productMap_surjective f g
      hf.surjective hg.surjective
```

뒤에서 집합의 크기를 다룰 때는 이 결과로 두 집합의 곱 사이에 전단사함수를 만든다.

# 역함수
%%%
tag := "functions-inverses"
file := "inverses"
%%%

함수 $`f : A\to B`를 적용한 뒤 원래 원소로 돌아가려면
반대 방향의 함수 $`g : B\to A`가 필요하다.
두 함수를 어느 순서로 합성하든 항등함수가 되는 경우를 정의하자.

*정의* 함수 $`f : A\to B`와 $`g : B\to A`가 모든 $`x\in A`, $`y\in B`에 대하여
$`g(f(x))=x`와 $`f(g(y))=y`를 만족하면 $`g`를 $`f`의 *역함수*라고 한다.
즉 $`g\circ f=\operatorname{id}_A`이고 $`f\circ g=\operatorname{id}_B`이다.

역함수는 보통 $`f^{-1}`로 쓰므로 앞에서 배운 역상의 표기 $`f^{-1}(T)`와 구별할 필요가 있다.
원소 $`y\in B`에 대한 $`f^{-1}(y)`는 역함수의 값이며,
집합 $`T\subseteq B`에 대한 $`f^{-1}(T)`는 $`f(x)\in T`를 만족하는 원소 $`x`들의 집합이다.
역상을 정의할 때는 이 원소 조건만 사용하므로 $`f`에 역함수가 없어도 $`f^{-1}(T)`를 쓸 수 있다.

*보기* 항등함수는 자기 자신의 역함수이다.
어느 원소에 두 번 적용해도 원래 원소를 얻으므로 다음 두 등식이 성립한다.

```savedLean
theorem functions_identity_twice
    (x : A) :
    identity A (identity A x) = x := by
  rfl

example :
    identity A ∘ identity A = identity A := by
  ext x
  exact functions_identity_twice x
```

두 번째 증명에서는 `ext x`로 함수값을 비교한 뒤
앞의 보기 `functions_identity_twice x`를 사용하여 그 등식을 증명한다.

*보기* 순서쌍의 두 원소를 바꾸는 함수는 한 번 더 원소를 바꾸면 원래 순서쌍을 돌려준다.
즉 $`A\times B`에서 $`B\times A`로 가는 함수 $`(a,b)\mapsto(b,a)`의 역함수는
$`B\times A`에서 $`A\times B`로 가는 함수 $`(b,a)\mapsto(a,b)`이다.

```savedLean
def swapPair (p : A × B) : B × A := (p.2, p.1)
theorem swapPair_twice (p : A × B) :
    swapPair (swapPair p) = p := by
  rfl
```

먼저 적용하는 안쪽의 `swapPair`의 값은 `B × A`의 원소이므로
그 값에 다시 사용하는 `swapPair`는 `B × A → A × B`인 함수이다.
위 등식은 두 타입을 서로 바꾸어도 성립하므로 양쪽 순서의 역함수 조건을 모두 확인한 것이다.

이 등식으로 `swapPair`가 전단사임을 보일 수 있다.
$`\operatorname{swapPair}(p)=\operatorname{swapPair}(q)`이면 양변에 한 번 더 `swapPair`를 적용하여
$`p=q`를 얻으므로 단사이다. 공역의 원소 $`q`에 대해서는
원소 $`\operatorname{swapPair}(q)`를 택하면 그 함수값이 $`q`이므로 전사이다.

```savedLean
theorem swapPair_bijective :
    Bijective (swapPair : A × B → B × A) := by
  constructor
  · intro p q hpq
    have h :
        swapPair (swapPair p) = swapPair (swapPair q) := by
      rw [hpq]

    rw [swapPair_twice, swapPair_twice] at h
    exact h

  · intro q
    exists (swapPair q)
```

단사성의 증명에서는 `swapPair_twice`로 양변을 각각 `p`, `q`로 바꾼다.
전사성에서 선택한 원소의 함수값은 두 성분을 두 번 바꾼 순서쌍이므로
정의에 따른 계산으로 `q`와 같음을 확인한다.

## 전단사와 원소의 유일성
%%%
tag := "functions-inverse-construction"
%%%

역함수를 구성하려면 각 $`y\in B`에 대응하는 원소를 정해야 한다.
$`f`가 전단사이면 전사성에 따라 $`f(x)=y`인 원소 $`x\in A`가 존재한다.
다른 원소 $`z`도 $`f(z)=y`를 만족하면 $`f(z)=f(x)`이므로 단사성에 따라 $`z=x`이다.
각 $`y\in B`에 대하여 $`f(x)=y`인 원소 $`x\in A`가 유일하게 존재함을 Lean으로 증명하자.
아래 명제에서는 원소의 존재를 `∃ x`로 쓰고,
그 원소가 만족하는 조건과 유일성을 논리곱으로 묶었다.

```savedLean
theorem bijective_preimage_unique (f : A → B)
    (hf : Bijective f) :
    ∀ y : B, ∃ x : A,
      f x = y ∧ ∀ z : A, f z = y → z = x := by
  intro y
  -- 전사성으로 f x = y인 원소를 얻는다.
  unpack hf.surjective y with ⟨x, hx⟩
  exists x
  constructor
  · exact hx
  · intro z hz
    -- 같은 함수값을 갖는 원소는 단사성으로 같다.
    apply hf.injective
    rw [hz, hx]
```

`hf.surjective y`는 `∃ x, f x = y`의 증명이므로 `unpack`으로 원소 `x`와 등식 `hx`를 얻는다.
유일성을 보이는 부분에서 `apply hf.injective`를 쓰면 목표가 `f z = f x`가 되고,
`rw [hz, hx]`는 대괄호 안의 등식을 왼쪽부터 차례로 사용한다.
먼저 `hz`로 `f z`를 `y`로 바꾸고 이어서 `hx`로 `f x`를 `y`로 바꾸면 양변이 같아진다.

## 원소의 선택과 역함수
%%%
tag := "functions-existence-and-values"
%%%

앞의 정리에 따르면 각 $`y\in B`에 대해 $`f(x)=y`인 원소 $`x`가 존재한다.
수학에서는 “그러한 $`x`를 하나 택하여 $`g(y)`로 정한다”는 방법으로 역함수를 구성한다.
Lean에서도 존재한다는 사실을 바탕으로 원소를 고른 뒤,
그 원소가 조건을 만족한다는 증명을 사용하여 역함수의 성질을 보인다.

먼저 존재명제의 증명과 함수값으로 사용할 원소를 구별하자.
`hf.surjective y`는 `∃ x, f x = y`의 증명이다.
이 명제를 `unpack`이나 `rcases`로 분해하여 다른 명제를 증명할 수는 있지만,
그 안의 원소를 꺼내 `A`의 값으로 반환할 수는 없다.
예를 들어 `∃ n : Nat, True`는 $`0`을 제시해서도, $`1`을 제시해서도 증명할 수 있다.
Lean은 이 두 증명을 같은 명제의 증명으로서 같게 취급한다.
만약 증명에 사용한 원소를 그대로 꺼내 계산할 수 있다면
같게 취급하는 두 증명에서 서로 다른 자연수 $`0`과 $`1`을 얻게 된다.
이를 막기 위해 존재명제의 증명을 분해하여 계산에 쓸 값을 만드는 데에는 제한이 있다.
원소의 유일성을 보인 경우에도 존재명제에서 값을 꺼내려면 별도의 원소 선택이 필요하다.

원소를 이후의 계산에도 사용하려면 앞에서 배운 부분타입으로 원소와 증명을 함께 제공할 수 있다.
항등함수를 예로 들어 존재명제의 증명과 부분타입의 원소를 각각 만들어 보자.

```savedLean
theorem identity_preimage_exists (y : A) :
    ∃ x : A, identity A x = y := by
  exists y

def identityPreimage (y : A) :
    {x : A // identity A x = y} :=
  { val := y, property := by rfl }
```

첫 번째 코드에서는 `exists y`로 원소의 존재를 증명하고,
두 번째 코드에서는 `val := y`로 값이 `y`인 부분타입의 원소를 만든다.
따라서 두 번째 결과에서는 `.val`로 원소를 꺼내 사용할 수 있다.

```savedLean
example
    (y : A) :
    (identityPreimage y).val = y := by
  rfl
```

항등함수에서는 필요한 원소가 `y`임을 알고 있으므로 `identityPreimage`에서 그 값을 직접 넣었다.
일반적인 전단사 `f`에 대해서는 `hf.surjective y`로 존재성을 확인한 뒤
조건을 만족하는 원소를 택해야 한다.
술어 `P : A → Prop`와 존재명제의 증명 `h : ∃ x, P x`가 주어졌을 때
`Classical.choose h`는 `P`를 만족하는 `A`의 원소 하나를 정한다.
원소의 유일성을 요구하지 않으므로 조건을 만족하는 원소가 여러 개일 때도 사용할 수 있다.
조건을 만족하는 원소가 여러 개라면 존재성을 증명할 때 제시했던 원소와 다른 원소를 고를 수도 있다.
어느 원소를 고르든 조건 `P`를 만족한다는 성질을 사용할 수 있다.

선택한 원소로 추론하려면 그 원소가 조건을 만족한다는 증명도 필요하다.
`Classical.choose h`의 타입은 `A`이고,
`Classical.choose_spec h`는 바로 그 원소에 대한 `P (Classical.choose h)`의 증명이다.
역함수에서는 각 `y`에 대해 `hf.surjective y`를 `Classical.choose`와 `Classical.choose_spec`에 넣는다.
선택한 원소들을 함수값으로 삼고 $`f(g(y))=y`의 증명을 함께 담으면
함수 $`g:B\to A`와 그 성질을 하나의 부분타입으로 구성할 수 있다.

`Classical.choose`는 조건을 만족하는 원소를 정하지만 그 원소를 계산하는 방법을 제공하지는 않는다.
이 선택을 이용하여 함수를 정의할 때는 `def` 앞에 `noncomputable`을 붙인다.

```savedLean
noncomputable def inverseMapData (f : A → B)
    (hf : Bijective f) :
    { g : B → A // ∀ y, f (g y) = y } :=
  { val := fun y => Classical.choose (hf.surjective y)
    property := by
      intro y
      exact Classical.choose_spec (hf.surjective y) }
```

`val`에는 선택한 원소를 함수값으로 삼는 함수를 넣는다.
`property`에서는 임의의 `y`를 택한 뒤
같은 존재성의 증명 `hf.surjective y`에 `choose_spec`을 적용한다.
이로써 `val`에 넣은 함수가 모든 `y`에서 $`f(g(y))=y`를 만족함을 보인다.

이제 `inverseMapData`에서 함수를 꺼내 `inverseMap`으로 정의하고,
그 성질을 `inverseMap_spec`이라는 정리로 사용하자.
`.val`은 함수이며 `.property`는 모든 `y`에서 성립하는 등식의 증명이므로
후자에 `y`를 넣으면 그 원소에서의 등식을 얻는다.

```savedLean
noncomputable def inverseMap (f : A → B)
    (hf : Bijective f) : B → A :=
  (inverseMapData f hf).val
theorem inverseMap_spec (f : A → B)
    (hf : Bijective f)
    (y : B) :
    f (inverseMap f hf y) = y := by
  exact (inverseMapData f hf).property y
```

원소를 선택하는 이 구성은 Lean의 선택공리에 의존한다.

반대 순서로 적용한 $`g(f(x))=x`도 확인하자.
$`f(g(f(x)))=f(x)`이므로 $`f`의 단사성을 사용하면 된다.

```savedLean
theorem inverseMap_left (f : A → B)
    (hf : Bijective f)
    (x : A) :
    inverseMap f hf (f x) = x := by
  apply hf.injective
  exact inverseMap_spec f hf (f x)
```

`apply hf.injective`는 두 원소가 같다는 목표를 그 함수값이 같다는 목표로 바꾼다.
남은 목표 `f (inverseMap f hf (f x)) = f x`는
`inverseMap_spec`에 공역의 원소 `f x`를 넣어 얻는다.

이제 역함수의 존재를 하나의 명제로 정리하자.
`inverseMap`은 함수 자체의 정의이고,
다음 정리는 두 역함수 조건을 만족하는 함수가 존재한다는 증명이다.

```savedLean
theorem inverse_exists (f : A → B)
    (hf : Bijective f) :
    ∃ g : B → A,
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  exists (inverseMap f hf)
  constructor
  · intro x
    exact inverseMap_left f hf x

  · intro y
    exact inverseMap_spec f hf y
```

`exists`로 앞에서 정의한 함수를 제시한 뒤 두 조건을 각각 증명했다.
함수의 정의인 `inverseMap`에는 `noncomputable`을 붙이고, 명제의 증명인 `inverse_exists`에는 붙이지 않는다.

## 역함수의 유일성
%%%
tag := "functions-inverse-uniqueness"
%%%

*정리* 두 함수 $`g,h : B\to A`가 모두 $`f : A\to B`의 역함수이면 $`g=h`이다.

*증명* 임의의 $`y\in B`를 택하자.
$`g`가 역함수이므로 $`g(f(h(y)))=h(y)`이고,
$`h`도 역함수이므로 $`f(h(y))=y`이다.
첫 번째 등식에 두 번째 등식을 대입하면 $`g(y)=h(y)`를 얻는다.
이 등식이 모든 $`y`에 대하여 성립하므로 두 함수는 같다.

Lean에서는 먼저 `g (f (h y)) = h y`에 이름 `hgy`를 붙인다.
`rw [hh.right y] at hgy`로 그 안의 `f (h y)`를 `y`로 바꾸면
목표인 `g y = h y`의 증명을 얻는다.

```savedLean
theorem inverse_function_unique (f : A → B)
    (g h : B → A)
    (hg : (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y))
    (hh : (∀ x, h (f x) = x) ∧ (∀ y, f (h y) = y)) :
    g = h := by
  ext y
  -- h(y)에 f를 적용한 뒤 g로 돌아오는 값을 비교한다.
  have hgy : g (f (h y)) = h y := by
    exact hg.left (h y)

  rw [hh.right y] at hgy
  exact hgy
```

가정 `hg`와 `hh`는 각 함수의 역함수 조건을 논리곱으로 묶은 것이다.
`hg.left`에 `h y`를 넣어 첫 등식을 얻고,
`hh.right y`로 그 등식의 안쪽 함수값을 바꾼다.

*보기* 전단사 `swapPair`에 `inverseMap`을 적용하여 얻은 역함수는 다시 `swapPair`이다.
`inverseMap`의 정의에서 원소를 어떻게 골랐는지와 관계없이
두 함수가 같은 역함수 조건을 만족하므로 유일성 정리를 사용할 수 있다.

```savedLean
example :
    inverseMap (swapPair : A × B → B × A)
      swapPair_bijective =
      swapPair := by
  apply inverse_function_unique swapPair
  · constructor
    · exact inverseMap_left swapPair swapPair_bijective
    · exact inverseMap_spec swapPair swapPair_bijective

  · constructor
    · exact swapPair_twice
    · exact swapPair_twice
```

첫 두 목표에는 `inverseMap`의 성질을 사용하고,
나머지 두 목표에는 앞에서 증명한 `swapPair_twice`를 사용한다.
이처럼 역함수의 유일성을 사용하면 `inverseMap`으로 정의한 함수를 구체적인 식으로 나타낼 수 있다.

## 역함수의 성질
%%%
tag := "functions-inverse-laws"
%%%

`inverseMap_left`와 `inverseMap_spec`은 각각의 원소에서 성립하는 등식이므로
`ext`로 원소별 등식을 목표로 삼으면 합성함수와 항등함수의 같음을 보일 수 있다.

```savedLean
theorem inverseMap_compose (f : A → B)
    (hf : Bijective f) :
    inverseMap f hf ∘ f = identity A := by
  ext x
  exact inverseMap_left f hf x

theorem compose_inverseMap (f : A → B)
    (hf : Bijective f) :
    f ∘ inverseMap f hf = identity B := by
  ext y
  exact inverseMap_spec f hf y
```

{anchor "functions-inverse-bijectivity"}[]*정리* 전단사함수의 역함수도 전단사이다.

*증명* 역함수를 $`g`라고 하자.
$`g(x)=g(y)`이면 양변에 $`f`를 적용하여 $`f(g(x))=f(g(y))`를 얻고
역함수의 성질로 양변을 바꾸면 $`x=y`이다.
또한 임의의 $`a\in A`에 대하여 $`g(f(a))=a`이므로 $`g`는 전사이다.

```savedLean
theorem inverseMap_bijective (f : A → B)
    (hf : Bijective f) :
    Bijective (inverseMap f hf) := by
  constructor
  · intro x y hxy
    -- 같은 두 역함수 값에 f를 적용한다.
    have h :
        f (inverseMap f hf x) = f (inverseMap f hf y) := by
      rw [hxy]

    -- f와 역함수를 차례로 적용하면 원래 원소이다.
    rw [inverseMap_spec f hf x, inverseMap_spec f hf y] at h
    exact h

  · intro x
    -- f x를 역함수에 넣으면 x를 얻는다.
    exists (f x)
    exact inverseMap_left f hf x
```

단사성을 보일 때는 `hxy`로 두 함수값의 등식 `h`를 얻은 뒤
`inverseMap_spec`을 `x`와 `y`에 각각 적용한 등식으로 양변을 바꾼다.
전사성을 보일 때는 `exists (f x)`로 원소를 택하면
남은 목표가 `inverseMap f hf (f x) = x`가 되므로 `inverseMap_left`를 사용한다.

# 연습문제
%%%
tag := "functions-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* $`S \subseteq T`이면 $`f^{-1}(S) \subseteq f^{-1}(T)`임을 증명하라.

```savedLean -keep
theorem exercise_preimage_subset
    (f : A → B) (S T : Set B)
    (hST : S ⊆ T) :
    preimage f S ⊆ preimage f T := by
  sorry
```


*문제 2* 합성함수 $`g \circ f`가 단사이면 $`f`도 단사임을 증명하라.

```savedLean -keep
theorem exercise_injective_of_compose
    (f : A → B) (g : B → C)
    (h : Injective (g ∘ f)) :
    Injective f := by
  sorry
```


*문제 3* 합성함수 $`g \circ f`가 전사이면 $`g`도 전사임을 증명하라.

```savedLean -keep
theorem exercise_surjective_of_compose
    (f : A → B) (g : B → C)
    (h : Surjective (g ∘ f)) :
    Surjective g := by
  sorry
```


*문제 4* $`f(n) = n + 1`, $`g(n) = 2n`인 두 자연수 함수에 대하여
$`(g \circ f)(3)`과 $`(f \circ g)(3)`을 계산하고 두 합성함수가 서로 다름을 증명하라.
세 번째 증명에서는 앞의 두 계산 결과를 사용하라.

```savedLean -keep
theorem exercise_double_after_successor_at_three :
    (double ∘ (fun n : Nat => n + 1)) 3 = 8 := by
  sorry

theorem exercise_successor_after_double_at_three :
    ((fun n : Nat => n + 1) ∘ double) 3 = 7 := by
  sorry

theorem exercise_double_successor_noncommute :
    double ∘ (fun n : Nat => n + 1) ≠
    (fun n : Nat => n + 1) ∘ double := by
  sorry
```


*문제 5* 전단사함수의 역함수에 다시 역함수를 취하면 원래 함수를 얻음을 증명하라.

```savedLean -keep
theorem exercise_inverse_inverse
    (f : A → B)
    (hf : Bijective f) :
    inverseMap (inverseMap f hf)
      (inverseMap_bijective f hf) = f := by
  sorry
```

*힌트* `ext x`로 원소별 등식을 보인 뒤 역함수의 단사성을 사용하라.
남은 두 함수값은 `inverseMap_spec`과 `inverseMap_left`로 각각 `x`가 된다.


*문제 6* $`(a,b)\in S\times T`이면 $`(b,a)\in T\times S`임을 증명하라.

```savedLean -keep
theorem exercise_setProduct_swap
    (S : Set A) (T : Set B) (a : A) (b : B)
    (h : (a, b) ∈ setProduct S T) :
    (b, a) ∈ setProduct T S := by
  sorry
```

*문제 7* (두 원소 집합의 상과 역상)

(1) $`\operatorname{double}(\{2,3\})=\{4,6\}`임을 증명하라.
(2) 첫 결과와 `preimage_image_of_injective`를 사용하여
$`\operatorname{double}^{-1}(\{4,6\})=\{2,3\}`임을 보이라.

```savedLean -keep
def practiceFourSix : Set Nat := fun n => n = 4 ∨ n = 6
theorem exercise_image_double_twoThree :
    image double twoThree = practiceFourSix := by
  sorry

theorem exercise_preimage_double_fourSix :
    preimage double practiceFourSix = twoThree := by
  sorry
```

*문제 8* (좌표 함수)

첫 좌표를 꺼내는 함수 $`p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}`에 대하여
전사성을 증명하고 단사성이 성립하지 않음을 보이라.
단사성을 반박할 때에는 함수값이 같아지는 서로 다른 두 순서쌍을 찾으라.

```savedLean -keep
def practiceFirst : Nat × Nat → Nat := fun p => p.1
theorem exercise_first_surjective :
    Surjective practiceFirst := by
  sorry

theorem exercise_first_not_injective :
    ¬ Injective practiceFirst := by
  sorry
```

*문제 9* (대각선 함수)

$`d(n)=(n,n)`으로 정한 함수 $`d:\mathbb{N}\to\mathbb{N}\times\mathbb{N}`의 단사성을 증명하라.
또한 이 함수는 전사가 아님을 증명하라.

```savedLean -keep
def practiceDiagonal : Nat → Nat × Nat := fun n => (n, n)
theorem exercise_diagonal_injective :
    Injective practiceDiagonal := by
  sorry

theorem exercise_diagonal_not_surjective :
    ¬ Surjective practiceDiagonal := by
  sorry
```

*문제 10* (역상과 집합 연산)

역상은 교집합과 여집합을 보존한다. 다음 두 등식을 증명하라.
함수의 단사성이나 전사성을 가정하지 않고 증명하라.

```savedLean -keep
theorem exercise_preimage_inter (f : A → B)
    (S T : Set B) :
    preimage f (S ∩ T) = preimage f S ∩ preimage f T := by
  sorry

theorem exercise_preimage_compl (f : A → B) (T : Set B) :
    preimage f Tᶜ = (preimage f T)ᶜ := by
  sorry
```

*문제 11* (합집합의 상)

$`f(S\cup T)=f(S)\cup f(T)`임을 증명하라.

```savedLean -keep
theorem exercise_image_union (f : A → B) (S T : Set A) :
    image f (S ∪ T) = image f S ∪ image f T := by
  sorry
```

*문제 12* (합성에서의 소거)

(1) 단사함수 $`h`에 대하여 $`h\circ f=h\circ g`이면 $`f=g`임을 증명하라.
(2) 전사함수 $`h`에 대하여 $`f\circ h=g\circ h`이면 $`f=g`임을 증명하라.
두 증명에서 단사성과 전사성이 각각 어디에 쓰이는지 주석으로 적으라.

```savedLean -keep
theorem exercise_cancel_injective (f g : A → B)
    (h : B → C)
    (hh : Injective h)
    (heq : h ∘ f = h ∘ g) :
    f = g := by
  sorry

theorem exercise_cancel_surjective (f g : B → C)
    (h : A → B)
    (hh : Surjective h)
    (heq : f ∘ h = g ∘ h) :
    f = g := by
  sorry
```

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
