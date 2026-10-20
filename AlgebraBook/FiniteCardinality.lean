import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Relations
import AlgebraBook.Tactic.Cardinality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "집합의 크기와 유한성" =>

%%%
tag := "cardinality"
file := "cardinality"
%%%

두 집합의 원소를 빠짐없이 짝지을 수 있는지를 기준으로 크기를 비교하자.
이 관계로 기수를 정의한 뒤 유한집합에 번호를 붙여 원소를 센다.
번호를 붙이는 방법이 달라도 원소 수는 같음을 증명하고,
유한 개의 번호로 자연수 전체를 셀 수 없음을 보인다.

```savedImport
import AlgebraBook.Relations
import AlgebraBook.Tactic.Cardinality
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

# 전단사와 같은 크기
%%%
tag := "cardinality-same-size"
file := "same-cardinality"
%%%

두 유한집합의 원소를 하나씩 짝지어 모두 대응시킬 수 있다면 원소의 수가 같다.
전단사는 서로 다른 원소가 겹치지 않게 대응하면서 공역의 원소를 빠짐없이 포함하므로
이러한 짝짓기를 나타낸다.
같은 조건을 무한집합 사이의 대응에도 사용할 수 있으므로 다음과 같이 크기를 비교하자.

*정의* 두 집합 $`A`, $`B` 사이에 전단사함수가 존재하면 두 집합의 *크기가 같다*고 한다.
집합의 크기를 *기수*(cardinality)라고도 하며 두 집합의 기수가 같다는 관계를 $`|A|=|B|`로 쓴다.

Lean에서는 함수 절에서와 같이 원소들의 타입을 `A`, `B`로 두고
그 사이에 전단사가 존재한다는 명제를 정의한다.

```savedLean
def SameCardinality : Type → Type → Prop :=
  fun A B => ∃ f : A → B, Bijective f
```

집합 `S : Set A`와 `T : Set B`의 크기를 비교할 때는
{ref "functions-elements"}[집합 위의 함수]에서 정의한 원소 타입을 사용하여
`SameCardinality (Elem S) (Elem T)`로 쓴다.

`SameCardinality A B`의 정의를 펼치면 `∃ f : A → B, Bijective f`이다.
이 명제를 증명하려면 함수 하나를 제시하고 그 함수가 전단사임을 보이면 된다.
반대로 가정에서 이러한 함수와 전단사성의 증명을 꺼낼 때는 `unpack`을 사용한다.

이 관계가 동치관계임을 확인하자. 반사성에는 항등함수,
대칭성에는 역함수, 추이성에는 합성함수를 사용한다.

{anchor "cardinality-reflexivity"}[]*정리* 모든 집합은 자기 자신과 크기가 같다.

*증명* 항등함수는 전단사이므로 그 함수를 택하면 된다.

```savedLean
theorem sameCardinality_refl (A : Type) :
    SameCardinality A A := by
  exists identity A
  exact identity_bijective A
```

{anchor "cardinality-symmetry"}[]*정리* $`|A|=|B|`이면 $`|B|=|A|`이다.

*증명* {ref "functions-inverse-bijectivity"}[역함수의 성질]에서 전단사의 역함수도 전단사임을 보였다.
주어진 전단사의 역함수를 택하면 된다.

```savedLean
theorem sameCardinality_symm {A B : Type}
    (h : SameCardinality A B) :
    SameCardinality B A := by
  unpack h with ⟨f, hf⟩
  exists (inverseMap f hf)
  exact inverseMap_bijective f hf
```

{anchor "cardinality-transitivity"}[]*정리* $`|A|=|B|`이고 $`|B|=|C|`이면 $`|A|=|C|`이다.

*증명* 전단사함수 $`f : A \to B`와 $`g : B \to C`를 택하자.
{ref "functions-composition-bijectivity"}[함수의 합성]에서 두 전단사함수의 합성도 전단사임을 증명했으므로 $`g\circ f`를 사용하면 된다.

```savedLean
theorem sameCardinality_trans {A B C : Type}
    (hAB : SameCardinality A B)
    (hBC : SameCardinality B C) :
    SameCardinality A C := by
  unpack hAB with ⟨f, hf⟩
  unpack hBC with ⟨g, hg⟩
  exists (g ∘ f)
  exact bijective_compose f g hf hg
```

# 기수와 동치류
%%%
tag := "cardinality-quotient-type"
file := "cardinals"
%%%

이로써 같은 크기라는 관계의 반사성·대칭성·추이성을 모두 확인했다.
{ref "preliminaries-quotients"}[몫집합]에서는 같은 부류에 속하는 원소들이 같은 동치류를 정했다.
이번에는 원소 타입 `A`와 전단사가 존재하는 타입들을 하나의 동치류로 모으자.
정수의 합동에서는 정수들을 동치류로 묶었지만,
여기서는 `Nat`, `Fin 3`, `Elem positives`와 같은 타입들이 관계의 대상이다.
각 동치류를 하나의 원소로 갖는 몫타입을 만들면 집합의 크기 자체를 값으로 다룰 수 있다.
이 몫타입을 `Cardinal`이라고 정의하자.

```savedLean -show
theorem sameCardinality_equivalence : IsEquivalence SameCardinality := by
  and_intros
  · exact sameCardinality_refl
  · intro A B hAB
    exact sameCardinality_symm hAB

  · intro A B C hAB hBC
    exact sameCardinality_trans hAB hBC
```

```savedLean
def Cardinal := Type / SameCardinality
def cardinal (A : Type) : Cardinal :=
  ⟦A⟧
```

```savedLean -show
attribute [reducible] Cardinal
```

`Type / SameCardinality`는 타입들을 전단사 관계로 나눈 몫타입이며,
정의를 펼치면 `Elem (quotientSet SameCardinality)`이다.
`cardinal A`는 `A`를 대표원으로 만든 몫 원소이다.
그 안에는 `A`와 전단사가 존재하는 타입들의 집합과, 이 집합이 동치류라는 증명이 들어 있다.
따라서 두 타입의 크기가 같으면 그 기수에 담긴 동치류도 같다.

*정리* 두 기수 `cardinal A`와 `cardinal B`가 같을 필요충분조건은
`SameCardinality A B`이다.

```savedLean
theorem cardinal_eq_iff (A B : Type) :
    cardinal A = cardinal B ↔ SameCardinality A B := by
  exact classOf_eq_iff SameCardinality
    sameCardinality_equivalence A B
```

```savedLean -show
attribute [ample_compare] cardinal_eq_iff
```

앞 절의 `classOf_eq_iff`를 전단사 관계에 적용한 결과이다.
두 기수가 같다는 것은 같은 동치류를 값으로 담았다는 뜻이며,
이 동치류가 같을 필요충분조건은 대표원 사이에 전단사가 존재한다는 것이다.
이 정리는 `ext`와 `indisc`에도 연결했다.
`ext`로 기수의 등식을 전단사의 존재를 보이는 목표로 바꾸고,
`indisc at h`로 기수의 등식 `h`에서 전단사가 존재한다는 증명을 얻을 수 있다.

앞으로 크기가 같다는 명제는 `cardinal A = cardinal B`로 나타내겠다.
이 등식을 증명할 때 `ext`를 쓰면 `SameCardinality A B`가 목표가 되므로
앞에서와 같이 `A`에서 `B`로 가는 전단사를 제시하면 된다.
등식의 증명 `h`가 주어졌을 때는 `(cardinal_eq_iff A B).mp h`로 전단사의 존재를 얻는다.

```savedLean
example {A B : Type}
    (f : A → B)
    (hf : Bijective f) :
    cardinal A = cardinal B := by
  ext
  exists f

example {A B : Type}
    (h : cardinal A = cardinal B) :
    ∃ f : A → B, Bijective f := by
  exact (cardinal_eq_iff A B).mp h
```

첫 예제의 `exists f`는 함수 `f`를 제시하고 이미 주어진 전단사성의 증명 `hf`로 증명을 마친다.
둘째 예제에서는 기수의 등식으로부터 전단사의 존재를 얻는다.
이 결과를 `unpack`으로 나누면 함수와 전단사성의 증명을 사용할 수 있다.
집합 `S : Set A`의 기수는 `cardinal (Elem S)`이며
두 집합을 비교할 때도 그 원소 타입의 기수를 사용한다.

```savedLean -show
theorem cardinal_eq_of_sameCardinality {A B : Type}
    (h : SameCardinality A B) : cardinal A = cardinal B :=
  (cardinal_eq_iff A B).2 h

theorem sameCardinality_of_cardinal_eq {A B : Type}
    (h : cardinal A = cardinal B) : SameCardinality A B :=
  (cardinal_eq_iff A B).1 h

namespace Cardinal

theorem eq_symm {a b : Cardinal} (h : a = b) : b = a :=
  h.symm

theorem eq_trans {a b c : Cardinal}
    (hab : a = b) (hbc : b = c) : a = c :=
  hab.trans hbc

end Cardinal
```

# 유한집합과 원소 수
%%%
tag := "cardinality-finite-sets"
file := "finite-sets"
%%%

{ref "functions-fin"}[유한한 번호]에서 `Fin n`을 자연수 값과 범위 조건으로 구성했다.
이제 각 원소에 번호를 하나씩 붙이는 전단사로 원소 수를 정의하자.

*정의* $`\{k\in\mathbb{N}:k<n\}`에서 $`A`로 가는 전단사가 존재하면
$`A`의 *원소 수가 $`n`*이라고 한다.
그러한 자연수 $`n`이 존재하는 집합을 *유한집합*이라고 한다.

```savedLean
def IsFinite : Type → Prop :=
  fun A => ∃ n : Nat, cardinal A = cardinal (Fin n)
```

원소 수가 $`n`이라는 조건은 `cardinal A = cardinal (Fin n)`으로 쓴다.
이 등식에 `ext`를 쓰면 `A`에서 `Fin n`으로 가는 전단사를 제시하는 목표가 된다.
정의에서 사용한 `Fin n → A`와 방향이 반대이지만, 전단사의 역함수도 전단사이므로 두 조건은 동치이다.
번호에서 원소로 가는 함수가 단사라는 조건은 같은 원소를 중복해서 세지 않는다는 뜻이고
전사라는 조건은 빠뜨린 원소가 없다는 뜻이다.

`Fin n`에는 항등함수로 번호를 붙일 수 있으므로 원소 수가 $`n`이며 유한하다.

```savedLean
theorem fin_isFinite (n : Nat) : IsFinite (Fin n) := by
  exists n
```

## 공집합과 한 원소 집합
%%%
tag := "cardinality-empty-and-singleton"
%%%

*보기* 공집합의 원소 수는 $`0`이다.

`Fin 0`과 공집합의 원소 타입에는 모두 원소가 없다.
정의역이 `Fin 0`인 함수는 `fun i => Fin.elim0 i`로 정의할 수 있으며
단사성과 전사성을 보일 때도 원소가 있다는 가정에서 모순을 얻는다.

번호에서 원소로 가는 함수를 제시하려면 먼저 `symm`으로 등식의 양변을 바꾸자.
그다음에 `ext`를 사용하면 `Fin 0`에서 공집합의 원소 타입으로 가는 전단사의 존재가 목표가 된다.

```savedLean
theorem empty_cardinal (A : Type) :
    cardinal (Elem (∅ : Set A)) = cardinal (Fin 0) := by
  symm
  ext
  exists (fun i : Fin 0 => Fin.elim0 i)
  constructor
  · intro i j hij
    exact Fin.elim0 i

  · intro x
    have hx : False :=
      x.property
    contradiction
```

전사성을 보이는 부분의 `x`는 공집합의 원소이므로 `x.property`는 `False`의 증명이다.
따라서 `contradiction`으로 그 경우를 마친다.

*보기* 원소 $`a` 하나로 이루어진 집합 $`\{a\}`의 원소 수는 $`1`이다.

먼저 원소 조건 $`x=a`로 이 집합을 정의하자.

```savedLean
def singleton {A : Type} (a : A) : Set A := fun x => x = a
```

유일한 번호 $`0`에 원소 $`a`를 대응시키자.
단사성을 확인하려고 번호 $`i`, $`j`를 택하면 둘 다 $`0`이므로 서로 같다.
또한 $`\{a\}`의 모든 원소가 $`a`와 같으므로 이 대응은 전사이다.

이 대응을 증명 안에서 여러 번 사용하므로 `let`으로 함수 `f`를 정의하자.
{ref "relations-local-definitions"}[앞에서는] `let`으로 대표원에 이름을 붙였으며,
이번에는 `let f (_ : Fin 1) ...`처럼 인수를 적어 함수를 정의한다.
이후에는 `f`를 함수 이름으로 사용하고 필요할 때 그 정의를 펼친다.
전사성을 증명할 때 쓰는 번호 `zero`도 같은 방법으로 정의한다.

```savedLean
theorem singleton_cardinal {A : Type} (a : A) :
    cardinal (Elem (singleton a)) = cardinal (Fin 1) := by
  symm
  ext
  -- 번호 0을 원소 a에 대응시킨다.
  let f (_ : Fin 1) : Elem (singleton a) :=
    { val := a, property := by rfl }
  exists f
  constructor
  · intro i j hij
    -- Fin 1의 두 번호는 모두 자연수 값이 0이다.
    ext
    have hi : i.val < 1 :=
      i.isLt
    have hj : j.val < 1 :=
      j.isLt
    arith

  · intro x
    -- 집합의 원소 x는 a이므로 번호 0에서 얻는다.
    let zero : Fin 1 :=
      { val := 0, isLt := by decide }
    exists zero
    ext
    exact x.property.symm
```

함수 `f`의 값은 원소 `a`와 그 원소 조건인 `a = a`의 증명을 함께 담는다.
단사성의 목표에 `ext`를 사용하면 목표가 `i.val = j.val`로 바뀐다.
두 값이 모두 $`1`보다 작은 자연수라는 조건 `i.isLt`와 `j.isLt`에 따라
두 값은 모두 $`0`이다. 이 범위 조건으로 두 값이 같음을 `arith`가 확인한다.
전사성에서는 번호 $`0`을 택하고 `ext`로 집합의 원소 값을 비교한다.
이때 `x.property`는 `x.val = a`의 증명이므로 `.symm`으로 양변의 순서를 바꾼다.

## 세 원소 집합의 원소 수
%%%
tag := "cardinality-counting-three-elements"
%%%

*보기* 자연수의 집합 $`\{10,11,12\}`의 원소 수는 $`3`이다.
이 집합을 부등식으로 정의하고 번호 $`0`, $`1`, $`2`를 각각 $`10`, $`11`, $`12`에 대응시키자.

```savedLean
def threeNumbers : Set Nat := fun k => 10 ≤ k ∧ k < 13
```

대응 함수는 $`f(i)=10+i`이다.
$`10+i=10+j`이면 $`i=j`이므로 단사이며,
집합의 원소 $`x`는 $`10\leq x<13`을 만족하므로 번호 $`x-10`에 대응한다.
원소 $`x`의 범위 조건에 따라 이 번호는 $`0`, $`1`, $`2` 중 하나이며 그 함수값은 다시 $`x`이다.
따라서 모든 원소가 함수값으로 나타나므로 함수는 전사이다.

Lean의 자연수 뺄셈은 결과가 음수가 되는 경우에 $`0`을 돌려준다.
여기서는 $`10\leq x`라는 조건이 있으므로 $`10+(x-10)=x`가 성립하며
이 등식으로 택한 번호의 함수값이 원래 원소임을 확인한다.

아래 증명에서는 `expand at hij`로 함수의 정의를 드러내고
`indisc at hij`로 함수값에 담긴 자연수의 등식을 얻는다.
이 등식에서 공통 항을 소거하는 계산은 `arith`로 확인한다.

```savedLean
theorem threeNumbers_cardinal :
    cardinal (Elem threeNumbers) = cardinal (Fin 3) := by
  symm
  ext
  -- 번호 0, 1, 2를 각각 10, 11, 12에 대응시킨다.
  let f (i : Fin 3) : Elem threeNumbers :=
    { val := 10 + i.val
      property := by
        have hi : i.val < 3 :=
          i.isLt
        constructor
        · arith
        · arith }

  exists f
  constructor
  · intro i j hij
    -- 함수값의 등식을 자연수의 등식으로 옮긴다.
    expand at hij
    indisc at hij
    ext
    arith

  · intro x
    -- 원소 x에 대응하는 번호는 x - 10이다.
    have hx : 10 ≤ x.val ∧ x.val < 13 :=
      x.property
    let i : Fin 3 :=
      { val := x.val - 10, isLt := by arith }
    -- 이 번호에 10을 더하면 원래 원소 x를 얻는다.
    exists i
    ext
    dsimp [f, i]
    arith
```

함수값을 만들 때는 `i.isLt`가 번호의 범위 `i.val < 3`을 보장한다.
이를 사용하여 `10 + i.val`이 집합의 두 부등식 조건을 만족함을 확인한다.
단사성에서 `expand at hij`로 함수값을 펼친 뒤
`indisc at hij`를 쓰면 $`10+i=10+j`라는 자연수의 등식을 얻는다.
`ext`로 두 번호의 값을 비교하면 목표가 `i.val = j.val`이 되며,
`arith`가 공통 항 $`10`을 소거하여 증명을 마친다.

전사성에서는 `x.property`에서 원소의 범위를 얻고 이를 바탕으로 번호 `i`를 만든다.
`ext`로 원소 값을 비교하고 `dsimp [f, i]`로 두 정의를 펼치면
목표는 `10 + (x.val - 10) = x.val`이며
`hx`의 하한 조건 `10 ≤ x.val`이 있으므로 자연수의 뺄셈에서도 이 등식이 성립한다.

## 연습문제: 두 원소 집합의 번호
%%%
tag := "cardinality-counting-practice"
%%%

앞의 세 원소 집합에서 사용한 번호 붙이기를 두 원소 집합에 적용해 보자.

*문제 1* (두 원소 집합의 번호)

집합 $`\{2,3\}`의 두 원소에 각각 번호 $`0`, $`1`을 붙인다.
아래 함수가 전단사임을 증명한 뒤 그 결과로 집합의 원소 수가 $`2`임을 보이라.

```savedLean -keep
def practiceIndexTwo (i : Fin 2) : Elem twoThree :=
  { val := i.val + 2
    property := by
      expand
      arith }

theorem exercise_indexTwo_bijective :
    Bijective practiceIndexTwo := by
  sorry

theorem exercise_twoThree_cardinal :
    cardinal (Elem twoThree) = cardinal (Fin 2) := by
  sorry
```

## 전단사와 원소 수
%%%
tag := "cardinality-transport"
%%%

*정리* $`A`의 원소 수가 $`n`이고 $`|A|=|B|`이면 $`B`의 원소 수도 $`n`이다.

*증명* 번호에서 $`A`로 가는 전단사에 $`A`에서 $`B`로 가는 전단사를 합성한다.
이 합성도 전단사이므로 같은 번호로 $`B`의 원소를 셀 수 있다.
기수의 등식으로 증명할 때는 목표의 `cardinal B`를 `cardinal A`로 바꾸면 된다.
`rw [← hAB]`는 등식 `hAB`를 반대 방향으로 사용하므로 이 변환을 수행한다.

```savedLean
theorem cardinality_finite_transport {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B)
    (hA : cardinal A = cardinal (Fin n)) :
    cardinal B = cardinal (Fin n) := by
  rw [← hAB]
  exact hA
```

# 자연수와 유한한 번호
%%%
tag := "cardinality-fin-conversions"
file := "finite-indices"
%%%

지금까지 공집합과 한 원소 집합, 세 원소 집합에 번호를 붙여 원소 수를 확인했다.
다음에는 번호를 붙이는 방법이 달라도 원소 수가 같음을 증명한다.
그 증명에서는 번호 하나를 지우거나 남은 번호를 옮겨야 하므로,
먼저 `Fin n`의 자연수 값을 꺼내고 범위를 바꾸는 방법을 정리하자.

{anchor "cardinality-fin-values"}[]`i : Fin n`의 자연수 값은 `i.val`이며
그 값이 범위 안에 있다는 증명은 `i.isLt : i.val < n`이다.
자연수 값을 함수에 넣거나 계산할 때는 `i.val`을 사용한다.
Lean은 자연수가 필요한 문맥에서 이 값을 자동으로 꺼낼 수도 있으며
이를 *형변환*이라고 한다.
`(i : Nat)`는 이 형변환을 명시한 표현으로 `i.val`과 같다.
증명 화면에는 같은 변환이 `↑i`로 표시되기도 하며
기호 `↑`는 `\u`로 입력한다.

```savedLean
example {n : Nat}
    (i : Fin n) :
    (i : Nat) = i.val := by
  rfl
```

거꾸로 자연수 `x`를 값으로 갖는 `Fin n`의 원소를 만들려면 `x < n`의 증명이 필요하다.
`hx : x < n`이 주어졌을 때는 다음과 같이 `x`를 값으로 택한다.

```savedLean
def cardinality_fin_from_bound {n : Nat}
    (x : Nat)
    (hx : x < n) :
    Fin n :=
  { val := x, isLt := hx }
```

`val`에는 자연수 `x`를 적고 `isLt`에는 주어진 범위 조건의 증명 `hx`를 적는다.
범위 조건을 새로 증명해야 하는 경우에는 `isLt := by` 아래에 그 증명을 적는다.

## 범위 변경과 번호 이동
%%%
tag := "cardinality-fin-bounds"
%%%

`i : Fin n`의 값은 $`n`보다 작으므로 $`n+1`보다도 작다.
따라서 같은 자연수 값을 사용하여 `Fin (n + 1)`의 원소를 만들 수 있다.

```savedLean
def cardinality_fin_embed_succ {n : Nat}
    (i : Fin n) : Fin (n + 1) :=
  { val := i.val
    isLt := by
      have hi : i.val < n :=
        i.isLt
      arith }
```

이 변환은 `i.castSucc`로도 쓸 수 있으며 자연수 값은 그대로 유지된다.
한편 번호 값을 하나 늘리려면 `i.succ`를 사용한다.
`i.succ`의 타입은 `Fin (n + 1)`이며
자연수 값은 `i.val + 1`이다.

```savedLean
example {n : Nat}
    (i : Fin n) :
    i.castSucc.val = i.val := by
  rfl

example {n : Nat}
    (i : Fin n) :
    i.succ.val = i.val + 1 := by
  rfl
```

함수 `f : Fin (n + 1) → A`에 대하여
`f i.castSucc`는 기존 번호에서의 함수값이고
`f i.succ`는 그다음 번호에서의 함수값이다.

더 큰 범위 `Fin m`으로 옮길 때도 같은 원리로 자연수 값을 유지한다.
`h : n ≤ m`이면 모든 `Fin n`의 번호가 `Fin m`의 범위 안에 있으므로
`i.castLE h : Fin m`을 사용할 수 있다.

```savedLean
def cardinality_fin_castLE {m n : Nat}
    (i : Fin n)
    (h : n ≤ m) :
    Fin m := by
  exact i.castLE h

example {m n : Nat} (i : Fin n)
    (h : n ≤ m) :
    (i.castLE h).val = i.val := by
  rfl
```

첫 예제에서는 `i.castLE h`가 목표 타입 `Fin m`의 원소이므로 `exact`로 이를 제시한다.
이렇게 범위를 넓힐 때는 기존의 범위 조건을 사용할 수 있다.
범위를 줄일 때는 옮길 번호가 새 범위 안에 있다는 사실을 따로 확인해야 한다.
`Fin (n + 1)`에는 마지막 번호 $`n`도 들어 있으므로
같은 값을 `Fin n`으로 옮기려면 `i.val < n`의 증명이 필요하다.

```savedLean
def cardinality_fin_castLT {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val < n) :
    Fin n :=
  { val := i.val, isLt := hi }
```

범위 조건 `hi`를 사용하여 같은 값을 새 범위로 옮기는 표현이 `i.castLT hi`이다.
아래의 결과는 `Fin n`의 원소이며 자연수 값은 원래 번호와 같다.

```savedLean
example {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val < n) :
    (i.castLT hi).val = i.val := by
  rfl
```

*보기* 마지막 번호가 아니라는 가정 `hi : i.val ≠ n`만 주어져도
`i.isLt : i.val < n + 1`과 함께 `i.val < n`을 얻을 수 있다.

```savedLean
def cardinality_fin_pred {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val ≠ n) :
    Fin n :=
  { val := i.val
    isLt := by
      have hbound : i.val < n + 1 :=
        i.isLt
      arith }
```

## 번호의 같음
%%%
tag := "cardinality-fin-equality"
%%%

앞에서 배운 대로 같은 `Fin n`의 두 원소는 자연수 값으로 비교한다.
목표 `i = j`에 `ext`를 쓰면 `i.val = j.val`이 남는다.
거꾸로 `h : i = j`가 주어졌다면 `rw [h]`로 값의 등식을 증명할 수 있다.

```savedLean
theorem cardinality_fin_eq_iff_values {n : Nat}
    (i j : Fin n) :
    i = j ↔ i.val = j.val := by
  constructor
  · intro h
    rw [h]

  · intro h
    ext
    exact h
```

서로 다른 범위의 번호를 비교할 때는 범위를 맞춘 뒤 `ext`를 사용한다.
예를 들어 `i : Fin n`과 `j : Fin (n + 1)`의 자연수 값이 같다면
`i`를 `i.castSucc`로 옮겨 두 번호가 같음을 보일 수 있다.

```savedLean
example {n : Nat}
    (i : Fin n) (j : Fin (n + 1))
    (h : i.val = j.val) :
    i.castSucc = j := by
  ext
  exact h
```

{anchor "cardinality-fin-reference"}[]아래 표에서 `i : Fin n`이라 하고
다른 범위로 옮길 때는 새 범위의 크기를 `m`으로 둔다.

:::table +header (align := left)
*
  * 할 일
  * 표현
  * 조건 또는 결과
*
  * 자연수 값
  * `i.val`, `(i : Nat)`
  * 결과는 `Nat`이며 증명 화면에서는 `↑i`로 표시될 수도 있다
*
  * 범위 조건
  * `i.isLt`
  * `i.val < n`의 증명
*
  * 자연수에서 번호로
  * `{ val := x, isLt := hx }`
  * `hx : x < n`이 필요하며 결과는 `Fin n`
*
  * 범위를 한 칸 늘리기
  * `i.castSucc`
  * 타입은 `Fin (n + 1)`이며 값은 `i.val`
*
  * 다음 번호
  * `i.succ`
  * 타입은 `Fin (n + 1)`이며 값은 `i.val + 1`
*
  * 더 큰 범위로
  * `i.castLE h`
  * `h : n ≤ m`이 필요하며 결과는 `Fin m`
*
  * 새 범위의 증명으로
  * `i.castLT hi`
  * `hi : i.val < m`이 필요하며 결과는 `Fin m`
*
  * 번호의 등식
  * `ext`
  * `i = j`라는 목표를 `i.val = j.val`로 바꾼다
:::

# 원소 수의 유일성
%%%
tag := "cardinality-uniqueness"
file := "uniqueness"
%%%

한 집합에 두 가지 방법으로 번호를 붙였다고 하자.
각 방법에서 번호로 쓴 `Fin m`과 `Fin n`은 모두 그 집합과 전단사로 연결되므로
두 번호 집합 사이에도 전단사가 있다.
따라서 원소 수가 하나로 정해짐을 보이려면 이러한 전단사에서 $`m=n`을 얻어야 한다.

이 절의 결론은 다음과 같다.

> 한 집합 `A`에 대해 `cardinal A = cardinal (Fin m)`과
> `cardinal A = cardinal (Fin n)`이 모두 성립하면 `m = n`이다.

예를 들어 앞에서 세 원소 집합으로 센 `threeNumbers`에 다른 번호를 붙여
`cardinal (Elem threeNumbers) = cardinal (Fin n)`을 얻었다면 $`n=3`이어야 한다.
이 결론을 사용할 때는 번호를 지우는 함수를 다시 구성할 필요 없이
아래에서 증명할 `finite_cardinal_unique`에 두 등식의 증명을 주면 된다.

증명은 다음 세 단계로 진행한다.

1. `Fin (m + 1)`에서 `Fin (n + 1)`로 가는 단사함수에서
   정의역의 번호 하나와 그 함수값을 지워 `Fin m`에서 `Fin n`으로 가는 단사함수를 만든다.
2. 이 축소를 귀납법으로 반복하여 `Fin m`에서 `Fin n`으로 가는 단사가 있으면 $`m\leq n`임을 보인다.
   이는 서로 다른 $`m`개의 원소를 $`n`개의 자리에 넣으려면 자리가 충분해야 한다는 비둘기집 원리이다.
3. 전단사와 그 역함수에 두 번째 결과를 적용하면 $`m\leq n`과 $`n\leq m`을 얻으므로 $`m=n`이다.

먼저 첫 단계에 필요한 번호의 재배열을 구성하자.
먼저 각 단계의 수학적 설명을 읽고 {ref "cardinality-number-unique"}[세는 방법과 원소 수]에서
결론이 어떻게 이어지는지 확인해도 좋다. 번호의 재배열을 Lean으로 직접 구현하려면
그 뒤에 각 코드 블록의 범위 조건과 귀납 가정을 살펴보면 된다.

## 번호의 재배열
%%%
tag := "cardinality-erasing-an-index"
%%%

번호 $`0,1,\ldots,n`에서 번호 $`r` 하나를 지운 뒤
남은 번호들에 $`0,1,\ldots,n-1`을 차례로 대응시켜 보자.
$`r`보다 작은 번호는 그대로 두고 $`r`보다 큰 번호에서는 $`1`을 빼면 된다.

```savedLean
def eraseIndex (r k : Nat) : Nat :=
  if k < r then k else k - 1
```

`if k < r then k else k - 1`은 조건 `k < r`이 참이면 `k`를
그렇지 않으면 `k - 1`을 값으로 갖는다.

*보기* $`0,1,2,3,4` 중 번호 $`2`를 지우면
남은 번호 $`0,1,3,4`는 각각 $`0,1,2,3`으로 바뀐다.

```savedLean
example :
    eraseIndex 2 0 = 0 ∧ eraseIndex 2 1 = 1 ∧
    eraseIndex 2 3 = 2 ∧ eraseIndex 2 4 = 3 := by
  decide
```

그런데 함수 `eraseIndex`에는 지운 번호 $`2`도 넣을 수 있다.
이때는 $`2-1=1`이므로 지우지 않은 번호 $`1`과 같은 값을 얻는다.

```savedLean
example :
    eraseIndex 2 1 = eraseIndex 2 2 := by
  rfl
```

따라서 `eraseIndex`의 단사성을 사용할 때는 지운 번호를 제외해야 한다.
아래에서는 이 조건을 `k ≠ r`과 같은 가정으로 명시한다.

남은 번호 $`k`, 곧 $`0\leq k\leq n`이고 $`k\ne r`인 번호에 대하여
새 번호가 $`n`보다 작다는 사실부터 확인하자.
$`k<r`이면 $`k<r\leq n`이므로 그대로 둔 번호가 $`n`보다 작다.
$`k\geq r`이면 $`k\ne r`에 따라 $`r<k`이며
$`0<k\leq n`에서 $`k-1<n`을 얻는다.

Lean에서는 `by_cases h : k < r`로 두 경우를 나눈다.
첫 경우에는 `h : k < r`을, 둘째 경우에는 `h : ¬ k < r`을 가정으로 갖는다.
각 경우에서 `eraseIndex r k`를 계산하려면 이 가정으로 `if`의 어느 쪽 값을 사용할지 정해야 한다.

이를 위한 정리가 `ite_eq_left`와 `ite_eq_right`이다.
이름의 `ite`는 `if–then–else`의 줄임말이며 `left`는 `then` 쪽의 식을, `right`는 `else` 쪽의 식을 가리킨다.
`h : k < r`일 때 `ite_eq_left h`는 `(if k < r then k else k - 1) = k`의 증명이다.
조건이 성립하지 않는다는 증명 `h : ¬ k < r`을 `ite_eq_right`에 넣으면
같은 `if` 식의 값이 `k - 1`이라는 등식의 증명을 얻는다.

```savedLean
example (r k : Nat)
    (h : k < r) :
    (if k < r then k else k - 1) = k := by
  exact ite_eq_left h

example
    (r k : Nat)
    (h : ¬ k < r) :
    (if k < r then k else k - 1) = k - 1 := by
  exact ite_eq_right h
```

이 등식들을 `rw`에 넣으면 목표에 있는 `if` 식을 해당 값으로 바꿀 수 있다.
`rw`에는 등식의 증명뿐 아니라 정의 이름도 넣을 수 있으므로
먼저 `rw [eraseIndex]`로 함수값을 정의식으로 바꾸어 `if` 식을 드러내자.

```savedLean
theorem eraseIndex_lt {n r k : Nat}
    (hr : r < n + 1)
    (hk : k < n + 1)
    (hne : k ≠ r) :
    eraseIndex r k < n := by
  rw [eraseIndex]
  by_cases h : k < r
  · rw [ite_eq_left h]
    arith

  · rw [ite_eq_right h]
    arith
```

첫 줄의 `rw [eraseIndex]`로 정의를 펼치면 목표는
`(if k < r then k else k - 1) < n`이다.
이어서 `by_cases h : k < r`로 조건 `k < r`의 성립 여부에 따라 두 경우를 나눈다.
첫 경우에는 `rw [ite_eq_left h]`로 목표가 `k < n`으로 바뀌며
`arith`가 `h : k < r`과 `hr : r < n + 1`에서 이 부등식을 얻는다.
둘째 경우에는 `rw [ite_eq_right h]`로 목표가 `k - 1 < n`으로 바뀐다.
이때 `h`와 `hne`에서 `r < k`를 얻고 `hk`에서 `k ≤ n`을 얻으므로
`arith`가 남은 부등식을 증명한다.

이번에는 두 새 번호가 같을 때 원래 번호도 같음을 보이자.
원래 번호가 모두 $`r`보다 작으면 새 번호가 곧 원래 번호이므로 결론을 얻는다.
모두 $`r`보다 크면 새 번호의 등식 양변에 $`1`을 더하여 원래 번호의 같음을 얻는다.
한 번호만 $`r`보다 작으면 그 새 번호는 $`r`보다 작고 다른 새 번호는 $`r` 이상이므로 같을 수 없다.

```savedLean
theorem eraseIndex_injective {r x y : Nat}
    (hx : x ≠ r)
    (hy : y ≠ r)
    (h : eraseIndex r x = eraseIndex r y) :
    x = y := by
  -- 두 번호를 지운 번호 r의 앞뒤에 따라 나눈다.
  rw [eraseIndex, eraseIndex] at h
  by_cases hxr : x < r
  · by_cases hyr : y < r

    · -- 양쪽 모두 원래 번호를 유지한다.
      rw [ite_eq_left hxr, ite_eq_left hyr] at h
      arith

    · -- 새 번호가 r의 양쪽에 있으므로 같을 수 없다.
      rw [ite_eq_left hxr, ite_eq_right hyr] at h
      arith

  · by_cases hyr : y < r

    · -- 이번에도 새 번호가 r의 양쪽에 있다.
      rw [ite_eq_right hxr, ite_eq_left hyr] at h
      arith

    · -- 양변에 1을 더하면 원래 번호의 등식을 얻는다.
      rw [ite_eq_right hxr, ite_eq_right hyr] at h
      arith
```

첫 줄에서는 `rw`로 가정 `h`의 왼쪽에 있는 `eraseIndex r x`와
오른쪽에 있는 `eraseIndex r y`를 차례로 펼친다.
이어서 `x < r`과 `y < r`을 각각 나누어 네 경우를 다룬다.
각 경우에 `rw [...] at h`로 두 `if` 식을 바꾸면
원래 번호나 $`1`을 뺀 번호 사이의 등식이 남는다.
`arith`는 이 등식과 각 경우의 부등식으로 `x = y`를 증명하거나 모순을 얻는다.

## 단사함수의 축소
%%%
tag := "cardinality-removing-a-pair"
%%%

*정리* `Fin (m + 1)`에서 `Fin (n + 1)`로 가는 단사함수가 있으면
`Fin m`에서 `Fin n`으로 가는 단사함수가 존재한다.

*증명* 단사함수 $`f`의 정의역에서 $`0`을 지우고 공역에서 $`f(0)`을 지우자.
나머지 정의역의 번호는 $`i+1`로 쓸 수 있으며 단사성에 따라 $`f(i+1)\ne f(0)`이다.
공역에서 $`f(0)`을 제외한 번호들에 `eraseIndex`로 새 번호를 붙이면
$`f(i+1)`에 대응하는 번호는 $`n`보다 작다.
이를 $`g(i)`로 두면 `Fin m`에서 `Fin n`으로 가는 함수를 얻는다.

$`g(i)=g(j)`라고 하자.
$`f(i+1)`과 $`f(j+1)`은 모두 지운 번호 $`f(0)`과 다르므로
`eraseIndex_injective`에 따라 $`f(i+1)=f(j+1)`이다.
여기에 $`f`의 단사성을 사용하면 $`i+1=j+1`이므로 $`i=j`이다.
이로써 $`g`도 단사임을 얻는다.

아래에서 `first`는 번호 $`0`이고 `next i`는 번호 $`i+1`이다.
`Nat.succ_lt_succ`는 `i.val < m`에서 `i.val + 1 < m + 1`을 얻는 정리이므로
`next i`가 정의역의 범위 안에 있음을 보장한다.
또한 `have hne (i : Fin m) : ... := by`는 임의의 `i`에 대하여 성립하는 명제를 증명한다.
이후에는 `hne i`로 해당 번호에서의 증명을 사용할 수 있다.

```savedLean
theorem fin_injection_remove {m n : Nat}
    (f : Fin (m + 1) → Fin (n + 1))
    (hf : Injective f) :
    ∃ g : Fin m → Fin n, Injective g := by
  -- 정의역의 0을 지우고 나머지 번호를 i + 1로 쓴다.
  let first : Fin (m + 1) :=
    { val := 0, isLt := by arith }
  let next (i : Fin m) : Fin (m + 1) :=
    { val := i.val + 1
      isLt := Nat.succ_lt_succ i.isLt }

  -- 단사성에 따라 나머지 함수값은 f(0)과 다르다.
  have hne (i : Fin m) :
      (f (next i)).val ≠ (f first).val := by
    intro h
    have hfi : f (next i) = f first := by
      ext
      exact h

    have hi : next i = first :=
      hf (next i) first hfi
    have hiVal : (next i).val = first.val := by
      rw [hi]

    expand at hiVal
    arith

  -- 공역에서 f(0)을 지우고 번호를 다시 붙인다.
  let g (i : Fin m) : Fin n :=
    { val := eraseIndex (f first).val (f (next i)).val
      isLt := eraseIndex_lt
        (f first).isLt (f (next i)).isLt (hne i) }

  have hg : Injective g := by
    intro i j hij
    -- 새 번호의 등식에서 원래 함수값의 등식을 얻는다.
    have hVal : (g i).val = (g j).val := by
      rw [hij]

    have hfi : f (next i) = f (next j) := by
      ext
      exact eraseIndex_injective (hne i) (hne j) hVal

    -- f의 단사성으로 i + 1 = j + 1을 얻는다.
    have hi : next i = next j :=
      hf (next i) (next j) hfi
    have hiVal : (next i).val = (next j).val := by
      rw [hi]

    -- 양변의 1을 소거하여 i = j를 보인다.
    ext
    expand at hiVal
    arith

  exists g
```

`hne i`는 `f (next i)`와 지울 번호 `f first`의 자연수 값이 다르다는 증명이다.
만약 두 함수값이 같다면 `hf`로 `next i = first`를 얻어 $`i+1=0`이라는 모순이 생긴다.
함수 `g`를 정의할 때는 `eraseIndex_lt`에 이 증명을 주어 새 번호의 범위를 확인한다.

`hg`의 가정 `hij : g i = g j`에서 자연수 값의 등식 `hVal`을 얻는다.
`g`의 정의를 펼치면 이 등식은 `eraseIndex`로 얻은 두 새 번호가 같다는 뜻이다.
따라서 `eraseIndex_injective`로 원래 함수값의 같음을 얻고
`hf`로 `next i = next j`를 얻는다.
그 자연수 값은 각각 $`i+1`, $`j+1`이므로 $`i=j`이다.
마지막의 `exists g`는 구성한 함수를 제시하며 단사성은 이미 얻은 `hg`로 확인된다.

## 비둘기집 원리
%%%
tag := "cardinality-pigeonhole"
%%%

*정리* `Fin m`에서 `Fin n`으로 가는 단사함수가 있으면 $`m\leq n`이다.

*증명* 공역의 번호 수 $`n`에 대한 귀납법을 사용한다.
$`n=0`이면 공역에 원소가 없으므로 정의역도 비어 있어야 하며 $`m=0`이다.
이제 공역의 번호 수가 $`n+1`이라고 하자.
정의역이 비어 있으면 결론이 성립하며
정의역의 번호 수가 $`m+1`이면 앞의 정리로 한 쌍을 지워 `Fin m`에서 `Fin n`으로 가는 단사를 얻는다.
귀납 가정에 따라 $`m\leq n`이므로 $`m+1\leq n+1`이다.

이 증명에서는 한 쌍을 지울 때 정의역과 공역의 번호 수가 모두 하나씩 줄어든다.
따라서 귀납 가정을 줄어든 정의역에도 적용할 수 있어야 한다.
그런데 `induction n`만 쓰면 정의역의 번호 수 `m`은 처음 정한 값으로 고정된다.
`m = k + 1`인 경우에 얻는 귀납 가정은 다음 형태이다.

```
ih : ∀ (f : Fin (k + 1) → Fin n),
  Injective f → k + 1 ≤ n
```

이 귀납 가정이 받는 함수의 정의역은 `Fin (k + 1)`이다.
앞의 정리로 한 쌍을 지운 뒤 얻은 함수는 `g : Fin k → Fin n`이므로
정의역이 맞지 않아 `ih g hg`에 사용할 수 없다.

`induction n generalizing m`을 쓰면 `m`을 고정하지 않고 모든 `m`에 대하여 귀납법을 적용한다.
이때 귀납 가정은 다음과 같이 임의의 정의역 크기를 받을 수 있다.

```
ih : ∀ {m : Nat} (f : Fin m → Fin n),
  Injective f → m ≤ n
```

이제 `g : Fin k → Fin n`과 `hg : Injective g`를 넣으면
암시적 인수 `m`이 `k`로 정해지므로 `ih g hg`에서 `k ≤ n`을 얻는다.
아래 코드에서는 `cases m`으로 정의역의 번호 수를 $`0`과 $`k+1`의 두 경우로 나눈다.
코드의 `succ m`에서 새로 붙인 이름 `m`은 이 설명의 $`k`에 해당한다.

```savedLean
theorem fin_injective_le {m n : Nat} (f : Fin m → Fin n)
    (hf : Injective f) :
    m ≤ n := by
  -- 정의역의 크기도 달라질 수 있도록 귀납법을 쓴다.
  induction n generalizing m with
  | zero =>
      -- 공역이 공집합이면 정의역도 공집합이어야 한다.
      cases m with
      | zero => arith
      | succ m =>
          let first : Fin (m + 1) :=
            { val := 0, isLt := by arith }
          exact Fin.elim0 (f first)

  | succ n ih =>
      cases m with
      | zero => arith
      | succ m =>
          -- 한 쌍을 지워 양쪽 번호 수를 하나씩 줄인다.
          unpack fin_injection_remove f hf with ⟨g, hg⟩
          have hmn : m ≤ n :=
            ih g hg
          -- m ≤ n에서 m + 1 ≤ n + 1을 얻는다.
          arith
```

공역이 `Fin 0`이고 정의역에 번호 $`0`인 `first`가 있다면
`f first : Fin 0`에서 `Fin.elim0`으로 모순을 얻는다.
양쪽 번호 수가 모두 양수인 경우에는 `fin_injection_remove`로 한 쌍을 지운 뒤
귀납 가정에서 얻은 `m ≤ n`으로 `m + 1 ≤ n + 1`을 증명한다.

*보기* `Fin 3`에서 `Fin 2`로 가는 함수는 단사가 될 수 없다.
단사라고 가정하면 방금 증명한 정리에 따라 $`3\leq2`가 되어 모순이다.

```savedLean
theorem three_into_two_not_injective (f : Fin 3 → Fin 2) :
    ¬ Injective f := by
  intro hf
  have h : 3 ≤ 2 := by
    exact fin_injective_le f hf

  arith
```

이 결과를 세 사람을 두 방에 배정하는 상황에 적용하자.
사람의 번호를 `Fin 3`, 방의 번호를 `Fin 2`로 두면 배정은 함수 `f : Fin 3 → Fin 2`이다.
서로 다른 두 사람이 같은 방에 배정된다는 것은
`i ≠ j ∧ f i = f j`를 만족하는 번호 `i`, `j`가 존재한다는 뜻이다.

*보기* 세 사람을 두 방에 배정하면 같은 방에 배정된 서로 다른 두 사람이 있다.

*풀이* 그런 두 사람이 없다고 가정하자.
같은 방에 배정된 번호 $`i`, $`j`가 서로 다르다면 처음에 없다고 가정한 두 사람을 찾은 셈이다.
따라서 $`i=j`이며 배정 함수가 단사가 된다. 이는 앞의 정리와 모순이다.

```savedLean
theorem three_into_two_collision (f : Fin 3 → Fin 2) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  by_contra hCollision
  apply three_into_two_not_injective f
  intro i j hij
  -- 같은 함수값을 갖는 서로 다른 두 번호가 있으면 처음 가정과 모순이다.
  by_contra hne
  apply hCollision
  exists i
  exists j
```

`apply three_into_two_not_injective f` 뒤에는 `Injective f`가 목표로 남는다.
단사성을 증명하는 동안 `i ≠ j`라고 가정하면
`hne`와 `hij`가 처음의 존재명제에 필요한 두 조건을 모두 제공한다.
이처럼 단사가 될 수 없다는 일반적인 결론으로 실제로 겹치는 한 쌍의 존재를 얻는다.

## 세는 방법과 원소 수
%%%
tag := "cardinality-number-unique"
%%%

*정리* `Fin m`과 `Fin n`의 크기가 같으면 $`m=n`이다.

*증명* 주어진 전단사와 그 역함수는 모두 단사이다.
각 함수에 앞의 정리를 적용하면 $`m\leq n`과 $`n\leq m`을 얻는다.
따라서 $`m=n`이다.

```savedLean
theorem fin_sameCardinality_eq {m n : Nat}
    (h : SameCardinality (Fin m) (Fin n)) :
    m = n := by
  -- 양방향의 전단사를 각각 택한다.
  have hReverse : SameCardinality (Fin n) (Fin m) :=
    sameCardinality_symm h
  unpack h with ⟨f, hf⟩
  unpack hReverse with ⟨g, hg⟩

  -- 각 단사성에서 두 번호 수 사이의 부등식을 얻는다.
  have hmn : m ≤ n :=
    fin_injective_le f hf.inj
  have hnm : n ≤ m :=
    fin_injective_le g hg.inj
  -- m ≤ n과 n ≤ m을 합치면 m = n이다.
  arith
```

기수의 등식에서 전단사의 존재를 얻으면 다음과 같이 같은 결론을 사용할 수 있다.

```savedLean
theorem cardinal_fin_eq {m n : Nat}
    (h : cardinal (Fin m) = cardinal (Fin n)) :
    m = n := by
  apply fin_sameCardinality_eq
  exact (cardinal_eq_iff _ _).mp h
```

*정리* 한 집합의 원소 수가 $`m`이면서 $`n`이면 $`m=n`이다.

*증명* 두 기수의 등식 $`|A|=|\operatorname{Fin}(m)|`와
$`|A|=|\operatorname{Fin}(n)|`에서 $`|\operatorname{Fin}(m)|=|\operatorname{Fin}(n)|`를 얻는다.
방금 증명한 정리를 사용하면 $`m=n`이다.

```savedLean
theorem finite_cardinal_unique {A : Type} {m n : Nat}
    (hm : cardinal A = cardinal (Fin m))
    (hn : cardinal A = cardinal (Fin n)) :
    m = n := by
  apply cardinal_fin_eq
  exact hm.symm.trans hn
```

`hm.symm`으로 첫 등식의 방향을 바꾸면 `cardinal (Fin m) = cardinal A`를 얻는다.
여기에 `.trans hn`으로 두 번째 등식을 이어 붙이면 두 번호 타입의 기수가 같다는 등식이 된다.

앞에서 센 집합에 이 정리를 적용하면 다음과 같다. 첫 번째 인수는 새로운 방법으로 센 결과이고,
두 번째 인수는 이미 증명한 원소 수이다.

```savedLean
example (n : Nat)
    (hn : cardinal (Elem threeNumbers) = cardinal (Fin n)) :
    n = 3 := by
  exact finite_cardinal_unique hn threeNumbers_cardinal
```

# 유한기수와 자연수
%%%
tag := "cardinality-natural-cardinals"
file := "natural-cardinals"
%%%

앞의 정리에 따라 $`\operatorname{Fin}(m)`과 $`\operatorname{Fin}(n)`의 기수가 같으면 $`m=n`이다.
따라서 자연수 $`n`을 $`\operatorname{Fin}(n)`의 기수에 대응시키는 함수는 단사이다.
이 대응을 정의하고 두 자연수의 등식과 그 기수의 등식을 연결하자.

```savedLean
namespace Cardinal

def ofNat (n : Nat) : Cardinal := cardinal (Fin n)
theorem ofNat_eq_iff (m n : Nat) :
    ofNat m = ofNat n ↔ m = n := by
  constructor
  · exact cardinal_fin_eq
  · intro h
    rw [h]

end Cardinal
```

`ofNat_eq_iff`는 서로 다른 자연수가 서로 다른 기수에 대응함을 보인다.
이 단사성을 바탕으로 `(n : Cardinal)`을 `Cardinal.ofNat n`의 표기로 사용하겠다.
기수가 필요한 문맥에서는 자연수를 기수로 바꾸는 형변환이 적용되며
증명 화면에는 같은 변환이 `↑n`으로 나타날 수 있다.
따라서 `cardinal A = n`은 `cardinal A = cardinal (Fin n)`이라는 뜻이다.

```savedLean -show
namespace Cardinal
instance : NatCast Cardinal := ⟨ofNat⟩
instance (n : Nat) : OfNat Cardinal n := ⟨ofNat n⟩
end Cardinal
```

```savedLean
theorem cardinal_fin (n : Nat) :
    cardinal (Fin n) = (n : Cardinal) := by
  rfl
```

예를 들어 `cardinal (Fin 3) = 3`은 오른쪽의 $`3`을 유한기수로 사용한 등식이다.
자연수의 곱으로 원소 수를 나타내는 `cardinal A = m * n`에서는
먼저 자연수의 곱 `m * n`을 구한 뒤 그 값을 기수로 바꾼다.

## 원소 수의 자연수 값
%%%
tag := "cardinality-natural-value"
%%%

`cardinal A`는 유한집합과 무한집합 모두에 대해 정의한 기수이다.
유한집합의 원소 수를 자연수 계산에 사용하려면 그 수를 `Nat`의 값으로 꺼내야 한다.
이를 위해 유한성의 증명 `hA : IsFinite A`에서 자연수 $`n`을 골라
`cardinality A hA`로 정의하자.

`hA`는 `∃ n : Nat, cardinal A = n`의 증명이므로
`cardinalityData`에 `Classical.choose`로 고른 자연수와 `Classical.choose_spec`으로 얻은 등식의 증명을 함께 담는다.
이어지는 정의와 정리에서는 `.val`과 `.property`를 각각 꺼낸다.

```savedLean
noncomputable def cardinalityData (A : Type)
    (hA : IsFinite A) : {n : Nat // cardinal A = n} :=
  { val := Classical.choose hA
    property := Classical.choose_spec hA }

noncomputable def cardinality (A : Type)
    (hA : IsFinite A) : Nat :=
  (cardinalityData A hA).val
theorem cardinality_spec (A : Type)
    (hA : IsFinite A) :
    cardinal A = cardinality A hA := by
  exact (cardinalityData A hA).property

theorem cardinality_eq {A : Type} {n : Nat}
    (hA : IsFinite A)
    (hn : cardinal A = n) :
    cardinality A hA = n := by
  exact finite_cardinal_unique (cardinality_spec A hA) hn
```

`cardinality_spec`은 선택한 자연수가 원소 수임을 보인다.
다른 자연수 `n`에 대해 `cardinal A = n`을 증명했다면
`cardinality_eq`와 원소 수의 유일성으로 `cardinality A hA = n`을 얻는다.
따라서 유한성의 증명이나 번호를 붙이는 방법이 달라져도 이 자연수 값은 같다.

*보기* `Fin 3`의 원소 수는 `cardinal_fin 3`으로 확인했으므로
`cardinality`의 값도 $`3`이다.

```savedLean
example :
    cardinality (Fin 3) (fin_isFinite 3) = 3 := by
  exact cardinality_eq (fin_isFinite 3) (cardinal_fin 3)
```

# 무한집합
%%%
tag := "cardinality-infinite-sets"
file := "infinite-sets"
%%%

유한집합의 원소는 어떤 자연수 $`n`을 택하여 $`n`개의 번호로 정확히 셀 수 있다.
어느 자연수를 택해도 이러한 번호 붙이기가 불가능한 경우를 다음과 같이 정의한다.

*정의* 유한집합이 아닌 집합을 *무한집합*이라고 한다.

```savedLean
def IsInfinite : Type → Prop := fun A => ¬ IsFinite A
```

자연수 전체가 무한함을 보이기 위해
먼저 자연수에서 유한한 번호 집합으로 가는 함수가 단사일 수 없음을 보이자.

*정리* 자연수에서 `Fin n`으로 가는 단사함수는 존재하지 않는다.

*증명* 그러한 함수가 있다고 가정하고 자연수 중 $`0,1,\ldots,n`에서의 값만 보자.
정의역을 이 원소들로 제한해도 단사이므로 `Fin (n + 1)`에서 `Fin n`으로 가는 단사를 얻는다.
비둘기집 원리에 따라 $`n+1\leq n`이 되어 모순이다.

```savedLean
theorem no_injection_nat_fin (n : Nat) (f : Nat → Fin n) :
    ¬ Injective f := by
  intro hf
  -- 처음 n + 1개의 자연수에 정의역을 제한한다.
  let g (i : Fin (n + 1)) : Fin n := f i.val
  have hg : Injective g := by
    intro i j hij
    ext
    exact hf i.val j.val hij

  -- 비둘기집 원리에서 n + 1 ≤ n이라는 모순을 얻는다.
  have hbound : n + 1 ≤ n :=
    fin_injective_le g hg
  arith
```

여기서 `g`는 `Fin (n + 1)`의 번호를 자연수 값으로 꺼내 `f`에 넣는 함수이다.
`hf`로 두 자연수 값이 같음을 얻은 뒤 `ext`를 사용하면 `g`의 단사성을 확인할 수 있다.

{anchor "cardinality-natural-injection"}[]*정리* 자연수에서 $`A`로 가는 단사함수가 존재하면 $`A`는 무한집합이다.

*증명* $`A`가 유한하다고 가정하자.
그러면 어떤 자연수 $`n`에 대하여 전단사 $`r:A\to\operatorname{Fin}(n)`가 존재한다.
주어진 단사함수 $`f : \mathbb{N}\to A`에 $`r`을 합성하면 자연수에서 `Fin n`으로 가는 단사가 되어 모순이다.

유한성의 가정은 `∃ n : Nat, cardinal A = n`이므로 먼저 번호 수와 기수의 등식을 꺼낸다.
이 등식에 `cardinal_eq_iff`를 사용하면 `A`에서 `Fin n`으로 가는 전단사의 존재를 얻으므로
다시 `unpack`으로 함수와 전단사성의 증명을 꺼낼 수 있다.

```savedLean
theorem infinite_of_nat_injection {A : Type} (f : Nat → A)
    (hf : Injective f) :
    IsInfinite A := by
  intro hA
  -- A가 유한하다고 가정하여 유한한 번호를 붙인다.
  unpack hA with ⟨n, hn⟩
  unpack (cardinal_eq_iff A (Fin n)).mp hn with ⟨r, hr⟩

  -- 두 단사함수를 합성하면 Nat에서 Fin n으로 가는 단사이다.
  apply no_injection_nat_fin n (r ∘ f)
  exact injective_compose f r hf hr.inj
```

자연수의 항등함수에 이 정리를 사용하면 자연수 전체가 무한집합임을 얻는다.

```savedLean
theorem nat_isInfinite : IsInfinite Nat := by
  exact infinite_of_nat_injection
    (identity Nat) (identity_injective Nat)
```


# 번호 쌍과 집합의 곱
%%%
tag := "cardinality-product-numbering"
file := "product-numbering"
%%%

두 집합의 곱을 세려면 먼저 번호 쌍을 하나의 번호로 바꾸는 방법이 필요하다.
첫 번호의 범위가 $`m`, 둘째 번호의 범위가 $`n`이면
$`(i,j)`에 번호 $`i+jm`을 붙일 수 있다.
이 번호를 $`m`으로 나눈 나머지와 몫에서 각각 $`i`, $`j`를 되찾는다.

$`0\leq i<m`이고 $`0\leq j<n`이면
$`i+jm<(j+1)m\leq nm=mn`이므로 새 번호도 범위 안에 있다.
또한 $`i<m`이므로 $`i+jm`을 $`m`으로 나눈 나머지는 $`i`이고 몫은 $`j`이다.
거꾸로 $`0\leq x<mn`인 번호에서 출발하면
나머지와 몫은 각각 $`m`, $`n`보다 작으며
$`x=(x\bmod m)+\lfloor x/m\rfloor m`에 따라 원래 번호를 복원한다.
이때 번호 $`x`가 존재하면 $`mn>0`이므로 $`m>0`과 $`n>0`을 사용할 수 있다.
한쪽이 $`0`이면 `Fin (m * n)`과 `Fin m × Fin n` 모두 원소가 없다.

*보기* `Fin (m * n)`에서 `Fin m × Fin n`으로 가는 전단사를 구성하자.
아래 함수는 번호 $`x`를 나머지와 몫으로 나누며 각 범위 조건은 `arith`로 확인한다.
단사성에서는 `indisc : 2 at hxy`로 순서쌍과 각 번호의 등식을 차례로 비교하여
나머지와 몫이 같다는 조건을 얻는다. 전사성에서도 `ext : 2`로 두 성분과 그 자연수 값을 차례로 비교한다.

```savedLean
def finProduct (m n : Nat) (x : Fin (m * n)) :
    Fin m × Fin n :=
  ({ val := x.val % m, isLt := by
       by_cases hm : 0 < m
       · arith
       · arith },
   { val := x.val / m, isLt := by
       by_cases hn : 0 < n
       · arith
       · arith })

theorem finProduct_bijective (m n : Nat) :
    Bijective (finProduct m n) := by
  constructor
  · intro x y hxy
    -- 같은 나머지와 몫에서 원래 번호의 같음을 얻는다.
    indisc : 2 at hxy
    arith

  · intro y
    by_cases hpos : 0 < m ∧ 0 < n
    -- 번호 쌍 (i, j)에 i + jm을 대응시킨다.
    · exists ({ val := y.1.val + y.2.val * m,
                isLt := by arith } : Fin (m * n))

      ext : 2
      · expand
        arith

      · expand
        arith

    · arith
```

단사성에서는 두 순서쌍이 같다는 가정에서 나머지와 몫의 등식을 얻는다.
몫과 나머지가 모두 같으면 원래 번호도 같으므로 `arith`로 마친다.
전사성에서는 $`(i,j)`에 대응하는 번호 $`i+jm`을 제시한 뒤
`ext`로 나머지와 몫을 각각 비교한다.
한쪽 범위가 $`0`이면 주어진 순서쌍의 해당 성분이 존재할 수 없으므로 마지막 경우에는 모순을 얻는다.

이 전단사와 {ref "functions-product-maps"}[집합의 곱과 함수]의
`productMap_bijective`를 합성하면 임의의 두 유한집합의 곱을 셀 수 있다.
이 연결은 다음 연습문제에서 증명한다.

# 연습문제
%%%
tag := "cardinality-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 2* 원소가 하나씩 있는 두 집합은 크기가 같음을 증명하라.

```savedLean -keep
theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry
```


*문제 3* 크기가 같은 두 집합 $`A`, $`B`에 대하여
$`A`의 원소 수가 $`n`이라는 명제와 $`B`의 원소 수가 $`n`이라는 명제가 동치임을 증명하라.

```savedLean -keep
theorem exercise_finite_cardinal_transport
    {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry
```


*문제 4* $`n+1`개의 번호를 $`n`개의 번호에 단사로 대응시킬 수 없음을 증명하라.

```savedLean -keep
theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
  sorry
```


*문제 5* 무한집합과 크기가 같은 집합도 무한집합임을 증명하라.

```savedLean -keep
theorem exercise_infinite_transport {A B : Type}
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  sorry
```

*문제 6* 유한집합 $`A`, $`B`의 원소 수가 각각 $`m`, $`n`이면
집합의 곱 $`A\times B`의 원소 수가 $`mn`임을 증명하라.
즉 $`|A\times B|=|A||B|`이다.
함수 절의 `productMap_bijective`를 사용하여 `Fin m × Fin n`에서 `A × B`로 가는 전단사를 구성하라.

```savedLean -keep
theorem exercise_cardinal_product {A B : Type} {m n : Nat}
    (hA : cardinal A = m)
    (hB : cardinal B = n) :
    cardinal (A × B) = m * n := by
  sorry
```

*힌트* `finProduct_bijective`와 `productMap_bijective`를 합성하라. 기수의 등식에서 전단사를 꺼낼 때는 함수의 방향을 확인하라.


*문제 7* (색과 번호의 조합)

(1) 두 성분을 바꾸는 함수를 사용하여 $`|A\times B|=|B\times A|`임을 증명하라.

(2) 두 가지 색 중 하나와 세 가지 번호 중 하나를 고르는 방법이 모두 여섯 가지임을 보이라.
색과 번호를 각각 `Fin 2`, `Fin 3`으로 나타낸다.

(3) 앞의 두 결과를 사용하여 번호와 색의 순서로 나열해도 조합의 수는 같음을 보이라.

```savedLean -keep
theorem exercise_cardinal_swap (A B : Type) :
    cardinal (A × B) = cardinal (B × A) := by
  sorry

theorem exercise_two_by_three_cardinal :
    cardinal (Fin 2 × Fin 3) = 6 := by
  sorry

theorem exercise_three_by_two_cardinal :
    cardinal (Fin 3 × Fin 2) = 6 := by
  sorry
```

*문제 8* (같은 달에 태어난 두 사람)

(1) $`n+1`개의 번호를 $`n`개의 번호로 보내는 함수에서는
서로 다른 두 번호의 함수값이 같음을 증명하라.

(2) 열세 사람에게 태어난 달을 대응시키면 같은 달에 태어난 두 사람이 있음을 첫 결과로 보이라.
사람과 달을 각각 `Fin 13`, `Fin 12`로 나타낸다.

```savedLean -keep
theorem exercise_fin_collision (n : Nat)
    (f : Fin (n + 1) → Fin n) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  sorry

theorem exercise_birth_month_collision
    (month : Fin 13 → Fin 12) :
    ∃ i j, i ≠ j ∧ month i = month j := by
  sorry
```

*힌트* 첫 문제에서 같은 함수값을 갖는 서로 다른 두 번호가 없다고 가정하면 함수가 단사임을 보일 수 있다.

*문제 9* (서로 다른 원소 수)

(1) `Fin 2`와 `Fin 3` 사이에는 전단사가 존재하지 않음을 증명하라.

(2) 본문에서 센 집합 $`\{10,11,12\}`의 원소 수가 $`4`일 수 없음을 보이라.
원소 수의 유일성에 관한 정리들을 사용하라.

```savedLean -keep
theorem exercise_fin_two_three_not_same :
    ¬ SameCardinality (Fin 2) (Fin 3) := by
  sorry

theorem exercise_threeNumbers_not_four :
    cardinal (Elem threeNumbers) ≠ 4 := by
  sorry
```

# 크기 비교의 자동화
%%%
tag := "cardinality-automation"
file := "automation"
%%%

지금까지 전단사를 사용하여 크기를 비교하고 유한성과 무한성을 증명했다.
이제 이미 알고 있는 크기 관계로 다른 집합의 원소 수나 유한성을 얻는 과정을 정리하자.

{anchor "cardinality-finiteness-transport"}[]*정리* 원소 수가 주어진 집합은 유한하며
크기가 같은 두 집합은 함께 유한하거나 함께 무한하다.

```savedLean
theorem isFinite_of_cardinal_eq {A : Type} {n : Nat}
    (h : cardinal A = n) :
    IsFinite A := by
  exists n

theorem isFinite_transport {A B : Type}
    (hAB : cardinal A = cardinal B)
    (hA : IsFinite A) :
    IsFinite B := by
  unpack hA with ⟨n, hn⟩
  exists n
  rw [← hAB]
  exact hn

theorem isInfinite_transport {A B : Type}
    (hAB : cardinal A = cardinal B)
    (hA : IsInfinite A) :
    IsInfinite B := by
  intro hB
  apply hA
  exact isFinite_transport hAB.symm hB
```

유한성에서는 $`A`의 원소 수 $`n`을 정하고
기수의 등식 `hAB`로 $`B`의 원소 수도 $`n`임을 얻는다.
무한성에서는 $`B`가 유한하다고 가정하여 반대 방향으로 유한성을 옮긴다.
그러면 $`A`도 유한하여 주어진 무한성과 모순이다.

```savedLean -show
attribute [ample_card_rules]
  sameCardinality_refl sameCardinality_symm sameCardinality_trans
  cardinal_eq_of_sameCardinality sameCardinality_of_cardinal_eq
  Cardinal.eq_symm Cardinal.eq_trans
  cardinal_fin fin_isFinite empty_cardinal singleton_cardinal
  threeNumbers_cardinal finite_cardinal_unique
  fin_sameCardinality_eq cardinal_fin_eq cardinality_spec cardinality_eq
  isFinite_of_cardinal_eq isFinite_transport isInfinite_transport
  nat_isInfinite
```

{anchor "cardinality-card-tactic"}[]`card`는 현재 가정과 앞에서 증명한 크기 관련 정리를 연결하는 전술이다.
같은 크기의 반사성·대칭성·추이성, 원소 수의 유일성과
크기가 같은 집합 사이에서 유한성·무한성을 옮기는 정리를 사용한다.
기수의 등식과 `SameCardinality` 사이의 전환도 처리한다.
앞에서 증명한 `Fin n`, 공집합, 한 원소 집합과 `threeNumbers`의 기수 등식도 사용한다.

*보기* $`A`와 $`B`의 크기가 같고 $`A`의 원소 수가 $`n`이면
$`B`의 원소 수도 $`n`이다.

```savedLean
example {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B)
    (hA : cardinal A = n) :
    cardinal B = n := by
  card
```

*보기* 전단사가 존재한다는 가정은 기수의 등식으로 바꿀 수 있다.

```savedLean
example {A B : Type}
    (hAB : SameCardinality A B) :
    cardinal A = cardinal B := by
  card
```

*보기* 크기가 같은 두 집합 중 하나가 무한하면 다른 하나도 무한하다.

```savedLean
example {A B : Type}
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  card
```

*보기* 유한집합 `A`의 원소 수가 `n`이면 `cardinality A hA = n`이다.

```savedLean
example {A : Type} {n : Nat}
    (hA : IsFinite A)
    (hn : cardinal A = n) :
    cardinality A hA = n := by
  card
```

위의 증명들은 각각 기수 등식의 연결, `cardinal_eq_iff`,
`isInfinite_transport`, `cardinality_eq`를 사용한 추론을 자동으로 수행한다.

`card`의 탐색 범위는 이처럼 등록한 기본 정리로 한정된다.
새로운 전단사가 필요한 문제에서는 함수와 그 성질을 직접 제시하고,
이미 확인한 원소 수를 사용하거나 두 원소 수가 같음을 보일 때는 다음과 같이 `card`를 사용할 수 있다.

```savedLean
example
    (n : Nat) :
    cardinal (Fin n) = n := by
  card
```

*보기* 같은 집합의 원소 수로 얻은 두 자연수는 같다.

```savedLean
example {A : Type} {m n : Nat}
    (hm : cardinal A = m)
    (hn : cardinal A = n) :
    m = n := by
  card
```

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
