import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.FiniteCardinality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "무한집합의 크기" =>

%%%
tag := "infinite-cardinality"
file := "infinite-cardinality"
%%%

유한집합에서는 원소 수로 크고 작음을 비교했다.
무한집합까지 포함하여 크기를 비교하려면 한 집합의 원소를
다른 집합 안에 겹치지 않게 대응시키는 단사함수를 사용한다.
자연수와 같은 크기의 집합을 살펴본 뒤 멱집합과 대각선 논법으로 더 큰 무한집합을 구성하자.

```savedImport
import AlgebraBook.FiniteCardinality
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

# 기수의 대소 관계
%%%
tag := "cardinality-comparison"
file := "comparison"
%%%

*정의* $`A`에서 $`B`로 가는 단사함수가 존재하면 $`|A|\leq|B|`로 쓴다.
이 관계가 성립하고 두 기수가 같지 않으면 $`|A|<|B|`로 쓴다.

먼저 두 타입 사이에 단사가 존재한다는 조건을 술어로 정의하자.

```savedLean
def CardinalityLE : Type → Type → Prop :=
  fun A B => ∃ f : A → B, Injective f
```

```savedLean -show
def CardinalityLT : Type → Type → Prop :=
  fun A B => CardinalityLE A B ∧ ¬ SameCardinality A B
```

기수는 같은 크기의 타입들을 묶은 동치류이므로 기수의 부등식도 대표원으로 택한 타입에 의존하지 않아야 한다.
$`A`와 $`A'`, $`B`와 $`B'`의 크기가 각각 같고 단사함수 $`f:A\to B`가 있다고 하자.
전단사 $`a:A\to A'`의 역함수와 전단사 $`b:B\to B'`를 사용하면
$`b\circ f\circ a^{-1}:A'\to B'`도 단사이다.

```savedLean
theorem cardinalityLE_transport {A B : Type} {A' B' : Type}
    (hA : SameCardinality A A')
    (hB : SameCardinality B B')
    (h : CardinalityLE A B) :
    CardinalityLE A' B' := by
  unpack hA with ⟨a, ha⟩
  unpack hB with ⟨b, hb⟩
  unpack h with ⟨f, hf⟩

  -- 먼저 A'에서 A를 거쳐 B로 가는 단사를 얻는다.
  have hFirst : Injective (f ∘ inverseMap a ha) := by
    apply injective_compose
    · exact (inverseMap_bijective a ha).inj
    · exact hf

  -- B에서 B'로 가는 전단사를 이어 붙인다.
  exists b ∘ f ∘ inverseMap a ha
  exact injective_compose _ _ hFirst hb.inj
```

역방향은 두 전단사의 방향을 바꾸어 같은 정리를 사용하면 된다.
따라서 단사의 존재 여부는 대표원을 바꾸어도 달라지지 않는다.

이제 기수 `a`, `b`의 동치류에서 대표원 `A`, `B`를 택하여
`A`에서 `B`로 가는 단사가 존재한다는 조건으로 `a ≤ b`를 정의하자.
`A ∈ a.val`과 `B ∈ b.val`은 각각 그 타입이 해당 동치류에 속한다는 조건이다.

```savedLean -show
namespace Cardinal
```

```savedLean
def le : Cardinal → Cardinal → Prop :=
  fun a b => ∃ A B : Type,
    A ∈ a.val ∧ B ∈ b.val ∧ CardinalityLE A B
```

이 정의의 전체 이름은 `Cardinal.le`이며 기호 `≤`에 연결한다.
`a < b`는 `a ≤ b`이면서 두 기수가 다르다는 뜻이다.

```savedLean -show
instance : LE Cardinal := ⟨le⟩
instance : LT Cardinal := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

end Cardinal
```

Lean에서도 두 기수에 `≤`, `<`를 사용하며
`cardinal A ≤ cardinal B`는 `A`에서 `B`로 가는 단사의 존재와 다음과 같이 연결된다.

```savedLean
theorem cardinal_le_iff (A B : Type) :
    cardinal A ≤ cardinal B ↔ ∃ f : A → B, Injective f := by
  constructor
  · intro h
    rcases h with ⟨A', B', hA, hB, hf⟩
    exact cardinalityLE_transport hA hB hf

  · intro hf
    exists A, B
    and_intros
    · exact sameCardinality_refl A
    · exact sameCardinality_refl B
    · exact hf

theorem cardinal_lt_iff (a b : Cardinal) :
    a < b ↔ a ≤ b ∧ a ≠ b := by
  rfl
```

첫 번째 방향에서는 `≤`의 정의에 따라 대표원 `A'`, `B'`와 세 조건을 꺼낸다.
`hA : A' ∈ (cardinal A).val`은 `SameCardinality A' A`의 증명이며 `hB`도 같은 역할을 한다.
따라서 앞의 정리로 단사를 원래 타입 `A`, `B` 사이로 옮길 수 있다.
반대 방향에서는 `A`, `B` 자체를 대표원으로 택하므로 각 동치류에 속한다는 조건은 반사성으로 증명한다.

가령 `cardinal A ≤ cardinal B`를 보이려면
`apply (cardinal_le_iff A B).mpr`로 단사가 존재한다는 목표를 얻고 함수를 제시하면 된다.
기수의 등식에서 전단사를 사용했던 것과 같이 부등식에서는 단사함수를 사용한다.

*정리* 모든 기수는 자기 자신보다 작거나 같으며
$`|A|\leq|B|`, $`|B|\leq|C|`이면 $`|A|\leq|C|`이다.

*증명* 첫 명제에는 항등함수를 사용하고 둘째 명제에는 두 단사함수의 합성을 사용한다.
가정의 부등식에 `cardinal_le_iff`의 `.mp`를 적용하면 단사의 존재를 얻으므로
함수와 단사성의 증명을 `unpack`으로 꺼낼 수 있다.

```savedLean
theorem cardinal_le_refl (A : Type) :
    cardinal A ≤ cardinal A := by
  apply (cardinal_le_iff A A).mpr
  exists identity A
  exact identity_injective A

theorem cardinal_le_trans {A B C : Type}
    (hAB : cardinal A ≤ cardinal B)
    (hBC : cardinal B ≤ cardinal C) :
    cardinal A ≤ cardinal C := by
  unpack (cardinal_le_iff A B).mp hAB with ⟨f, hf⟩
  unpack (cardinal_le_iff B C).mp hBC with ⟨g, hg⟩

  -- 두 단사함수를 합성하여 크기의 비교를 연결한다.
  apply (cardinal_le_iff A C).mpr
  exists g ∘ f
  exact injective_compose f g hf hg
```

```savedLean -show
namespace Cardinal

theorem le_refl (a : Cardinal) : a ≤ a := by
  unpack (quotient_exists_classOf SameCardinality a) with ⟨A, hA⟩
  rw [hA]
  exact cardinal_le_refl A

theorem le_trans {a b c : Cardinal}
    (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c := by
  unpack (quotient_exists_classOf SameCardinality a) with ⟨A, hA⟩
  unpack (quotient_exists_classOf SameCardinality b) with ⟨B, hB⟩
  unpack (quotient_exists_classOf SameCardinality c) with ⟨C, hC⟩
  rw [hA, hB] at hAB
  rw [hB, hC] at hBC
  rw [hA, hC]
  exact cardinal_le_trans hAB hBC

theorem le_of_eq {a b : Cardinal} (h : a = b) : a ≤ b := by
  rw [← h]
  exact le_refl a

end Cardinal
```

단사함수에 의한 이 비교를 자연수와 같은 크기의 집합 및 멱집합에 적용하자.

# 자연수와 같은 크기의 집합
%%%
tag := "cardinality-countable-sets"
file := "countable-sets"
%%%

양의 자연수의 집합은 자연수 전체에서 $`0`을 뺀 집합이다.
자연수 $`n`을 양의 자연수 $`n+1`에 대응시키면
$`0,1,2,\ldots`와 $`1,2,3,\ldots`를 빠짐없이 짝지을 수 있다.
이 함수가 전단사임을 보여 두 집합의 크기를 비교하자.

```savedLean
def toPositive (n : Nat) : Elem positives :=
  { val := n + 1, property := by arith }
```

`val := n + 1`로 함수값을 정하고 `property`에서 그 수가 `positives`에 속함을 증명한다.
`arith`는 이 원소 조건을 `0 < n + 1`로 정리하여 부등식을 확인한다.
따라서 함수값은 양수라는 조건까지 갖춘 `Elem positives`의 원소이다.

$`x+1=y+1`이면 $`x=y`이므로 이 함수는 단사이다.
또한 양의 자연수 $`y`에 대하여 $`y-1`을 택하면
$`(y-1)+1=y`이므로 전사이다.

```savedLean
theorem toPositive_bijective : Bijective toPositive := by
  constructor
  · intro x y hxy
    -- 함수값이 같으면 x + 1 = y + 1이다.
    expand at hxy
    indisc at hxy
    arith

  · intro y
    -- 양의 자연수 y에 대응하는 번호는 y - 1이다.
    exists (y.val - 1)
    ext
    dsimp [toPositive]
    have hy :=
      y.property
    -- y > 0이므로 뺀 1을 다시 더하면 y를 얻는다.
    arith
```

단사성에서는 `expand at hxy`로 함수값을 펼치고
`indisc at hxy`로 $`x+1=y+1`을 얻는다.
이 등식에서 공통 항을 소거하면 $`x=y`이므로 `arith`로 증명을 마친다.
전사성에서는 `y.val - 1`을 택하고 `ext`와 `dsimp [toPositive]`로
목표를 `y.val - 1 + 1 = y.val`로 바꾼다.
`have hy := y.property`로 양수라는 조건을 가정에 넣으면
`arith`가 이를 `0 < y.val`로 정리하여 자연수의 뺄셈에서 $`(y-1)+1=y`임을 확인한다.

이 전단사에 따라 자연수 전체와 양의 자연수의 집합은 크기가 같다.
양의 자연수의 집합은 자연수 전체에서 $`0`을 뺀 것이므로
무한집합은 일부 원소를 제외한 부분집합과도 크기가 같을 수 있다.

*정의* 자연수 전체와 크기가 같은 집합을 *가산무한집합*이라고 한다.
자연수의 기수를 $`\aleph_0`로 나타내므로 가산무한집합 $`A`에 대하여 $`|A|=\aleph_0`로 쓴다.

기호 $`\aleph_0`는 `\aleph0`로 입력한다.

```savedLean
def IsCountablyInfinite : Type → Prop :=
  fun A => cardinal Nat = cardinal A
```

`IsCountablyInfinite A`는 $`\aleph_0=|A|`라는 기수의 등식이다.
이 등식에서 전단사 $`f : \mathbb{N}\to A`의 존재를 얻는다.
이 함수는 단사이기도 하므로 앞의 `infinite_of_nat_injection`에 따라 $`A`는 무한집합이다.
한편 양의 자연수의 집합이 가산무한이라는 사실은
자연수에서 오는 전단사 `toPositive`를 제시하여 증명한다.

```savedLean
theorem countablyInfinite_isInfinite {A : Type}
    (hA : IsCountablyInfinite A) :
    IsInfinite A := by
  unpack (cardinal_eq_iff Nat A).mp hA with ⟨f, hf⟩
  exact infinite_of_nat_injection f hf.inj

theorem positives_countablyInfinite :
    IsCountablyInfinite (Elem positives) := by
  ext
  exists toPositive
  exact toPositive_bijective
```

*보기* 짝수 집합도 가산무한집합이다.
{ref "functions-element-equality"}[함수 절]에서 자연수 $`n`을 짝수 $`2n`에 대응시키는
`doubleToEvens`가 전단사임을 증명했다.
이 전단사를 제시하여 자연수와 짝수 집합의 기수가 같음을 보이자.

```savedLean
theorem evens_countablyInfinite :
    IsCountablyInfinite (Elem evens) := by
  ext
  exists doubleToEvens
  exact doubleToEvens_bijective

example : IsInfinite (Elem evens) := by
  exact countablyInfinite_isInfinite evens_countablyInfinite
```

첫 정리는 자연수와 짝수 집합 사이의 전단사를 제시하고,
둘째 증명은 가산무한집합의 무한성을 앞의 일반 정리에서 얻는다.
양의 자연수의 집합과 짝수 집합도 모두 자연수와 크기가 같으므로 서로 크기가 같다.

```savedLean
example :
    cardinal (Elem evens) = cardinal (Elem positives) := by
  rw [← evens_countablyInfinite,
    ← positives_countablyInfinite]
```

두 정리를 등식으로 읽으면 각각 `cardinal Nat = cardinal (Elem evens)`와
`cardinal Nat = cardinal (Elem positives)`이다.
이들을 반대 방향으로 사용하여 양변을 `cardinal Nat`로 바꾸면 원하는 등식을 얻는다.

## 연습문제: 자연수의 꼬리
%%%
tag := "cardinality-countable-practice"
%%%

양의 자연수에 사용한 대응을 바꾸어 다음 집합의 크기를 확인해 보자.

*문제 1* $`\{n\in\mathbb{N}:2\leq n\}`이 가산무한집합임을 증명하라.

```savedLean -keep
theorem exercise_from_two_countably_infinite {n : Nat} :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
  sorry
```

## Advanced: 무한집합과 자연수의 단사
%%%
tag := "cardinality-infinite-converse"
%%%

앞에서는 자연수에서 $`A`로 가는 단사함수가 있으면 $`A`가 무한집합임을 보였다.
그 역을 보이기 위해 무한집합에서 서로 다른 원소를 하나씩 택하여 $`a_0,a_1,a_2,\ldots`로 놓으면
$`f(n)=a_n`이 원하는 단사함수가 된다.
이 절에서는 앞의 부분타입과 귀납법, {ref "functions-existence-and-values"}[원소의 선택과 역함수]에서 배운
`Classical.choose`와 `Classical.choose_spec`을 사용하여 이 단사함수를 구성한다.
각 단계에서 원소를 선택하므로 전체 구성은 Lean의 선택공리에 의존한다.

단사함수 $`s_n:\operatorname{Fin}(n)\to A`로 서로 다른 $`n`개의 원소를 골랐다고 하자.
이 함수가 전사라면 $`A`가 유한집합이 되므로
$`A`가 무한집합이라는 가정에 따라 $`s_n`의 상에 없는 원소가 존재한다.
이 원소를 번호 $`n`에 대응시키고 기존 번호의 함수값은 그대로 두면
단사함수 $`s_{n+1}:\operatorname{Fin}(n+1)\to A`를 얻는다.

이를 Lean으로 구성하려면 각 단계의 함수와 단사성의 증명을 함께 다루어야 한다.
함수 타입 `Fin n → A`에서 단사인 함수만 모은 부분타입을 다음과 같이 정의하자.

```savedLean
def FiniteListing (A : Type) (n : Nat) :=
  {f : Fin n → A // Injective f}

```

```savedLean -show
attribute [implicit_reducible] FiniteListing
```

```savedLean

def emptyListing (A : Type) : FiniteListing A 0 :=
  { val := fun i : Fin 0 => Fin.elim0 i
    property := by
      intro i j hij
      exact Fin.elim0 i }
```

`s : FiniteListing A n`에서 `s.val`은 함수이고 `s.property`는 그 단사성의 증명이다.
첫 단계인 `emptyListing A`는 정의역에 원소가 없는 함수를 사용한다.
따라서 단사성을 확인할 때도 `Fin 0`의 원소가 있다는 가정에서 모순을 얻는다.

기존 함수 `f : Fin n → A`에 새 함수값 `a : A`를 덧붙이는 과정은
번호가 `n`보다 작은지에 따라 나눌 수 있다.
아래의 `if hi : i.val < n then ... else ...`는 조건의 증명에 `hi`라는 이름을 붙인다.
조건이 참이면 `hi`를 범위 조건의 증명으로 사용하여 자연수 값이 `i.val`인 `Fin n`의 원소를 만들고 `f`에 넣는다.

```savedLean
def appendValue {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1)) :
    A :=
  if hi : i.val < n then
    f { val := i.val, isLt := hi }
  else a
```

`then` 쪽의 `{ val := i.val, isLt := hi }`는 자연수 `i.val`과 범위 조건의 증명 `hi`를 묶어
`Fin n`의 원소를 만든다. 따라서 이 식에서는 조건이 참이라는 사실을 함수값을 만드는 데에도 사용한다.
이처럼 `if`의 각 분기에서 조건의 증명을 사용할 수 있다.
Lean은 이 형태를 `dite`로 나타내며, 조건에 따라 값을 정리할 때는 `dite_eq_left`와 `dite_eq_right`를 사용한다.

`hi : i.val < n`을 `dite_eq_left`에 넣으면
원래 `if` 식이 `then` 쪽에서 그 증명을 사용한 값과 같다는 등식의 증명을 얻는다.
조건이 성립하지 않는다는 증명 `hi : ¬ i.val < n`을 `dite_eq_right`에 넣으면
`else` 쪽의 값과 같다는 등식의 증명을 얻는다.
`appendValue`에서 이 두 경우를 각각 쓰면 다음과 같다.

```savedLean
example {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1))
    (hi : i.val < n) :
    appendValue f a i = f { val := i.val, isLt := hi } := by
  rw [appendValue, dite_eq_left hi]

example {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1))
    (hi : ¬ i.val < n) :
    appendValue f a i = a := by
  rw [appendValue, dite_eq_right hi]
```

두 증명 모두 `rw [appendValue]`로 정의를 펼친 뒤
조건에 맞는 등식으로 `if` 식을 바꾼다.
첫 예제의 오른쪽에서는 주어진 `hi`로 원소의 범위 조건을 증명한다.

조건이 거짓이면 `i.val < n + 1`과 함께 `i.val = n`을 얻으므로
새 번호 $`n`에서의 함수값은 `a`이다.
기존 번호에서의 함수값은 다음과 같이 확인할 수 있다.
`i.castSucc`로 기존 번호를 그대로 새 목록의 범위에 옮긴다.

```savedLean
theorem appendValue_old {A : Type} {n : Nat}
    (f : Fin n → A) (a : A)
    (i : Fin n) :
    appendValue f a i.castSucc = f i := by
  have hi : i.castSucc.val < n :=
    i.isLt
  rw [appendValue]
  rw [dite_eq_left hi]
  rfl
```

`i.castSucc`의 자연수 값은 `i.val`과 같으므로 `i.isLt`로 조건의 증명 `hi`를 얻는다.
정의를 펼치고 `dite_eq_left hi`로 `then` 쪽의 값을 택하면
`f`에 넣는 원소는 값이 `i.val`인 `Fin n`의 원소이다.
이는 원래의 `i`와 같으므로 마지막 등식은 `rfl`로 증명한다.

이제 각 단계에서 다음 단계로 넘어가는 함수 `step`이 주어졌다고 하자.
`step`을 반복하여 모든 자연수 단계의 함수를 만드는 방법은 다음과 같다.

```savedLean
def buildListings {A : Type}
    (step : (n : Nat) → FiniteListing A n →
      FiniteListing A (n + 1)) :
    (n : Nat) → FiniteListing A n
  | 0 => emptyListing A
  | n + 1 => step n (buildListings step n)
```

이와 같이 앞에서 정한 값으로 다음 값을 정하는 방법을 *재귀적 정의*라고 한다.
`| 0 => ...`에는 첫 값을 적고 `| n + 1 => ...`에는 앞 단계 `n`의 값으로 다음 값을 만드는 식을 적는다.
따라서 `buildListings step 0`은 `emptyListing A`이고
`buildListings step (n + 1)`은 `step n (buildListings step n)`이다.
함수의 타입 `(n : Nat) → FiniteListing A n`에서 결과는 `n`에 따라 달라지는 타입에 속한다.
가령 `n = 2`에서는 `Fin 2 → A`인 단사함수를, `n = 3`에서는 `Fin 3 → A`인 단사함수를 얻는다.

### 보조정리의 연습문제
%%%
tag := "cardinality-infinite-lemmas"
%%%

단사함수의 구성에 필요한 두 보조정리를 증명하라.

*보충 문제 1* 무한집합 $`A`로 가는 단사함수 $`f:\operatorname{Fin}(n)\to A`가 주어졌다고 하자.
$`f`의 상에 속하지 않는 원소가 $`A`에 존재함을 증명하라.

```savedLean -keep
theorem fresh_element_exists {A : Type} {n : Nat}
    (hA : IsInfinite A)
    (f : Fin n → A)
    (hf : Injective f) :
    ∃ a : A, ∀ i : Fin n, f i ≠ a := by
  sorry
```

*힌트* 결론을 부정하면 `f`가 전사임을 보일 수 있다.
단사이기도 한 `f`는 전단사이므로 `A`가 유한하다는 결론을 얻는다.

*보충 문제 2* 무한집합 $`A`의 유한한 목록에 새 원소를 하나 덧붙여
기존 번호의 함수값을 보존하는 목록을 만들 수 있음을 증명하라.

```savedLean -keep
theorem finite_listing_extension {A : Type} {n : Nat}
    (hA : IsInfinite A)
    (s : FiniteListing A n) :
    ∃ t : FiniteListing A (n + 1),
      ∀ i : Fin n, t.val i.castSucc = s.val i := by
  sorry
```

*힌트* 문제 1에서 얻은 원소 `a`를 `appendValue s.val a`에 사용하라.
단사성을 확인할 때 두 번호가 각각 `n`보다 작은지에 따라 나누면
기존 함수의 단사성이나 새 원소의 선택 조건을 사용할 수 있다.

### 자연수에서 오는 단사함수
%%%
tag := "cardinality-infinite-construction"
%%%

이제 두 보조정리를 사용하여 자연수에서 $`A`로 가는 단사함수를 구성하자.
아래 코드에서는 두 번째 보조정리의 증명을 `extend`라는 인수로 받는다.
`extend hA s`는 무한성의 증명 `hA`와 목록 `s`를 받아,
기존 함수값을 보존하면서 새 원소를 하나 덧붙인 목록이 존재한다는 증명을 준다.

`section InfiniteConstruction`과 `end InfiniteConstruction` 사이에서는
이 인수를 공통으로 사용하며 `include extend`로 이어지는 정리에도 이 인수를 포함한다.

```savedLean
section InfiniteConstruction

variable
  (extend : ∀ {A : Type} {n : Nat},
    IsInfinite A → (s : FiniteListing A n) →
      ∃ t : FiniteListing A (n + 1),
        ∀ i : Fin n, t.val i.castSucc = s.val i)

include extend
```

확장이 존재한다는 증명 `extend hA s`에서 `Classical.choose`로 확장된 목록을 택하고
`Classical.choose_spec`으로 기존 번호에서 함수값이 보존된다는 증명을 얻자.
이 둘을 부분타입에 함께 담으면 다음과 같다.

```savedLean
noncomputable def nextListingData {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) :
    {t : FiniteListing A (n + 1) //
      ∀ i : Fin n, t.val i.castSucc = s.val i} :=
  { val := Classical.choose (extend hA s)
    property := Classical.choose_spec (extend hA s) }

noncomputable def nextListing {A : Type} (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) :
    FiniteListing A (n + 1) :=
  (nextListingData extend hA n s).val
theorem nextListing_spec {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) (i : Fin n) :
    (nextListing extend hA n s).val i.castSucc =
      s.val i := by
  exact (nextListingData extend hA n s).property i
```

`nextListing`은 `.val`에서 확장된 목록을 꺼내고,
`nextListing_spec`은 `.property`에서 기존 함수값이 보존된다는 증명을 꺼낸다.
원소의 선택은 `nextListingData`에서 이루어지므로 두 결과는 같은 확장에 관한 것이다.

`buildListings`에 `nextListing extend hA`를 넣으면
빈 목록에서 시작하여 원소가 하나씩 늘어나는 목록을 얻는다.
각 단계의 함수를 $`s_n:\operatorname{Fin}(n)\to A`라고 하자.
번호 $`n`은 원소가 $`n+1`개인 목록에 처음 들어가므로
그때의 함수값 $`s_{n+1}(n)`을 $`f(n)`으로 정한다.

```savedLean
noncomputable def infiniteListings {A : Type}
    (hA : IsInfinite A)
    (n : Nat) : FiniteListing A n :=
  buildListings (nextListing extend hA) n
noncomputable def natIntoInfinite {A : Type}
    (hA : IsInfinite A)
    (n : Nat) : A :=
  (infiniteListings extend hA (n + 1)).val
    { val := n, isLt := by arith }
```

`infiniteListings extend hA n`에는 함수 $`s_n`과 그 단사성의 증명이 함께 들어 있다.
`natIntoInfinite extend hA`가 방금 정한 함수 $`f:\mathbb{N}\to A`이다.

*보조정리* $`i<n`이면 $`s_n(i)=f(i)`이다.

*증명* $`n`에 대한 귀납법을 사용한다.
$`n=0`이면 확인할 번호가 없으며
원소가 $`n+1`개인 목록의 번호는 기존 번호 $`i<n`과 새 번호 $`i=n`으로 나뉜다.
기존 번호에서는 확장이 함수값을 보존하므로
$`s_{n+1}(i)=s_n(i)=f(i)`를 얻는다.
새 번호에서는 $`f(n)`을 바로 $`s_{n+1}(n)`으로 정의했으므로 등식이 성립한다.

여기서는 번호 `i`의 타입이 `Fin n`이므로 `n`에 따라 함께 달라진다.
`induction n`은 이처럼 타입이 `n`에 의존하는 인수도 귀납 단계에 맞추어 다룬다.
따라서 `succ n ih`의 귀납 가정 `ih`는 모든 `j : Fin n`에 대한 등식을 주며,
기존 번호를 `j : Fin n`으로 옮기면 `ih j`를 사용할 수 있다.

```savedLean
theorem infiniteListings_value {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (i : Fin n) :
    (infiniteListings extend hA n).val i =
      natIntoInfinite extend hA i.val := by
  -- 목록의 크기에 대한 귀납법으로 함수값을 비교한다.
  induction n with
  | zero =>
      exact Fin.elim0 i

  | succ n ih =>
      by_cases hi : i.val < n
      · let j : Fin n := { val := i.val, isLt := hi }

        -- 기존 번호를 앞 단계의 Fin n으로 옮긴다.
        have hij : i = j.castSucc := by
          ext

        rw [hij]
        rw [infiniteListings, buildListings]

        -- 확장은 기존 함수값을 보존하므로 귀납 가정을 쓴다.
        rw [nextListing_spec]
        exact ih j

      · have hin : i.val = n := by
          have hiBound : i.val < n + 1 :=
            i.isLt
          arith

        -- 새 번호 n으로 바꾸어 f(n)의 정의를 사용한다.
        let last : Fin (n + 1) :=
          { val := n, isLt := by arith }
        have hiLast : i = last := by
          ext
          exact hin

        rw [hiLast]
        rfl
```

첫 경우에는 `i`와 자연수 값이 같은 `j : Fin n`을 만든 뒤
`nextListing_spec`으로 앞 단계의 함수값을 얻고 귀납 가정 `ih j`를 사용한다.
둘째 경우에는 `i.val = n`이므로 `i`가 마지막 번호 `last`와 같음을 보인다.
이를 대입하면 `natIntoInfinite`의 정의에 따라 양변이 같아진다.

*정리* 무한집합 $`A`에 대하여 자연수에서 $`A`로 가는 단사함수가 존재한다.

*증명* 위에서 구성한 $`f`가 단사임을 보이자.
$`f(i)=f(j)`라고 가정하고 두 번호보다 큰 $`N=i+j+1`을 택한다.
앞의 보조정리에 따라 $`s_N(i)=f(i)=f(j)=s_N(j)`이며
$`s_N`이 단사이므로 $`i=j`이다.

```savedLean
theorem natIntoInfinite_injective {A : Type}
    (hA : IsInfinite A) :
    Injective (natIntoInfinite extend hA) := by
  intro i j hij
  -- 두 번호가 모두 들어 있는 유한한 목록을 택한다.
  let N := i + j + 1
  let p : Fin N := { val := i, isLt := by arith }
  let q : Fin N := { val := j, isLt := by arith }

  -- f(i) = f(j)를 그 목록 안의 함수값 등식으로 옮긴다.
  have hpq : (infiniteListings extend hA N).val p =
      (infiniteListings extend hA N).val q := by
    rw [infiniteListings_value extend hA N p,
      infiniteListings_value extend hA N q]
    exact hij

  -- 목록의 단사성으로 p = q를 얻고 번호 값을 비교한다.
  have hIndex : p = q :=
    (infiniteListings extend hA N).property p q hpq
  have hVal : p.val = q.val := by
    rw [hIndex]

  exact hVal

theorem infinite_has_nat_injection {A : Type}
    (hA : IsInfinite A) :
    ∃ f : Nat → A, Injective f := by
  exists natIntoInfinite extend hA
  exact natIntoInfinite_injective extend hA
```

`p`와 `q`는 자연수 값이 각각 `i`, `j`인 `Fin N`의 원소이다.
`infiniteListings_value`로 가정 `hij`를 목록 안의 등식 `hpq`로 옮기면
그 목록의 단사성에서 `p = q`를 얻는다.
이 등식의 자연수 값을 비교하면 원하는 결론 `i = j`이다.

{anchor "cardinality-least-infinite"}[]집합의 크기에 대한 부등식 $`|A|\leq|B|`는
$`A`에서 $`B`로 가는 단사함수가 존재한다는 뜻이다.
자연수 집합은 무한집합이며 방금 증명한 정리에 따라
모든 무한집합 $`A`에 대하여 $`|\mathbb{N}|\leq|A|`이다.
크기를 단사함수로 비교한다는 의미에서 자연수 집합은 가장 작은 무한집합이며
그 기수 $`\aleph_0`는 가장 작은 무한기수이다.

```savedLean
theorem nat_least_infinite :
    IsInfinite Nat ∧ ∀ (A : Type), IsInfinite A →
      cardinal Nat ≤ cardinal A := by
  constructor
  · exact nat_isInfinite
  · intro A hA
    apply (cardinal_le_iff Nat A).mpr
    exact infinite_has_nat_injection extend hA

end InfiniteConstruction
```

여기까지의 구성에는 목록을 한 칸 늘릴 수 있다는 증명 `extend`가 인수로 남아 있다.
앞의 연습문제 `finite_listing_extension`을 완성하면
`infinite_has_nat_injection finite_listing_extension hA`로 원하는 단사함수의 존재를 얻고,
`nat_least_infinite finite_listing_extension`으로 자연수의 최소성까지 얻는다.
따라서 이 절의 완전한 증명에는 두 보조정리의 풀이도 포함된다.

# 멱집합과 칸토어 정리
%%%
tag := "cardinality-power-sets"
file := "power-sets"
%%%

자연수와 양의 자연수처럼 무한집합은 자신의 진부분집합과도 크기가 같을 수 있다.
그렇다면 모든 무한집합의 크기가 같을까?
이 절에서는 부분집합들을 원소로 모은 멱집합을 정의하고
원래 집합보다 크기가 커진다는 칸토어 정리를 증명한다.

{anchor "cardinality-power-set-definition"}[]*정의* 집합 $`S`의 모든 부분집합으로 이루어진 집합을 $`S`의 *멱집합*이라고 하고 $`\mathcal{P}(S)`로 쓴다.
즉 $`T\in\mathcal{P}(S)`이라는 것은 $`T\subseteq S`라는 뜻이다.

```savedLean
def powerSet {A : Type} (S : Set A) : Set (Set A) :=
  fun T => T ⊆ S
```

`S`의 원소는 `A`의 원소이고 멱집합의 원소는 `A` 위의 집합이므로
`powerSet S`의 타입은 `Set (Set A)`이다.
예를 들어 $`S=\{a,b\}`이고 $`a\ne b`이면
$`\mathcal{P}(S)=\{\varnothing,\{a\},\{b\},\{a,b\}\}`이다.
공집합도 부분집합이므로 멱집합의 원소에 포함된다.

*보기* 모든 집합 $`S`에 대하여 $`\varnothing\in\mathcal{P}(S)`이고 $`S\in\mathcal{P}(S)`이다.

```savedLean
example {A : Type}
    (S : Set A) :
    (∅ : Set A) ∈ powerSet S := by
  exact empty_subset S

example {A : Type}
    (S : Set A) :
    S ∈ powerSet S := by
  exact subset_refl S
```

첫 목표는 공집합이 `S`의 부분집합이라는 명제이고
둘째 목표는 `S`가 자신의 부분집합이라는 명제이다.
따라서 집합 절에서 증명한 `empty_subset`과 `subset_refl`을 그대로 사용할 수 있다.

원소 타입 `A` 전체의 멱집합을 다룰 때는 `Set A`를 사용한다.
모든 `T : Set A`가 `whole A`의 부분집합이므로
`Set A`의 원소들이 바로 전체집합의 부분집합들이다.

```savedLean
example {A : Type}
    (T : Set A) :
    T ∈ powerSet (whole A) := by
  exact subset_whole T
```

{anchor "cardinality-singleton-injection"}[]멱집합과 원래 집합의 크기를 비교하려면 먼저 단사함수를 하나 찾으면 된다.
각 원소를 그 원소만으로 이루어진 부분집합에 대응시키자.

*보기* 원소 $`a`를 한 원소 집합 $`\{a\}`에 대응시키면
$`A`에서 그 멱집합으로 가는 단사함수를 얻는다.
$`\{a\}=\{b\}`이면 $`a\in\{b\}`이므로 $`a=b`이다.

```savedLean
theorem singleton_injective {A : Type} :
    Injective (singleton : A → Set A) := by
  intro a b hab
  have ha : a ∈ singleton a := by rfl
  rw [hab] at ha
  exact ha

theorem cardinal_le_powerSet (A : Type) :
    cardinal A ≤ cardinal (Set A) := by
  apply (cardinal_le_iff A (Set A)).mpr
  exists singleton
  exact singleton_injective
```

`singleton`의 단사성을 보일 때는 원소 `a`가 자신의 한 원소 집합에 속한다는 사실을 사용한다.
`rw [hab] at ha`로 그 집합을 `singleton b`로 바꾸면 `ha`는 `a = b`의 증명이 된다.
이 단사함수를 제시하면 멱집합과의 기수 부등식을 얻는다.

```savedLean -show
theorem cardinality_le_powerSet (A : Type) :
    CardinalityLE A (Set A) := by
  exact (cardinal_le_iff A (Set A)).mp (cardinal_le_powerSet A)
```

이로써 $`|A|\leq|\mathcal{P}(A)|`를 얻었다.
이제 $`|A|<|\mathcal{P}(A)|`를 보이려면 두 기수가 다름을 증명하면 된다.
이를 위해 $`A`에서 멱집합으로 가는 전사함수가 없음을 보이자.

## 칸토어 정리
%%%
tag := "cardinality-cantor"
%%%

*정리* 어떤 집합 $`A`에 대하여도
$`A`에서 $`\mathcal{P}(A)`로 가는 전사함수는 존재하지 않는다.
따라서 $`|A|<|\mathcal{P}(A)|`이다.

*증명* 함수 $`f:A\to\mathcal{P}(A)`가 주어졌다고 하자.
이 함수가 전사가 아님을 보이려면 모든 함수값 $`f(x)`와 다른 집합 $`D`를 찾으면 된다.
각 $`x`에서 원소 $`x`가 속하는지를 서로 반대로 정하면 $`D`와 $`f(x)`는 그 원소에서 달라진다.
이에 따라 다음 집합을 정의하자.

$$`D=\{x\in A:x\notin f(x)\}.`

$`f`가 전사라면 $`f(a)=D`인 원소 $`a`가 존재한다.
이 원소가 $`D`에 속하는지 살펴보자.

먼저 $`a\in D`라고 가정하면 정의에 따라 $`a\notin f(a)`이다.
여기에 $`f(a)=D`를 대입하면 $`a\notin D`를 얻어 가정과 모순이므로 $`a\notin D`이다.

그러면 $`f(a)=D`에 따라 $`a\notin f(a)`이며,
이는 $`D`의 원소 조건이므로 $`a\in D`를 얻는다.
다시 모순이 생겼으므로 $`f`는 전사일 수 없으며 전단사도 존재하지 않는다.

이 증명은 각 $`x`에서 $`x\in f(x)`인지를 보고
그 조건을 뒤집어 $`D`를 만든다.
이를 원소 관계의 표로 생각할 수 있다.
행에는 원소 $`x`를, 열에는 각 원소에서의 함수값 $`f(x)`를 같은 순서로 놓으면
$`x\in f(x)`인지를 기록한 칸은 대각선 위에 놓인다.
그 칸의 조건을 모두 뒤집어 새 집합을 만드는 데서 *대각선 논법*이라는 이름이 나온다.

여기서 `f`의 공역은 집합들을 원소로 갖는 타입 `Set A`이다.
따라서 전사성의 가정 `hf`가 증명하는 전칭명제는 `∀ T : Set A, ∃ a, f a = T`이다.
이 증명에 집합 `D`를 넣은 `hf D`는 `∃ a, f a = D`의 증명이므로,
`unpack`으로 원소 `a`와 등식 `ha`를 꺼낼 수 있다.

```savedLean
theorem cantor_not_surjective {A : Type} (f : A → Set A) :
    ¬ Surjective f := by
  intro hf
  let D : Set A := fun x => x ∉ f x
  unpack hf D with ⟨a, ha⟩

  -- a ∈ D이면 원소 조건과 모순이다.
  have hnot : a ∉ D := by
    intro hmem
    apply hmem
    rw [ha]
    exact hmem

  -- a ∉ D에서 다시 a ∈ D를 얻는다.
  have hmem : a ∈ D := by
    expand
    rw [ha]
    exact hnot

  exact hnot hmem
```

첫 `have`에서 `hmem : a ∈ D`의 원소 조건은 `a ∉ f a`이다.
따라서 `apply hmem`을 쓰면 모순을 보이는 목표 `False`가 `a ∈ f a`로 바뀐다.
`ha : f a = D`를 대입하면 `a ∈ D`가 되어 원래 가정으로 증명할 수 있다.

둘째 `have`에서는 `expand`로 `D`의 원소 조건을 펼친 뒤 같은 등식을 대입한다.
이때 목표는 `a ∉ D`이므로 앞에서 얻은 `hnot`으로 마친다.
최종적으로 `hnot : a ∉ D`와 `hmem : a ∈ D`를 함께 사용하여 모순을 얻는다.

*보기* 자연수 $`n`에 집합 $`\{0,\ldots,n-1\}`을 대응시키자.
$`n=0`일 때는 공집합을 얻으며, 이후의 함수값은 $`\{0\}`, $`\{0,1\}`, $`\{0,1,2\}`, $`\ldots`이다.
이 대응에 대각선 논법을 적용하면 어떤 집합이 빠져 있음을 알 수 있을까?

```savedLean
def initialSegment (n : Nat) : Set Nat := fun k => k < n
def initialSegmentDiagonal : Set Nat :=
  fun n => n ∉ initialSegment n
```

자연수 $`n`은 $`n`보다 작은 수들의 집합에 속하지 않는다.
따라서 모든 자연수가 대각선 집합에 속하며 이 집합은 자연수 전체이다.

```savedLean
theorem initialSegment_diagonal :
    initialSegmentDiagonal = whole Nat := by
  ext n
  constructor
  · intro hn
    trivial

  · intro hn
    expand
    expand
    arith
```

역방향에서 두 정의를 차례로 펼치면 `¬ n < n`이 남는다.
이것이 모든 자연수에서 성립하므로 대각선 집합은 전체집합이다.
어느 `initialSegment n`도 $`n`을 포함하지 못하므로 전체집합과 같을 수 없다.
전사함수가 없다는 결론은 앞의 칸토어 정리에 이 함수를 넣어 얻을 수도 있다.

```savedLean
example : ¬ Surjective initialSegment := by
  exact cantor_not_surjective initialSegment
```

이 예제의 대각선 집합은 자연수 전체이다.
다른 함수에서 출발하면 다른 대각선 집합을 얻을 수 있지만, 어느 경우에도 그 집합은 해당 함수의 상에 속하지 않는다.

이제 전단사가 존재한다고 가정하면 그 전사성이 방금 증명한 정리와 모순이므로
멱집합과 원래 집합의 크기가 같을 수 없다.

```savedLean
theorem powerSet_not_sameCardinality (A : Type) :
    ¬ SameCardinality A (Set A) := by
  intro h
  unpack h with ⟨f, hf⟩
  exact cantor_not_surjective f hf.surj

```

```savedLean -show
theorem cardinality_lt_powerSet (A : Type) :
    CardinalityLT A (Set A) := by
  constructor
  · exact cardinality_le_powerSet A
  · exact powerSet_not_sameCardinality A

```

```savedLean
theorem cardinal_ne_powerSet (A : Type) :
    cardinal A ≠ cardinal (Set A) := by
  intro h
  apply powerSet_not_sameCardinality A
  exact (cardinal_eq_iff A (Set A)).mp h

theorem cardinal_lt_powerSet (A : Type) :
    cardinal A < cardinal (Set A) := by
  constructor
  · exact cardinal_le_powerSet A
  · exact cardinal_ne_powerSet A
```

*보기* 자연수의 멱집합은 무한집합이며 가산무한집합이 아니다.
한 원소 집합을 만드는 단사함수로 무한성을 얻으며
자연수와 크기가 같다고 가정하면 칸토어 정리와 모순이다.

```savedLean
theorem nat_powerSet_isInfinite :
    IsInfinite (Set Nat) := by
  exact infinite_of_nat_injection
    singleton singleton_injective

theorem nat_powerSet_not_countablyInfinite :
    ¬ IsCountablyInfinite (Set Nat) := by
  exact cardinal_ne_powerSet Nat
```

자연수에서 시작하여 멱집합을 거듭 만들면 다음과 같이 크기가 커진다.

$$`|\mathbb{N}|<|\mathcal{P}(\mathbb{N})|<|\mathcal{P}(\mathcal{P}(\mathbb{N}))|<\cdots.`

이처럼 무한집합 사이에서도 크기의 차이가 생긴다.

# 연습문제
%%%
tag := "infinite-cardinality-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 2* 다음 멱집합의 등식을 증명하라.

```savedLean -keep
theorem exercise_powerSet_inter {A : Type} (S T : Set A) :
    powerSet (S ∩ T) = powerSet S ∩ powerSet T := by
  sorry
```

*문제 3* (등차수열과 가산무한집합)

집합 $`S=\{1,4,7,10,\ldots\}`을 $`3k+1` 꼴의 자연수로 정의한다.

(1) 아래 함수가 자연수에서 $`S`의 원소 타입으로 가는 전단사임을 증명하라.

(2) 첫 결과로 $`S`가 가산무한집합임을 보이라.

(3) $`S`가 자연수 전체와 같은 집합은 아님을 보이라.
집합의 같음과 크기의 같음을 구별하라.

```savedLean -keep
def practiceOneModThree : Set Nat :=
  fun n => ∃ k, n = 3 * k + 1
def practiceToOneModThree (n : Nat) :
    Elem practiceOneModThree :=
  { val := 3 * n + 1
    property := by exists n }

theorem exercise_oneModThree_bijective :
    Bijective practiceToOneModThree := by
  sorry

theorem exercise_oneModThree_countable :
    IsCountablyInfinite (Elem practiceOneModThree) := by
  sorry

theorem exercise_oneModThree_ne_whole :
    practiceOneModThree ≠ whole Nat := by
  sorry
```

*문제 4* (순서쌍 집합의 무한성)

자연수의 순서쌍 전체가 무한집합임을 증명하라.
자연수에서 오는 단사함수를 하나 구성하여 `infinite_of_nat_injection`을 사용하라.
선택한 함수가 전사일 필요가 없는 이유도 설명하라.

```savedLean -keep
theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry
```

*문제 5* (멱집합의 포함 관계)

(1) $`S\subseteq T`이면 $`\mathcal{P}(S)\subseteq\mathcal{P}(T)`임을 증명하라.

(2) 반대 방향도 증명하여 이 두 포함 관계가 동치임을 보이라.

(3) 첫 결과와 `twoThree_subset_positives`를 사용하여
$`\mathcal{P}(\{2,3\})\subseteq\mathcal{P}(\mathbb{N}_{>0})`임을 보이라.

```savedLean -keep
theorem exercise_powerSet_mono {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    powerSet S ⊆ powerSet T := by
  sorry

theorem exercise_powerSet_subset_iff {A : Type}
    (S T : Set A) :
    powerSet S ⊆ powerSet T ↔ S ⊆ T := by
  sorry

theorem exercise_powerSet_twoThree_positives :
    powerSet twoThree ⊆ powerSet positives := by
  sorry
```

*문제 6* (한 원소 집합들을 나열한 경우)

$`f(n)=\{n\}`으로 부분집합들을 나열하자.

(1) 이 나열의 대각선 집합 $`D=\{n:n\notin f(n)\}`이 공집합임을 보이라.

(2) 공집합이 이 함수의 상에 속하지 않음을 직접 증명하라.

(3) 둘째 결과로 이 함수가 전사가 아님을 보이라.

```savedLean -keep
def practiceSingletonDiagonal : Set Nat :=
  fun n => n ∉ singleton n
theorem exercise_singleton_diagonal_empty :
    practiceSingletonDiagonal = ∅ := by
  sorry

theorem exercise_empty_not_singleton_image :
    (∅ : Set Nat) ∉ image singleton (whole Nat) := by
  sorry

theorem exercise_singleton_not_surjective :
    ¬ Surjective (singleton : Nat → Set Nat) := by
  sorry
```

# 크기 비교의 자동화
%%%
tag := "infinite-cardinality-automation"
file := "automation"
%%%

{ref "cardinality-card-tactic"}[집합의 크기와 유한성]에서 배운 `card`에
이 절에서 증명한 기수의 대소 관계, 가산무한성, 멱집합의 크기에 관한 정리를 추가한다.
새로운 단사나 전단사를 구성해야 하는 문제에서는 함수를 직접 제시하고,
이미 알고 있는 크기 관계를 연결할 때는 `card`를 사용할 수 있다.

```savedLean -show
attribute [ample_card_rules]
  Cardinal.le_refl Cardinal.le_trans Cardinal.le_of_eq
  countablyInfinite_isInfinite positives_countablyInfinite
  cardinal_le_powerSet cardinal_ne_powerSet cardinal_lt_powerSet
```

*보기* $`|A|\leq|B|`이고 $`|B|\leq|C|`이면 $`|A|\leq|C|`이다.
새로운 단사를 직접 합성하는 대신 이미 주어진 두 크기 관계를 `card`로 연결할 수 있다.

```savedLean
theorem infinite_card_comparison {A B C : Type}
    (hAB : cardinal A ≤ cardinal B)
    (hBC : cardinal B ≤ cardinal C) :
    cardinal A ≤ cardinal C := by
  card
```

```savedLean
end Ample
```

```savedLean -show
export_course_compat
```
