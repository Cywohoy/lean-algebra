import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.Numbers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "동치관계와 몫집합" =>

%%%
tag := "relations"
file := "relations"
%%%

같은 나머지를 갖는 정수들을 한 부류로 묶듯이, 주어진 관계를 만족하는 원소들을 묶어 새로운 집합을 만들 수 있다.
이 절에서는 합동의 세 성질을 바탕으로 동치관계를 정의하고 동치류와 몫집합을 구성한다.
이어서 동치류를 인수로 받는 함수를 정의할 때 대표원의 선택이 어떤 역할을 하는지 살펴본다.
이 구성은 다음 절에서 집합의 크기를 나타내는 데에도 사용한다.

```savedImport
import AlgebraBook.Numbers
```

```savedLean -show
open scoped Classical
```

```savedLean
namespace Course
variable {A B C : Type} {m n : Nat}
local infixr:90 (priority := high) " ∘ " => compose
```

```savedLean -show
local notation:50 a " ≡ " b " [ZMOD " n "]" => Congruent n a b
```

# 동치관계
%%%
tag := "preliminaries-equivalence-relations"
file := "equivalence-relations"
%%%

앞에서 법 `n`을 고정하여 정의한 `Congruent n : Int → Int → Prop`는
두 정수 `a`, `b`에 “$`a`와 $`b`가 $`n`을 법으로 합동이다”라는 명제를 대응시킨다.
이처럼 두 원소 사이의 조건을 나타내는 것을 *이항관계*라고 한다.
원소 하나에 관한 술어의 타입이 `A → Prop`이었던 것과 같이
두 원소에 관한 관계의 타입은 `A → A → Prop`이다.
수학에서 $`R(a,b)`나 $`a\mathrel{R}b`, $`a\sim b`로 쓰는 명제는 Lean에서 `R a b`로 쓴다.

```savedLean
def Relation (A : Type _) := A → A → Prop
```

등식도 합동에서 확인한 세 성질을 만족한다.
자기 자신과 같고, 등식의 양변을 바꾸어도 성립하며, 두 등식을 이어 쓸 수 있다.
이 세 성질을 공통으로 다루기 위해 다음 정의를 사용한다.

*정의* 관계 $`R`이 다음 세 성질을 만족하면 *동치관계*라고 한다.

1. 모든 원소 $`a`에 대하여 $`R(a,a)`이다. 이를 *반사성*이라고 한다.
2. $`R(a,b)`이면 $`R(b,a)`이다. 이를 *대칭성*이라고 한다.
3. $`R(a,b)`이고 $`R(b,c)`이면 $`R(a,c)`이다. 이를 *추이성*이라고 한다.

```savedLean
def IsEquivalence {A : Type _} : Relation A → Prop :=
  fun R =>
    (∀ a, R a a) ∧
    (∀ a b, R a b → R b a) ∧
    (∀ a b c, R a b → R b c → R a c)
```

```savedLean -show
namespace IsEquivalence

theorem refl
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) (a : A) :
    R a a := hR.left a

theorem symm
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) {a b : A}
    (hab : R a b) : R b a := hR.right.left a b hab

theorem trans
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) {a b c : A}
    (hab : R a b) (hbc : R b c) : R a c := hR.right.right a b c hab hbc

end IsEquivalence
```

세 성질을 논리곱으로 묶었으므로 `hR : IsEquivalence R`이 주어지면
반사성·대칭성·추이성의 증명을 각각 꺼낼 수 있다.
교재에서는 이 세 조건을 이름으로 사용하는 정리도 준비했다.
`hR.refl a`는 `R a a`의 증명이고,
`hR.symm hab`는 `hab : R a b`에서 `R b a`를 얻는다.
또한 `hR.trans hab hbc`는 `hab : R a b`와 `hbc : R b c`에서 `R a c`를 얻는다.

*보기* 임의의 정수 $`n`에 대하여 합동 관계 `Congruent n`은 동치관계이다.

*풀이* 앞에서 증명한 `congruent_refl n`, `congruent_symm n`, `congruent_trans n`이
각각 반사성·대칭성·추이성의 증명이다.
논리곱으로 묶인 여러 조건을 한 번에 나누는 전술 `and_intros`를 사용하자.
이렇게 얻은 세 목표는 각각 반사성·대칭성·추이성이므로 앞의 세 정리를 차례로 사용하면 된다.

```savedLean
theorem congruent_equivalence (n : Int) :
    IsEquivalence (Congruent n) := by
  and_intros
  · exact congruent_refl n
  · exact congruent_symm n
  · exact congruent_trans n
```

`and_intros`는 바깥의 논리곱을 나누고 남은 목표가 다시 논리곱이면 그 목표도 나눈다.
이 증명에서 얻는 세 목표는 정의에 적은 순서대로 반사성·대칭성·추이성이다.
각 정리에서 법 `n`을 고정하면 해당 조건의 증명이 되므로 `exact`로 마친다.

*보기* 자연수에서 $`a\leq b`라는 관계는 동치관계가 아니다.
이 관계에서는 $`0\leq1`이 성립하지만 그 반대인 $`1\leq0`은 성립하지 않으므로 대칭성이 없다.

```savedLean
example :
    ¬ IsEquivalence (fun a b : Nat => a ≤ b) := by
  intro h
  have h01 : 0 ≤ 1 := by decide

  -- 대칭성이 있다면 0 ≤ 1에서 1 ≤ 0을 얻어야 한다.
  have h10 : 1 ≤ 0 := by
    exact h.symm h01

  have hNot10 : ¬ 1 ≤ 0 := by decide
  exact hNot10 h10
```

`h.symm h01`은 대칭성을 사용하여 $`0\leq1`에서 $`1\leq0`을 얻는다.
`decide`로 확인한 그 부정 `hNot10`에 `h10`을 적용하면 모순이다.

# 동치류와 대표원
%%%
tag := "preliminaries-equivalence-classes"
file := "equivalence-classes"
%%%

동치관계가 주어지면 한 원소와 관계를 맺는 원소들을 모을 수 있다.
가령 $`7`을 법으로 하는 합동에서는 $`2`와 합동인 정수들을 모아
$`\{\ldots,-12,-5,2,9,16,23,\ldots\}`이라는 집합을 얻는다.

*정의* 동치관계 $`R`에 대하여 $`R(x,a)`를 만족하는 원소 $`x`들의 집합
$`[a]_R=\{x\in A:R(x,a)\}`를 $`a`의 *동치류*라고 한다.

```savedLean
def equivalenceClass {A : Type _} (R : Relation A) (a : A) :
    Set A :=
  fun x => R x a
```

`equivalenceClass R a`의 원소 조건은 `R x a`이다.
이 집합을 정의할 때는 관계 `R`만 있으면 되고
아래에서 동치류의 성질을 증명할 때는 `IsEquivalence R`를 가정한다.

동치류 $`[a]_R`를 나타내기 위해 택한 원소 $`a`를 *대표원*이라고 한다.
앞의 정수 집합은 $`23`과 합동인 정수들을 모아도 얻으므로 $`2`와 $`23`을 모두 대표원으로 택할 수 있다.
이처럼 관계를 만족하는 두 원소가 같은 동치류를 나타냄을 일반적으로 증명하자.

*정리* $`R`이 동치관계이고 $`R(a,b)`이면 $`[a]_R=[b]_R`이다.

*증명* $`x\in[a]_R`이라고 하자. 그러면 $`R(x,a)`이므로
가정 $`R(a,b)`와 추이성에 따라 $`R(x,b)`, 곧 $`x\in[b]_R`를 얻는다.
거꾸로 $`x\in[b]_R`이라고 하자.
대칭성으로 $`R(b,a)`를 얻고 여기에 $`R(x,b)`와 추이성을 사용하면 $`R(x,a)`, 곧 $`x\in[a]_R`이다.
두 동치류의 원소 조건이 동치이므로 두 집합은 같다.

```savedLean
theorem equivalenceClass_eq {A : Type _} (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (hab : R a b) :
    equivalenceClass R a = equivalenceClass R b := by
  ext x
  constructor
  · intro hx
    -- R(x,a)와 R(a,b)에 추이성을 사용한다.
    exact hR.trans hx hab

  · intro hx
    -- 대칭성으로 R(b,a)를 얻은 뒤 추이성을 사용한다.
    exact hR.trans hx (hR.symm hab)
```

`ext x`로 원소 조건의 동치를 목표로 삼은 뒤 `constructor`로 두 방향을 나눈다.
정방향에서는 `hR.trans`에 `R x a`와 `R a b`의 증명을 넣고
역방향에서는 `R x b`와 `hR.symm hab`로 얻은 `R b a`의 증명을 넣는다.

*보기* $`7`을 법으로 할 때 $`23`과 $`-5`의 동치류는 같다.
정수 절에서 $`23\equiv2\pmod7`과 $`-5\equiv2\pmod7`을 연결하여
$`23\equiv-5\pmod7`을 증명했다. 이 결과를 동치류의 등식에 사용하자.

```savedLean
example :
    equivalenceClass (Congruent 7) 23 =
    equivalenceClass (Congruent 7) (-5) := by
  apply equivalenceClass_eq (Congruent 7)
    (congruent_equivalence 7) 23 (-5)
  exact congruent_twenty_three_neg_five
```

`apply`에 합동 관계와 그 관계가 동치관계라는 증명을 주면
남은 목표는 `23 ≡ -5 [ZMOD 7]`이다.
이는 앞의 보기 `congruent_twenty_three_neg_five`에서 증명한 합동이므로
그 결과를 사용하면 두 동치류의 등식을 얻는다.

# 몫집합과 몫타입
%%%
tag := "preliminaries-quotients"
file := "quotients"
%%%

앞에서 정수 하나에 대하여 그 정수와 합동인 정수들의 집합을 만들었다.
$`2`를 법으로 하면 $`0`의 동치류는 짝수들의 집합이고 $`1`의 동치류는 홀수들의 집합이다.
이번에는 이 두 집합을 각각 하나의 원소로 갖는 집합을 생각하자.
정수를 원소로 갖는 짝수 집합과 달리, 이 새 집합의 원소는 짝수 집합과 홀수 집합이다.

*정의* 동치관계 $`R`에 대한 동치류 전체의 집합
$`A/R=\{[a]_R:a\in A\}`를 *몫집합*이라고 한다.

$`[a]_R`는 $`A`의 부분집합이므로 $`A/R`는 집합들을 원소로 갖는다.
따라서 Lean에서 몫집합의 타입은 `Set (Set A)`이다.
집합 `S : Set A`가 이 몫집합에 속한다는 조건은
어떤 원소 `a : A`에 대하여 `S = equivalenceClass R a`라는 것이다.

```savedLean
def quotientSet {A : Type _} (R : Relation A) :
    Set (Set A) :=
  fun S => ∃ a : A, S = equivalenceClass R a
```

가령 `quotientSet (Congruent 2)`의 원소는 짝수 집합과 홀수 집합이다.
대표원으로 $`0`과 $`2`를 각각 택해도 같은 짝수 집합을 얻으므로
두 대표원은 이 몫집합의 같은 원소를 가리킨다.

모든 동치류는 정의에 따라 몫집합에 속한다.
`equivalenceClass R a`가 어떤 원소의 동치류임을 보이려면 그 원소로 `a`를 제시하면 된다.

```savedLean
theorem equivalenceClass_mem_quotientSet {A : Type _}
    (R : Relation A) (a : A) :
    equivalenceClass R a ∈ quotientSet R := by
  exists a
```

## 몫집합의 원소 타입
%%%
tag := "relations-quotient-elements"
file := "quotient-elements"
%%%

이제 몫집합을 함수의 정의역이나 공역으로 사용하려고 한다.
앞의 {ref "functions-elements"}[집합 위의 함수]에서와 같이
동치류인 집합과 그 집합이 몫집합에 속한다는 증명을 묶으면 원소 타입을 얻는다.
이 원소 타입을 *몫타입*이라고 한다.

```savedLean
def QuotientType {A : Type _}
    (R : Relation A) :=
  Elem (quotientSet R)
```

수학에서 몫집합을 $`A/R`로 쓰는 것에 맞추어 이 원소 타입도 `A / R`로 표기하겠다.
여기서 `A`는 관계를 정의한 원소들의 타입이며, `A / R`은 `QuotientType (A := A) R`를 뜻한다.
`/`는 자연수와 정수의 나눗셈에 쓰는 것과 같은 기호이다.

```savedLean -show
attribute [reducible] QuotientType
scoped notation:70 (name := quotientTypeNotation) α " / " R:71 =>
  QuotientType (A := α) R

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display the quotient carrier and relation without unfolding its construction. -/
def Notation.delabQuotientType : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  withOverApp 2 do
    let carrier ← withNaryArg 0 delab
    let relation ← withNaryArg 1 delab
    return ⟨mkNode ``quotientTypeNotation #[carrier.raw, mkAtom "/", relation.raw]⟩

attribute [scoped delab app.Course.QuotientType] Notation.delabQuotientType
```

`q : A / R`이면 `q.val`은 동치류인 집합이고
`q.property`는 `q.val ∈ quotientSet R`의 증명이다.
`S ∈ quotientSet R`는 집합 `S`가 주어지면 쓸 수 있는 명제인 데 비해,
`A / R`의 원소를 만들려면 이 명제의 증명을 함께 제시해야 한다.

앞에서 증명한 `equivalenceClass_mem_quotientSet R a`를 사용하여
동치류를 몫타입의 원소로 만들자.

```savedLean
def classOf {A : Type _} (R : Relation A) (a : A) :
    A / R :=
  { val := equivalenceClass R a
    property := equivalenceClass_mem_quotientSet R a }
```

`classOf R a`의 값은 동치류인 집합 `equivalenceClass R a`이다.
따라서 서로 다른 대표원을 넣어도 같은 동치류를 얻으면 두 몫 원소는 같다.

앞으로 원소 `a`에 대응하는 몫 원소는 `⟦a⟧`로 표기하겠다.
몫타입이 `A / R`로 정해져 있으면 `⟦a⟧`는 `classOf R a`를 뜻한다.
가령 `F : A / R → B`일 때 `F ⟦a⟧`는 이 몫 원소에서의 함수값이다.
몫타입을 명시해야 할 때는 `(⟦a⟧ : A / R)`로 적는다.
`⟦`와 `⟧`는 각각 `\[[`와 `\]]`로 입력한다.

```savedLean -show
scoped notation:max (name := classOfNotation) "⟦" a "⟧" => classOf _ a

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display a quotient constructor using the ambient quotient type. -/
def Notation.delabClassOf : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  withOverApp 3 do
    let value ← withNaryArg 2 delab
    return ⟨mkNode ``classOfNotation #[mkAtom "⟦", value.raw, mkAtom "⟧"]⟩

attribute [scoped delab app.Course.classOf] Notation.delabClassOf
```

## 몫 원소의 등식
%%%
tag := "relations-quotient-equality"
file := "quotient-equality"
%%%

두 몫 원소가 같은지는 그 안에 담긴 집합을 비교하여 판단한다.
가령 몫타입 `A / R`의 두 원소 `⟦a⟧`와 `⟦b⟧`를 비교하려면
두 동치류 $`[a]_R`, $`[b]_R`가 같은지 확인하면 된다.
부분타입의 원소를 비교할 때는 값의 등식만 증명하면 되기 때문이다.

*정리* 동치관계 $`R`에 대한 몫타입 `A / R`에서 `⟦a⟧ = ⟦b⟧`일 필요충분조건은 $`R(a,b)`이다.

*증명* 두 몫 원소가 같으면 그 값인 동치류도 같다.
반사성에 따라 $`a\in[a]_R`이므로 $`a\in[b]_R`, 곧 $`R(a,b)`를 얻는다.
역방향에서는 앞에서 증명한 `equivalenceClass_eq`로 두 동치류의 등식을 얻고
부분타입의 원소도 같다고 결론 내린다.

```savedLean
theorem classOf_eq_iff {A : Type _} (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A) :
    (⟦a⟧ : A / R) = ⟦b⟧ ↔ R a b := by
  constructor
  · intro h
    indisc at h with hSets
    have ha : a ∈ equivalenceClass R a := by
      exact hR.refl a

    rw [hSets] at ha
    exact ha

  · intro hab
    ext
    exact equivalenceClass_eq R hR a b hab
```

첫 방향의 `indisc`은 부분타입의 값인 두 집합의 등식 `hSets`를 얻는다.
그 등식으로 `ha`의 집합을 바꾸면 `a ∈ equivalenceClass R b`가 되므로
원하는 관계 `R a b`를 얻는다.
역방향의 `ext`도 부분타입의 값만 비교하며,
남은 집합의 등식에는 앞의 정리 `equivalenceClass_eq`를 사용한다.

*보기* 짝수 집합과 홀수 집합을 원소로 갖는 타입을 다음과 같이 정의하자.

```savedLean
def Parity := Int / Congruent 2
def parityClass (a : Int) : Parity :=
  ⟦a⟧
```

```savedLean -show
attribute [reducible] Parity
```

앞의 `classOf_eq_iff`를 적용하면
두 몫 원소가 같다는 조건을 두 정수가 합동이라는 조건으로 바꿀 수 있다.

```savedLean
theorem parityClass_eq_iff (a b : Int) :
    parityClass a = parityClass b ↔ a ≡ b [ZMOD 2] := by
  exact classOf_eq_iff (Congruent 2)
    (congruent_equivalence 2) a b
```

```savedLean -show
attribute [course_compare] parityClass_eq_iff
```

이 비교도 `ext`와 `indisc`에 연결했다.
예를 들어 `parityClass 0 = parityClass 2`를 보일 때 `ext`를 사용하면
목표가 `0 ≡ 2 [ZMOD 2]`로 바뀐다.
$`0=2+2\cdot(-1)`이므로 합동의 정의에 필요한 정수로 $`-1`을 제시하면 된다.

```savedLean
theorem parityClass_zero_two :
    parityClass 0 = parityClass 2 := by
  ext
  exists (-1)
```

몫 원소의 등식이 가정으로 주어졌다면 `indisc`으로 두 대표원의 합동을 얻을 수 있다.
다음 예제의 `indisc`은 `h`를 `a ≡ b [ZMOD 2]`의 증명으로 바꾼다.

```savedLean
example (a b : Int)
    (h : parityClass a = parityClass b) :
    a ≡ b [ZMOD 2] := by
  indisc at h
  exact h
```

두 명령 모두 방금 증명한 `parityClass_eq_iff`를 사용한다.

## 대표원의 선택
%%%
tag := "relations-quotient-representatives"
file := "quotient-representatives"
%%%

몫타입 `A / R`에서 `⟦a⟧`는 원소 `a`의 동치류에 해당하는 몫 원소이다.
이번에는 몫 원소 `q`가 주어졌을 때 `q = ⟦a⟧`인 대표원 `a`를 하나 고르자.
가령 짝수 집합을 나타내는 몫 원소에서는 $`0`이나 $`2`를 대표원으로 택할 수 있다.
다음에서는 `A`에서 정의한 함수를 이용하여 몫집합 위의 함수를 만든다.
원래 함수가 `A`의 원소를 받으므로 몫 원소에서 대표원을 골라 그 함수에 넣는다.

`q : A / R`에는 동치류인 집합 `q.val`과
그 집합이 몫집합에 속한다는 증명 `q.property`가 담겨 있다.
따라서 `q.val`로 꺼내는 것은 대표원 하나가 아니라 동치류 전체이다.
대표원은 이 집합이 어떤 원소의 동치류인지 밝히는 존재명제에서 찾아야 한다.
`q.property`는 정의에 따라 `∃ a, q.val = equivalenceClass R a`의 증명이므로
`unpack`으로 대표원 `a`와 집합의 등식을 얻을 수 있다.
이 등식으로 부분타입의 값을 비교하면 `q = ⟦a⟧`를 얻는다.

```savedLean
theorem quotient_exists_classOf {A : Type _}
    (R : Relation A) (q : A / R) :
    ∃ a : A, q = ⟦a⟧ := by
  unpack q.property with ⟨a, ha⟩
  exists a
  ext
  exact ha
```

이 정리로 대표원의 존재를 확인했으므로
{ref "functions-existence-and-values"}[역함수를 구성할 때]와 같은 방법으로 대표원을 고르자.
`quotientReprData`에 `Classical.choose`로 고른 원소와
`Classical.choose_spec`으로 얻은 등식의 증명을 함께 담는다.
이어서 `.val`로 대표원을, `.property`로 그 대표원이 원래 몫 원소를 나타낸다는 증명을 꺼낸다.

```savedLean
noncomputable def quotientReprData {A : Type _}
    (R : Relation A) (q : A / R) :
    { a : A // q = ⟦a⟧ } :=
  { val := Classical.choose (quotient_exists_classOf R q)
    property :=
      Classical.choose_spec (quotient_exists_classOf R q) }

noncomputable def quotientRepr {A : Type _}
    (R : Relation A) (q : A / R) : A :=
  (quotientReprData R q).val
theorem quotientRepr_spec {A : Type _}
    (R : Relation A) (q : A / R) :
    q = ⟦quotientRepr R q⟧ := by
  exact (quotientReprData R q).property
```

`quotientRepr R q`는 대표원이며 `quotientRepr_spec R q`는
`q = ⟦quotientRepr R q⟧`의 증명이다.
가령 `q`가 `parityClass 0`이면 선택한 정수가 반드시 `0`일 필요는 없지만,
`parityClass_eq_iff`에 따라 그 정수는 $`0`과 합동이다.

## 몫집합 위의 함수
%%%
tag := "preliminaries-quotient-functions"
file := "quotient-functions"
%%%

짝수 집합에는 `0`을, 홀수 집합에는 `1`을 대응시키는 함수를 만들자.
정수 하나가 주어졌다면 그 수를 `2`로 나눈 나머지를 계산하면 된다.
몫집합에서는 정수들의 동치류를 인수로 받으므로
이 계산을 이용하려면 먼저 그 동치류에서 정수 하나를 골라야 한다.
짝수 집합에서 `0`을 고르든 `2`를 고르든 나머지는 `0`이고,
홀수 집합에서 `1`을 고르든 `23`을 고르든 나머지는 `1`이다.
따라서 대표원을 골라 그 나머지를 취하면 원하는 함수값을 얻는다.

이때 대표원을 바꾸어도 값이 같다는 사실이 중요하다.
가령 $`F([a])=a`라는 규칙으로는 함수를 정의할 수 없다.
$`[0]=[2]`인 같은 짝수 집합에서 $`F([0])=0`, $`F([2])=2`라는 서로 다른 값을 요구하기 때문이다.
먼저 $`F([a])=a`라는 규칙이 불가능하다는 설명을 증명으로 적자.
이 조건이 모든 정수에서 성립한다고 가정하면
`parityClass_zero_two`로 $`[0]=[2]`를 사용하여 $`0=2`라는 모순을 얻는다.

```savedLean
example :
    ¬ ∃ F : Parity → Int, ∀ a, F (parityClass a) = a := by
  intro h
  unpack h with ⟨F, hF⟩
  have hZero : F (parityClass 0) = 0 :=
    hF 0
  rw [parityClass_zero_two, hF 2] at hZero
  contradiction
```

`rw`의 첫 등식으로 같은 몫 원소를 다른 대표원으로 나타낸 뒤
두 번째 등식으로 그 함수값을 $`2`로 바꾸면 `hZero`는 `2 = 0`의 증명이 된다.
나머지를 취하는 규칙에서는 같은 동치류의 두 대표원이 같은 나머지를 갖기 때문에
이러한 충돌이 생기지 않는다.

*보기* $`a\equiv b\pmod2`이면 $`a\bmod2=b\bmod2`이다.

*풀이* 합동의 정의에 따라 $`a=b+2k`인 정수 $`k`가 존재한다.
두 수의 차이가 $`2`의 배수이므로 $`2`로 나눈 나머지는 같다.
Lean에서도 `rcases`로 이 정수 `k`와 등식 `hk`를 얻은 뒤 `arith`로 나머지의 등식을 확인한다.

```savedLean
theorem congruent_two_same_remainder (a b : Int)
    (hab : a ≡ b [ZMOD 2]) :
    a % 2 = b % 2 := by
  rcases hab with ⟨k, hk⟩
  arith
```

같은 방법을 동치관계 $`R`과 일반적인 함수 $`f:A\to B`에 적용하자.
이 함수로부터 $`F:A/R\to B`를 정의하여 모든 $`a`에 대해
$`F([a]_R)=f(a)`가 되게 하려고 한다.
$`R(a,b)`이면 $`[a]_R=[b]_R`이므로
$`F([a]_R)=F([b]_R)`이며, 원하는 등식이 성립하려면 다음 조건이 필요하다.

$$`R(a,b)\ \Longrightarrow\ f(a)=f(b).`

이 조건이 성립하면 동치류 $`S`의 대표원 $`a`를 골라 $`F(S)=f(a)`로 정할 수 있다.
다른 대표원 $`b`를 사용해도 $`R(a,b)`이므로 $`f(a)=f(b)`이며 같은 함수값을 얻는다.
이처럼 대표원의 선택에 무관하게 함수값이 정해질 때
동치류 위의 함수가 *잘 정의된다*고 한다.

*정리* 동치관계 $`R`에 대하여 함수 $`f`가
$`R(a,b)\Rightarrow f(a)=f(b)`를 만족한다고 하자.
그러면 모든 $`a\in A`에 대하여 $`F([a]_R)=f(a)`인 함수 $`F:A/R\to B`가 존재한다.

*증명* 각 몫 원소 $`q`에서 `quotientRepr`로 대표원 하나를 골라
그 원소에 $`f`를 적용한 값을 $`F(q)`로 정하자.
이 함수가 원하는 등식을 만족하는지 확인하기 위해
몫 원소 $`[a]_R`에서 고른 대표원을 $`b`라고 하자.
대표원을 고를 때 얻은 등식은 $`[a]_R=[b]_R`이므로
그 방향을 바꾸고 앞의 `classOf_eq_iff`를 사용하면 $`R(b,a)`를 얻는다.
가정으로 받은 조건에 따라 $`f(b)=f(a)`이며,
왼쪽 $`f(b)`가 바로 정의한 함수의 $`[a]_R`에서의 값이다.

Lean에서는 함수와 모든 대표원에 대한 계산 규칙을 함께 구성하자.
`quotientLiftData`의 `val`에는 $`q\mapsto f(\operatorname{quotientRepr}(q))`를 넣고,
`property`에서는 `∀ a, F ⟦a⟧ = f a`를 증명한다.
이때 함수의 정의를 계산하면 남는 등식은 다음과 같다.

```
f (quotientRepr R ⟦a⟧) = f a
```

선택한 대표원과 `a`는 서로 다를 수 있지만 같은 동치류를 나타낸다.
따라서 두 대표원 사이의 관계를 먼저 보이고, 가정 `hf`를 사용하여 함수값이 같음을 증명한다.

{anchor "relations-local-definitions"}[]선택한 대표원을 나타내는 식이 길므로 코드에서는 `let b := ...`로 `b`라는 이름을 붙인다.
`let 이름 : 타입 := 값`은 증명 안에서 사용할 값을 정의하는 문법이며 타입은 추론할 수 있으면 생략한다.
앞에서 `have`로 중간 명제의 증명에 이름을 붙였던 것처럼,
여기서는 `let`으로 원소를 정의하여 이어지는 논증에서 사용한다.

```savedLean
noncomputable def quotientLiftData {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) :
    { F : A / R → B //
      ∀ a, F ⟦a⟧ = f a } :=
  { val := fun q => f (quotientRepr R q)
    property := by
      intro a
      let b := quotientRepr R ⟦a⟧
      have hRelation : R b a := by
        apply (classOf_eq_iff R hR b a).mp
        exact (quotientRepr_spec R ⟦a⟧).symm

      -- 같은 동치류에서 f의 값은 같다.
      exact hf b a hRelation }
```

`quotientRepr_spec`으로 얻은 $`[a]_R=[b]_R`의 방향을 바꾸고
`classOf_eq_iff`를 사용하면 `hRelation : R b a`를 얻는다.
마지막의 `hf b a hRelation`이 `f b = f a`를 증명하므로
대표원을 골라 정의한 함수가 모든 대표원에서 원하는 값을 갖는다.

이제 `.val`로 함수를 꺼내 `quotientLift`로 정의하고,
함께 증명한 등식은 `quotientLift_classOf`로 사용하자.
이 정리는 `.property`에 대표원 `a`를 넣어 얻는다.

```savedLean
noncomputable def quotientLift {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) :
    A / R → B :=
  (quotientLiftData R hR f hf).val
theorem quotientLift_classOf {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b)
    (a : A) :
    quotientLift R hR f hf ⟦a⟧ = f a := by
  exact (quotientLiftData R hR f hf).property a
```

*보기* 이제 처음에 생각한 나머지 함수를 정의하자.
`Congruent 2`가 동치관계라는 증명과 원래 함수 `fun a => a % 2`를 준비하고,
대표원을 바꾸어도 나머지가 같다는 증명 `congruent_two_same_remainder`를
함께 `quotientLift`에 넣자.

```savedLean
noncomputable def parityRemainder : Parity → Int :=
  quotientLift (Congruent 2) (congruent_equivalence 2)
    (fun a => a % 2) congruent_two_same_remainder
```

정의할 때 함께 구성한 성질을 `quotientLift_classOf`로 꺼내면
`parityRemainder (parityClass a) = a % 2`를 얻는다.

```savedLean
theorem parityRemainder_class (a : Int) :
    parityRemainder (parityClass a) = a % 2 := by
  exact quotientLift_classOf (Congruent 2)
    (congruent_equivalence 2) (fun a => a % 2)
    congruent_two_same_remainder a
```

이 정리로 몫 원소에서의 함수값을 대표원을 $`2`로 나눈 나머지로 바꾸어 계산할 수 있다.
가령 $`0`의 동치류에서는 $`0`을, $`23`과 $`-5`의 동치류에서는 $`1`을 얻는다.

```savedLean
example : parityRemainder (parityClass 0) = 0 := by
  rw [parityRemainder_class]
  decide

example : parityRemainder (parityClass 23) = 1 := by
  rw [parityRemainder_class]
  decide

example : parityRemainder (parityClass (-5)) = 1 := by
  rw [parityRemainder_class]
  decide
```

각 증명은 먼저 몫 원소에서의 함수값을 대표원의 나머지로 바꾼 뒤 그 나머지를 계산한다.
`23`과 `-5`는 같은 홀수 집합을 나타내므로 두 예제에서 같은 함수값을 얻는다.

*보기* $`0`과 $`1`의 동치류는 서로 다르다.
같은 몫 원소라면 `parityRemainder`의 값도 같아야 하는데
각각의 나머지는 $`0`, $`1`이므로 모순이다.

```savedLean
theorem parityClass_zero_ne_one :
    parityClass 0 ≠ parityClass 1 := by
  intro h
  have hRemainders :
      parityRemainder (parityClass 0) =
        parityRemainder (parityClass 1) := by
    rw [h]

  rw [parityRemainder_class,
    parityRemainder_class] at hRemainders
  contradiction
```

이 증명은 두 동치류의 원소를 모두 비교하는 대신
이미 정의한 함수의 값으로 두 몫 원소를 구별한다.
일반적으로 $`f(x)\ne f(y)`임을 알면 $`x\ne y`임을 보일 수 있다.

대표원을 고르는 방식을 바꾸어 함수를 구성해도 같은 결과를 얻는지 확인하자.
어떤 방식으로 구성했든 모든 대표원에서 $`F([a]_R)=f(a)`를 만족한다면,
다음 유일성에 따라 같은 함수가 된다.

*정리* 두 함수 $`F,G:A/R\to B`가 모든 $`a\in A`에 대하여
$`F([a]_R)=f(a)`와 $`G([a]_R)=f(a)`를 만족하면 $`F=G`이다.

*증명* 임의의 몫 원소 $`q`는 어떤 대표원 $`a`에 대해 $`q=[a]_R`로 나타낼 수 있다.
따라서 $`F(q)=F([a]_R)=f(a)=G([a]_R)=G(q)`이며 두 함수는 모든 원소에서 값이 같다.

```savedLean
theorem quotientLift_unique {A B : Type _}
    (R : Relation A) (f : A → B)
    (F G : A / R → B)
    (hF : ∀ a, F ⟦a⟧ = f a)
    (hG : ∀ a, G ⟦a⟧ = f a) :
    F = G := by
  ext q
  unpack quotient_exists_classOf R q with ⟨a, ha⟩
  rw [ha, hF a, hG a]
```

`ext q`로 임의의 몫 원소에서 두 함수값을 비교한다.
`quotient_exists_classOf R q`는 `∃ a, q = ⟦a⟧`의 증명이므로
`unpack`으로 대표원과 등식을 얻은 뒤 `rw`로 두 함수값을 모두 `f a`로 바꾼다.

# 연습문제
%%%
tag := "relations-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 1* 모든 원소는 자신의 동치류에 속함을 증명하라.

```savedLean -keep
theorem exercise_mem_own_equivalenceClass
    (R : Relation A)
    (hR : IsEquivalence R)
    (a : A) :
    a ∈ equivalenceClass R a := by
  sorry
```


*문제 2* 함수 $`f:A\to B`에 대하여 $`f(x)=f(y)`로 정한 관계가 동치관계임을 증명하라.

```savedLean -keep
theorem exercise_equal_values_equivalence (f : A → B) :
    IsEquivalence (fun x y : A => f x = f y) := by
  sorry
```


*문제 3* 동치관계 $`R`에 대하여 $`[a]_R=[b]_R`이면 $`R(a,b)`임을 증명하라.

```savedLean -keep
theorem exercise_relation_of_classes_equal
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : equivalenceClass R a = equivalenceClass R b) :
    R a b := by
  sorry
```

*힌트* 반사성으로 $`a\in[a]_R`를 얻은 뒤 두 동치류가 같다는 가정을 사용하라.

*문제 4* $`3`과 $`1`이 같은 홀수 동치류를 나타냄을 증명하라.
이 결과와 `parityClass_zero_ne_one`을 사용하여 $`3`의 동치류와 $`0`의 동치류가 다름을 보이라.

```savedLean -keep
theorem exercise_parityClass_three_one :
    parityClass 3 = parityClass 1 := by
  sorry

theorem exercise_parityClass_three_ne_zero :
    parityClass 3 ≠ parityClass 0 := by
  sorry
```

*문제 5* (첫 좌표가 같은 점들)

두 좌표가 모두 정수인 점들 사이에 첫 좌표가 같다는 관계를 정의한다.
(1) 이 관계가 동치관계임을 증명하라.
(2) $`(a,b)`의 동치류가 첫 좌표가 $`a`인 점들의 집합임을 보이라.
(3) 첫 결과와 `equivalenceClass_eq`를 사용하여 $`(2,3)`과 $`(2,-5)`의 동치류가 같음을 보이라.

```savedLean -keep
def practiceSameFirst : Relation (Int × Int) :=
  fun p q => p.1 = q.1
theorem exercise_sameFirst_equivalence :
    IsEquivalence practiceSameFirst := by
  sorry

theorem exercise_sameFirst_class (a b : Int) :
    equivalenceClass practiceSameFirst (a, b) =
      (fun p => p.1 = a) := by
  sorry

theorem exercise_vertical_class :
    equivalenceClass practiceSameFirst (2, 3) =
      equivalenceClass practiceSameFirst (2, -5) := by
  sorry
```

*문제 6* (겹치는 동치류)

(1) 동치관계의 두 동치류가 공통 원소를 가지면 두 동치류가 같음을 증명하라.
(2) $`6`을 법으로 하는 합동에서 $`2`가 $`8`과 $`20`의 동치류에 모두 속함을 보이라.
(3) 앞의 두 결과를 사용하여 두 동치류가 같음을 보이라.

```savedLean -keep
theorem exercise_classes_of_common_element
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : ∃ x, x ∈ equivalenceClass R a ∧
      x ∈ equivalenceClass R b) :
    equivalenceClass R a = equivalenceClass R b := by
  sorry

theorem exercise_mod_six_common :
    ∃ x, x ∈ equivalenceClass (Congruent 6) 8 ∧
      x ∈ equivalenceClass (Congruent 6) 20 := by
  sorry

theorem exercise_mod_six_classes :
    equivalenceClass (Congruent 6) 8 =
      equivalenceClass (Congruent 6) 20 := by
  sorry
```

*문제 7* (대표원에 따라 달라지는 값)

모든 정수 $`a`에 대하여 $`F([a])=a\bmod3`을 만족하는 함수 $`F:\operatorname{Parity}\to\mathbb{Z}`는 존재하지 않음을 증명하라.
여기서 $`[a]`는 $`2`를 법으로 한 동치류이다.
같은 동치류에 속하지만 $`3`으로 나눈 나머지가 다른 두 정수를 찾으라.

```savedLean -keep
theorem exercise_parity_no_mod_three :
    ¬ ∃ F : Parity → Int,
      ∀ a, F (parityClass a) = a % 3 := by
  sorry
```

*문제 8* (짝수 동치류와 홀수 동치류의 교환)

동치류 $`[a]`에 $`[a+1]`을 대응시키는 함수를 구성한다.
(1) $`a\equiv b\pmod2`이면 $`[a+1]=[b+1]`임을 증명하여 대표원에 무관함을 확인하라.
(2) 이 증명을 사용한 아래 함수의 계산 규칙을 증명하라.
(3) 이 함수를 두 번 적용하면 원래 몫 원소를 얻음을 보이라.

```savedLean -keep
theorem exercise_nextParity_respects (a b : Int)
    (hab : Congruent 2 a b) :
    parityClass (a + 1) = parityClass (b + 1) := by
  sorry

noncomputable def practiceNextParity : Parity → Parity :=
  quotientLift (Congruent 2) (congruent_equivalence 2)
    (fun a => parityClass (a + 1))
    exercise_nextParity_respects
theorem exercise_nextParity_class (a : Int) :
    practiceNextParity (parityClass a) =
      parityClass (a + 1) := by
  sorry

theorem exercise_nextParity_twice (q : Parity) :
    practiceNextParity (practiceNextParity q) = q := by
  sorry
```

*힌트* 마지막 증명에서는 `quotient_exists_classOf`로 `q`의 대표원을 얻은 뒤 두 번째 결과를 사용하라.

```savedLean
end Course
```
