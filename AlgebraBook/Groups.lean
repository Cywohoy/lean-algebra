import VersoManual
import AlgebraBook.Operations
import AlgebraBook.Groups.Definition
import AlgebraBook.GroupExamples

open Verso.Genre Manual
open AlgebraBook

#doc (Manual) "연산과 군" =>

%%%
tag := "operations-and-groups"
file := "operations-and-groups"
%%%

이 장에서는 이항연산의 성질을 모아 군을 정의하고
그 법칙으로 원소 사이의 등식을 증명한다.
정수의 덧셈군과 두 원소 군에서 출발하여 역원과 거듭제곱을 계산한 뒤,
군의 곱과 순열군을 구성한다.

이 기본 성질들을 직접 증명한 다음 군 계산의 자동화를 소개한다.
마지막 절에서는 준비 장의 집합의 크기를 사용하여 유한군의 위수를 다룬다.

```savedImport
import AlgebraBook.GroupExamples
```

{include 1 AlgebraBook.Operations}
{include 1 AlgebraBook.Groups.Definition}
{include 1 AlgebraBook.Groups.Calculations}
{include 1 AlgebraBook.Groups.Powers}
{include 1 AlgebraBook.Groups.Products}
{include 1 AlgebraBook.Groups.Permutations}
{include 1 AlgebraBook.Groups.Automation}

{include 1 AlgebraBook.Groups.Order}
