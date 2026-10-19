import VersoManual
import AlgebraBook.Introduction
import AlgebraBook.Proofs
import AlgebraBook.Sets
import AlgebraBook.Functions
import AlgebraBook.Numbers
import AlgebraBook.Relations
import AlgebraBook.FiniteCardinality
import AlgebraBook.InfiniteCardinality

open Verso.Genre Manual

#doc (Manual) "준비: Lean과 기초 수학" =>

%%%
tag := "foundations"
file := "foundations"
%%%

이 장에서는 Lean의 기본 표기를 익히고 대수학에 필요한 집합과 함수의 정의 및 기초 수학을 Lean으로 옮긴다.
값과 함수, 명제와 술어의 표기를 배운 뒤 함의와 전칭명제의 증명을 구성한다.
이를 바탕으로 집합과 함수의 성질을 증명하고 자연수와 정수의 계산을 익힌다.

수학적으로 알고 있는 사실도 Lean으로 옮기다 보면 새로운 표현이나 증명 방법이 필요하다.
본문에서는 이미 배운 방법으로 증명을 시작하고, 남은 목표를 살펴보면서 필요한 개념을 도입한다.
각 단계에서 무엇을 가정하고 무엇을 보이는지 수학적 논증과 비교하며 읽으라.

뒤의 세 절에서는 동치관계와 몫집합을 구성한 뒤 전단사로 집합의 크기를 비교한다.
유한집합의 원소 수를 정의하고 그 유일성을 증명한 다음 무한집합의 크기를 살펴본다.

이 장은 Lean을 처음 접하는 독자가 집합과 함수의 증명을 직접 작성할 수 있도록 구성했다.
앞의 절에서 정의한 대상과 증명한 정리를 뒤에서 사용하므로 처음에는 순서대로 읽는 것이 좋다.
제목에 *Advanced*가 붙은 보충 설명은 건너뛰어도 이후의 기본 본문을 읽을 수 있다.
각 절의 연습문제는 그 절까지 배운 정의와 증명 방법으로 풀 수 있으며,
여러 소문제로 이루어진 문제에서는 앞에서 얻은 결과를 이어서 사용한다.

군론을 먼저 공부하려면 1.1~1.5를 읽고 2.1~2.7로 진행한 뒤,
{ref "group-order"}[유한군과 위수] 앞에서 1.6~1.7로 돌아오라.
무한집합의 크기를 다루는 1.8은 기초 군론을 읽는 데 필요한 선수 내용이 아니다.

{include 1 AlgebraBook.Introduction}
{include 1 AlgebraBook.Proofs}
{include 1 AlgebraBook.Sets}
{include 1 AlgebraBook.Functions}
{include 1 AlgebraBook.Numbers}
{include 1 AlgebraBook.Relations}
{include 1 AlgebraBook.FiniteCardinality}
{include 1 AlgebraBook.InfiniteCardinality}
