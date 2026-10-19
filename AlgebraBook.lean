import VersoManual
import AlgebraBook.Foundations
import AlgebraBook.Groups
import AlgebraBook.Tactics
import AlgebraBook.Symbols

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean으로 배우는 대수학" =>

%%%
tag := "home"
%%%

이 교재에서는 수학의 정의를 Lean으로 옮기고 그 정의를 사용하여 정리를 증명하며
수학적 설명과 Lean 코드를 나란히 읽으면서 대수학을 공부한다.

*읽는 방법*

각 절은 개념을 소개하는 설명에서 시작하여 정의, 정리와 증명으로 이어진다.
먼저 수학적 의미를 이해한 뒤 Lean 코드를 읽고, 보기와 연습문제를 풀며 익히라.
코드의 이름에 마우스를 올리면 타입을 확인할 수 있고,
증명 코드의 전술을 누르면 그 단계의 가정과 목표를 펼쳐 볼 수 있다.
같은 전술을 다시 누르면 접힌다.

`instance`처럼 기호 사용을 위한 보조 선언은 해당 설명에서 역할을 확인하며 읽으면 되고,
그 세부 문법은 필요한 때 다시 익혀도 좋다.

입문부는 Lean의 값과 함수에서 시작하여 명제와 증명으로 이어진다.
이후에는 집합과 대수적 구조의 정의를 직접 작성하고 그 성질을 증명한다.
전술의 용법은 {ref "tactic-reference"}[전술 일람]에서,
기호의 입력법은 처음 등장하는 절을 표시한 {ref "symbol-reference"}[기호 부록]에서 찾을 수 있다.

제목에 *Advanced*가 붙은 절은 선택해서 읽는 보충 내용이다.
이후의 기본 본문에서는 Advanced 절의 내용을 요구하지 않으며,
이후 Advanced 절에서 앞선 Advanced 내용을 사용할 때는 필요한 선수 지식을 명시한다.


*두 가지 읽기 순서*

정의와 증명을 차례로 구축하려면 준비 장 전체를 읽은 뒤 연산과 군으로 진행하라.
군론을 먼저 공부하려면 {ref "mathematical-preliminaries"}[자연수와 정수]까지 읽고
2장의 군의 정의, 기본 계산, 군의 곱과 순열군을 살펴보라.
{ref "group-order"}[유한군과 위수]를 읽기 전에는
{ref "relations"}[동치관계와 몫집합]과 {ref "cardinality"}[집합의 크기와 유한성]으로 돌아온다.
{ref "infinite-cardinality"}[무한집합의 크기]는 이 경로를 마친 뒤 읽어도 좋다.

*학습 순서*

1. 준비: Lean의 기본 문법과 증명, 집합과 함수, 정수와 동치관계, 집합의 크기
2. 군론: 연산과 군, 구체적인 예와 거듭제곱, 부분군과 순환군, 잉여류와 라그랑주 정리,
   준동형과 몫군, 군의 작용, 실로 정리와 군의 구조
3. 환론: 환과 체의 기본 예, 아이디얼과 몫환, 다항식과 인수분해
4. 가군과 선형대수: 가군과 벡터공간, 선형사상과 행렬, 텐서곱, PID 위 가군의 구조와 표준형
5. 체론과 갈루아 이론: 체의 확대와 분해체, 유한체, 갈루아 대응, 방정식과 갈루아 군
6. 가환대수와 표현론: 국소화와 뇌터 환, 정수적 확대와 차원, 유한군의 표현과 지표
7. 확장 과정: 비가환대수, 호몰로지 대수, 리 대수

현재 본문은 준비 장과 군의 기본 예제, 거듭제곱과 유한군의 위수까지 다룬다.
위 목록은 이후 집필할 내용을 포함한 전체 학습 순서이다.

{include 1 AlgebraBook.Foundations}
{include 1 AlgebraBook.Groups}
{include 1 AlgebraBook.Tactics}
{include 1 AlgebraBook.Symbols}
