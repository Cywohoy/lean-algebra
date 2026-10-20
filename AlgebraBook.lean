import VersoManual
import AlgebraBook.Foundations
import AlgebraBook.Tactics
import AlgebraBook.Symbols

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean으로 배우는 기초 수학" =>

%%%
tag := "home"
%%%

이 교재는 익숙한 수학적 정의와 증명을 Lean으로 옮기는 방법을 다룬다.
Lean을 처음 접하는 독자를 위해 값과 함수, 명제와 증명의 표기에서 시작하여
집합과 함수의 성질, 자연수와 정수, 동치관계와 몫집합, 유한집합과 무한집합의 크기를 차례로 살펴본다.
수학적 설명과 Lean 코드를 함께 읽으며 각 증명의 가정과 결론이 어떻게 이어지는지 확인하라.

*읽는 방법*

각 절은 개념을 소개하는 설명에서 시작하여 정의, 정리와 증명으로 이어진다.
먼저 수학적 의미를 이해한 뒤 Lean 코드를 읽고, 보기와 연습문제를 풀며 익히라.
앞에서 정의한 대상과 증명한 정리를 뒤에서 사용하므로 처음에는 순서대로 읽는 것이 좋다.
1.1~1.8절은 각각 한 페이지에서 이어 읽을 수 있으며, 목차의 소제목을 누르면 그 위치로 이동한다.
설명 사이의 짧은 연습문제로 방금 배운 방법을 써 보고, 절 끝의 문제에서 여러 결과를 함께 사용하라.

코드의 이름에 마우스를 올리면 타입을 확인할 수 있고,
증명 코드의 전술을 누르면 그 단계의 가정과 목표를 펼쳐 볼 수 있다.
같은 전술을 다시 누르면 접힌다.
`instance`처럼 기호 사용을 위한 보조 선언은 해당 설명에서 역할을 확인하며 읽으면 되고,
그 세부 문법은 필요한 때 다시 익혀도 좋다.

전술의 용법은 {ref "tactic-reference"}[전술 일람]에서,
기호의 입력법은 처음 등장하는 절을 표시한 {ref "symbol-reference"}[기호 부록]에서 찾을 수 있다.
제목에 *Advanced*가 붙은 절은 선택해서 읽는 보충 내용이다.
이후의 기본 본문에서는 Advanced 절의 내용을 요구하지 않으며,
이후 Advanced 절에서 앞선 Advanced 내용을 사용할 때는 필요한 선수 지식을 명시한다.

{include 1 AlgebraBook.Foundations}
{include 1 AlgebraBook.Tactics}
{include 1 AlgebraBook.Symbols}
