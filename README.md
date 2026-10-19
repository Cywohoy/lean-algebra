# Lean으로 배우는 대수학

전술과 수학 코드의 독립 라이브러리는 별도 Git 프로젝트 [Ample](https://github.com/Cywohoy/ample)에서 관리한다.
개발할 때는 두 저장소를 나란히 두고 교재에서 `../Ample`을 Lake 경로 의존성으로 가져온다.
Ample 자체는 Verso나 교재 문서에 의존하지 않는다.
Ample은 공개하고 교재 저장소는 현재 비공개로 관리한다.
교재에서 수학 코드를 수정하면 `python scripts/sync_ample.py`로 Ample에 반영하고,
`python scripts/sync_ample.py --check`로 두 저장소의 코드가 일치하는지 검사한다.
Ample의 위치가 다르면 `--ample-root 경로`를 지정한다.
개인 풀이인 `Exercises/`와 생성된 문서는 Git 추적에서 제외한다.
본문과 새 연습문제는 `Ample` 이름공간과 `Ample.Auto` 설정을 사용한다.
기존 개인 풀이의 `open Course`, `open scoped Course.Auto`와 `Course.singleton` 같은 이름은
교재의 호환 모듈이 연결하므로 풀이 파일을 고칠 필요가 없다.
기존 Cubical 실험은 `C:/Users/Cywohoy/Documents/AmpleCTT`로 옮겨 보관했다.

수업에서 배우는 수학적 정의를 직접 구현하며 공부하는 한국어 대수학 교재이다.
한국어 설명, 수식, Lean 정의와 증명을 Verso로 웹 문서에 함께 담는다.
현재 **준비: Lean과 기초 수학**, **연산과 군**을 수록한다.
준비 장은 1.1 Lean의 기본 문법, 1.2 증명의 구성과 사용, 1.3 집합의 구성,
1.4 함수, 1.5 자연수와 정수, 1.6 동치관계와 몫집합,
1.7 집합의 크기와 유한성, 1.8 무한집합의 크기로 구성한다.
군론을 먼저 공부하려면 1.1~1.5를 읽고 2.1~2.7로 진행한다.
2.8 유한군과 위수 앞에서는 1.6~1.7을 읽고, 1.8은 이후에 이어 읽을 수 있다.
2장은 2.1 이항연산, 2.2 군의 정의와 기본 성질, 2.3 역원과 곱의 계산,
2.4 거듭제곱, 2.5 군의 곱, 2.6 순열군, 2.7 군 계산의 자동화,
2.8 유한군과 위수로 구성한다. 두 원소 군은 2.2에서 구성하고 이후 절에서 다시 사용한다.
전술 일람과 기호 입력은 별도의 부록으로 둔다.
**기호 입력** 부록에는 기호를 하나의 표에 모으고 처음 등장하는 절을 표시했다.
집합을 정의하는 절에는 짧은 subsection인 **Advanced: 원소의 타입과 러셀의 역설**을 덧붙였다.
집합의 크기에는 **Advanced: 무한집합과 자연수의 단사**를 두어 원소의 선택과 재귀적 구성으로 자연수 집합이 가장 작은 무한집합임을 보인다.
이 구성에 필요한 두 보조정리는 연습문제로 둔다.
멱집합의 정의와 칸토어 정리, 대각선 논법의 수학적 설명과 Lean 증명은 기본 본문에 둔다.
동치류 뒤에는 몫집합 `quotientSet R`을 집합들의 집합으로 정의하고,
원소 타입 `Elem (quotientSet R)`을 몫타입으로 사용한다.
몫 원소의 등식을 동치류의 등식에 연결한 뒤 `quotientRepr`로 대표원을 고른다.
몫집합 위의 함수는 짝수·홀수의 두 부류에 나머지를 대응시키는 예에서 출발하며,
대표원을 통해 원래 함수를 적용하는 이유와 대표원을 바꾸어도 함수값이 같아야 하는 조건을 설명한다.
기수 타입 `Cardinal`은 원소 타입들을 전단사 관계로 묶은 몫타입이며
`cardinal A = cardinal B`와 `SameCardinality A B`를 연결한다.
전단사 관계의 반사성·대칭성·추이성 바로 뒤에 이를 정의하고 이후의 크기 비교를 기수의 등식과 부등식으로 서술한다.
유한집합의 원소 수는 `cardinal A = cardinal (Fin n)`으로 나타내며
번호 수의 유일성을 증명한 뒤에는 자연수를 기수로 바꾸어 `cardinal A = n`으로 쓴다.
`IsCountablyInfinite A`는 `cardinal Nat = cardinal A`이다.
기수의 대소 관계는 대표원에 무관하도록 정의하며 칸토어 정리도 `cardinal A < cardinal (Set A)`로 쓴다.
유한집합의 원소 수를 자연수로 꺼내는 기존 `cardinality A hA`는 유지한다.
Advanced 절은 이후 기본 본문의 선수 지식이 아니며, 이후 Advanced 절에서는 선수 지식으로 명시한 경우 앞선 Advanced 내용을 사용할 수 있다.

## 집필 계획

전체 범위와 선수 관계는 [교재 구성과 집필 계획](CURRICULUM.md)에 정리했다.
군·환·가군·체·갈루아 이론에서 가환대수와 표현론으로 이어지고,
확장 과정에는 비가환대수·호몰로지 대수·리 대수의 입문을 둔다.
현재 구성의 선수관계와 다음 집필 준비는 [부분군과 순환군 집필 준비](planning/NextChapter.md)에 정리했다.
다음 집필 대상은 3장 **부분군과 순환군**이다.
[준비 코드](planning/GroupExamples.lean)는 본문과 구별하여 검사한다.


## 준비

- Git과 [elan](https://github.com/leanprover/elan)을 설치한다.
- 이 폴더를 VS Code에서 열고 Lean 4 확장을 사용한다.
- Lean과 Verso는 **v4.35.0**으로 고정한다.
  `lean-toolchain`이 프로젝트의 Lean 버전을 선택하므로 전역 기본 버전을 바꿀 필요는 없다.
- Verso와 그 의존 패키지는 첫 빌드에서 자동으로 준비된다.
  별도의 Python, Node.js, mathlib 설치는 필요하지 않다.
- `by_contra`는 `Ample.Tactic.Classical`에서 구현하며 기존 교재 경로로도 가져올 수 있다.
  수학적 정의와 핵심 증명은 교재에서 직접 작성한다.

두 저장소를 새로 받을 때는 같은 폴더에서 다음과 같이 실행한다.
교재를 받으려면 비공개 저장소에 접근할 수 있는 GitHub 계정으로 로그인해야 한다.

```powershell
git clone https://github.com/Cywohoy/ample.git Ample
git clone https://github.com/Cywohoy/lean-algebra.git Textbook
cd Textbook
lake update ample
```

## 문서 생성

프로젝트 폴더에서 다음 명령을 실행하라.

```powershell
lake exe textbook
```

결과는 `_out/html-multi/`에 생성된다.
본문에 있는 Lean 코드도 함께 검사되므로, 증명이 잘못되면 빌드가 실패한다.

## 미리보기

Windows에서는 `preview.bat`를 더블클릭하라.
교재 생성과 예제 검사가 끝나면 미리보기 서버가 실행된다.
실행 창을 열어 둔 동안 서버가 계속 돌아간다.
서버를 끄려면 `Ctrl+C`를 누르거나 실행 창을 닫는다.
오류가 발생하면 창이 열린 채로 남으므로 메시지를 확인할 수 있다.

다음 명령은 문서 생성, 추출한 예제의 검사, 로컬 미리보기를 차례로 실행한다.

```powershell
.\preview.ps1
```

브라우저에서 <http://127.0.0.1:8000/>을 열어 확인하라.
종료할 때는 실행한 터미널에서 `Ctrl+C`를 누른다.
실행 정책으로 스크립트를 사용할 수 없으면 아래 두 명령을 각각 실행하라.

```powershell
lake exe textbook
lake exe verso-serve --port 8000 --strict-port
```

수정한 뒤에는 다른 터미널에서 `lake exe textbook`을 실행하고 브라우저를 새로 고친다.
현재 미리보기는 파일 변경을 자동으로 빌드하지 않는다.

## 연습문제 풀이

Lean 4 확장이 설치된 VS Code에서 이 프로젝트 폴더를 열고
`Exercises/` 안에서 풀려는 절의 파일을 선택하라.
절별 연습문제 원본은 아래 파일에 모았다. 원본을 `Exercises/`의 같은 이름으로 복사하여 풀거나 해당 절의 초기화 명령을 사용하라.
기존 풀이 파일은 구성이 바뀌어도 덮어쓰지 않는다. 각 원본의 첫 줄에서 해당 절을 import하므로 본문의 정의와 정리를 사용할 수 있다.

| 내용 | 연습문제 원본 |
|---|---|
| Lean의 기본 문법 | [Introduction.lean](ExerciseTemplates/Introduction.lean) |
| 증명의 구성과 사용 | [Proofs.lean](ExerciseTemplates/Proofs.lean) |
| 집합의 구성 | [Sets.lean](ExerciseTemplates/Sets.lean) |
| 함수 | [Functions.lean](ExerciseTemplates/Functions.lean) |
| 자연수와 정수 | [Preliminaries.lean](ExerciseTemplates/Preliminaries.lean) |
| 동치관계와 몫집합 | [Relations.lean](ExerciseTemplates/Relations.lean) |
| 집합의 크기와 유한성 | [FiniteCardinality.lean](ExerciseTemplates/FiniteCardinality.lean) |
| 무한집합의 크기와 보조정리 | [InfiniteCardinality.lean](ExerciseTemplates/InfiniteCardinality.lean) |
| 이항연산 | [Operations.lean](ExerciseTemplates/Operations.lean) |
| 군의 정의와 기본 성질 | [GroupBasics.lean](ExerciseTemplates/GroupBasics.lean) |
| 역원·거듭제곱·군의 곱·순열군 | [GroupExamples.lean](ExerciseTemplates/GroupExamples.lean) |
| 유한군과 위수 | [GroupOrder.lean](ExerciseTemplates/GroupOrder.lean) |

각 `sorry`를 자신의 증명으로 바꾸어 완성하라.
증명 안에 커서를 두면 Lean Infoview에 현재의 가정과 목표가 표시된다.
전술을 한 줄씩 작성하면서 목표가 어떻게 바뀌는지 확인하라.
`sorry`가 남아 있으면 미완성 증명이라는 경고가 표시되며
증명을 완성하면 해당 경고가 사라진다.

존재명제의 증명에는 `exists`를 사용한다.
집합 `S`의 원소 타입은 `Elem S`로 명시하며, 함수의 타입은 `Elem S → Elem T`, 집합의 기수는 `cardinal (Elem S)`로 쓴다.
부분타입의 원소는 `{ val := 값, property := 증명 }`으로,
`Fin n`의 원소는 `{ val := 값, isLt := 증명 }`으로 구성하여 두 역할을 구분한다.
`hR : IsEquivalence R`에서 세 조건은 `hR.refl a`, `hR.symm hab`, `hR.trans hab hbc`로 사용할 수 있다.
`hf : Bijective f`에서는 `hf.injective`와 `hf.surjective`로 두 조건을 사용할 수 있다.

### 전술의 공통 규약

규칙의 전제 자리와 결론을 Lean 타입으로 분석한다.
독립된 두 자리 `[P, Q]`와 묶인 자리 하나 `[P ∧ Q]`는 다르게 유지한다.
이 목록은 명제의 논리 연산자가 아니라 전술이 다루는 항목의 구조이다.
연결의 실제 증명은 Lean 커널이 검사한다.

| 명령 | 목표 | 가정 |
|---|---|---|
| `ext` | 전체 등식 → 비교 의무 | 비교 증거 → 전체 등식 |
| `indisc` | 비교 의무 → 전체 등식 | 전체 등식 → 비교 증거 |
| `apply r` | 결론 → 필요한 전제 | 전제의 증명 → 적용 결과 |
| `constructor` | 구성할 증명 → 각 인수의 증명 | 여러 인수의 증명 → 구성한 증명 |
| `unpack` | 독립적인 두 목표 → 곱 구조의 목표 | 곱 구조 하나 → 각 성분 |
| `rw`, `expand` | 표현 변환 | 같은 표현 변환 |

기본 `ext`, `indisc`, `expand`는 한 단계이며 `!`형은 반복형이다.
교재의 `ext` 기본 깊이는 표준 Lean과 다르며 `open Ample`에서 활성화된다.
기존 `indiscern`과 짧은 `suffices`는 개인 풀이 호환을 위해 남겨 두되 본문에서 가르치지 않는다.

| 선택과 명명 | 의미 |
|---|---|
| `at h` | 사용할 기존 가정 |
| `goals first second` | 사용할 기존 목표 |
| `with first second` | 독립된 두 결과의 이름 |
| `with ⟨first, second⟩` | 결과 하나의 내부 분해 |

`with`의 이름은 가정에서 증명 이름이고 목표에서 `case` 이름이다.
묶인 결과를 독립된 여러 이름으로 명명하면 실패한다.
`ext`·`indisc`의 목표 결합은 같은 문맥의 독립적인 명제 목표에 적용하며 선택하지 않은 목표를 보존한다.
`unpack goals`는 같은 조건 아래에서 자료형의 원소를 요구하는 목표도 곱타입으로 묶을 수 있다.
여러 등식은 지정한 순서로 오른쪽에 중첩된 순서쌍으로 묶는다.
문맥이 다르거나 목표의 타입에 미해결 변수가 있으면 실패한다.
목표를 합치는 연결은 새 등식과 등록한 비교 원리만 사용하며 주변 가정으로 우회하지 않는다.

```lean
ext with first second
indisc goals first second with pair
```

`ext at h1 h2 with whole`는 두 비교 증거로 전체 등식을 얻는다.
결과를 추론하기 어려우면 `: 원하는 등식`을 적는다.
대표원으로 만든 몫의 등식은 동치류인 집합의 등식에 근거한 동치형 정리로 연결한다.
`ample_compare`에 등록한 정리를 `ext`와 `indisc`이 양방향으로 사용한다.
임의의 몫 원소에서 대표원을 자동으로 선택하지 않으며 일반 함수의 단사성도 추론하지 않는다.

`apply r at h`는 정리에서 `h`가 들어갈 자리를 찾고 실제 적용 결과를 가정에 기록한다.
여러 인수는 `apply r at hP hQ with hR`로 순서대로 공급한다.
아직 받지 않은 뒤쪽 인수는 함수의 인수로 유지한다.
여러 전제의 증명은 나란히 공급하거나 `apply (r hP) at hQ`처럼 일부를 먼저 적용한다.
논리곱이나 존재명제인 결과는 `with ⟨…⟩`로 요청했을 때 분해한다.
`apply r with first second`와 `constructor with first second`도 같은 명명 처리를 사용한다.
규칙 적용이나 패턴 검사가 실패하면 목표와 가정을 복원한다.

`constructor at hp hq with h`는 생성자에 두 증명을 공급하여 `h`를 만든다.
결과는 현재 목표의 구조에 맞추어 찾고, 필요하면 `: 결과 타입`으로 지정한다.
`unpack h with ⟨hp, hq⟩`는 생성자가 하나인 곱 구조를 한 층만 분해한다.
`unpack`의 성분 이름은 묶음 하나를 나타내는 꺾쇠 패턴으로 적으며 중첩 패턴은 받지 않는다.
`cases h`는 생성자에 따른 경우 구분, `rcases h`는 패턴에 따른 곱 분해와 경우 구분으로 가르친다.
`unpack goals first second with combined`는 같은 문맥의 두 독립적인 목표를
논리곱 또는 곱타입의 목표로 묶는다. `rcases goals`는 중첩된 곱에도 적용한다.
각 원래 목표의 증명을 새 목표에서 얻는 추론을 실제로 구성하며,
분기하는 합 타입이나 미해결 증인에 의존하는 목표는 곱의 필드처럼 묶지 않는다.
기존 `cases`·`rcases`의 표기와 명시적인 `at` 별칭도 유지한다.

논리합의 도입은 `left at hP`·`right at hQ`, 존재명제의 도입은 `exists a at ha`로 사용할 수 있다.
현재 목표 또는 `: 결과 타입`으로 결과를 정하며,
논리합의 미정인 다른 명제는 후속 추론에서 정해지거나 별도 `alternative` 목표로 남는다.
중첩된 논리곱은 `and_intros at hP hQ hR`로 구성한다.
`cases goal G`는 G의 증명과 각 생성자에 대한 함의를 실제 증명 의무로 생성한다.
`cases at source handler1 handler2`는 그 증명들로 결론을 만들며,
경우의 함수 타입에는 생성자의 인수와 그 의존성이 반영된다.
`intro at h`, `by_cases at hPos hNeg`, `by_contra at counter`,
`induction at zero step`, `wlog at restricted reduction`도 동일한 원리의 가정 쪽 용법이다.
가정 쪽 귀납법은 자연수, 일반화한 wlog는 동일한 전칭 인수를 받는 두 증명을 지원한다.
인덱스가 있는 자료형의 일반 case eliminator는 `apply`로 직접 지정한다.
`apply goal G`는 아직 증명하지 않은 명제나 함수 타입 G 자체를 증명 의무로 남기고 적용한다.
결론에 필요한 인수들도 별도의 목표로 요구하므로 새 규칙이 참이라고 가정하지 않는다.

공통 실행부는 규칙의 실제 Π 타입과 생성자의 인수를 검사하고,
분기의 지역 변수를 전칭 인수로 닫은 뒤 각 handler의 타입을 확인한다.
구조체의 `unpack`은 사영 함수를 사용하고 데이터 성분은 지역 정의로 보존한다.
증명 규칙의 도입·제거, 범위와 이름을 다루는 명령, 재작성, 목표를 해결하는 계산을 구분한다.
`exact`, `decide`, `arith` 등으로 새 사실을 만드는 공통 구문은 `have h : G := by ...`이다.
모든 계산 명령에 이름만 다른 가정 변환을 추가하지 않는다.

본문에서는 정의를 드러내는 `expand`, 주어진 등식에 따른 `rw`,
도입 뒤의 분야별 계산 전술을 사용한다. `simp`도 간단한 식을 정리할 때 사용하며,
정수 계산에서 `Int.zero_mul`, `Int.add_zero`, `Int.zero_add` 같은 등록 정리와 함께 소개한다.
`suffices h : G by ...`는 연결 증명을 명시하며 자동화의 선택도 그 증명에 적는다.
`let`과 `have`는 증명 안의 정의와 보조정리로 함께 설명한다.

`wlog`는 [mathlib 구현](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/WLOG.lean)을 바탕으로 옮겼다.
일반화할 변수에 의존하는 가정도 포함하며 환원 목표와 제한한 경우의 목표를 만든다.
Mathlib 전체를 의존성으로 추가하지 않았으며 원본의 Apache 2.0 저작권 표시를 보존한다.
Mathlib의 `wlog!` 부정 전개 변형은 추가하지 않는다.
필요한 표현 정리는 교재의 고전논리 범위와 자동 정리 규칙을 사용한다.

자동 표현 정리는 풀이 파일 맨 위에 `import AlgebraBook.Tactic.Auto`를 추가하고
`open scoped Ample.Auto`를 한 번 적으면 활성화된다.
증명 시작과 전술의 각 단계 전후에 익명 술어의 원소 조건, 지역 함수의 계산과 부등식의 부정을 정리한다.
일반적인 `x ∈ S`는 유지하며 이름 붙인 집합은 `expand`, `dsimp` 등으로 명시적으로 펼친다.
직접 만든 원소의 등식은 유지하고 값의 등식을 추가한다.
`open scoped Classical`이나 증명 안의 `classical`로 고전논리를 활성화하면
목표와 가정의 이중 부정도 제거한다.
`by_cases`·`by_contra` 이후에는 해당 목표와 그 하위 목표에서 같은 정리를 수행한다.
새 연습문제 원본에는 이 설정이 포함되어 있다.
기존 `Exercises/` 파일의 설정과 개인 풀이는 그대로 보존한다.

정의의 이름을 적지 않고 원소 조건이나 함수값을 펼치려면
`open Ample` 아래에서 `expand at h`를 사용할 수 있다.
이 전술은 필요한 정의를 찾아 `dsimp`의 계산으로 식을 정리한다.
교재와 현재 풀이 파일의 정의를 바깥에서 한 층만 펼치며
새로 나타난 정의는 다음 `expand`까지 남겨 둔다.
인수 대입과 지역 정의, 순서쌍의 성분, 직접 만든 원소의 값과 패턴 매칭은 계산하고
논리곱이나 부등식을 정리로 단순화하지 않는다.
`expand`는 목표를, `expand at *`는 목표와 모든 가정을 펼친다.

자연수와 정수 이후의 풀이에서는 `open Ample`로 산술 전술 `arith`와 `suffices`도 사용할 수 있다.
분야별 자동화는 정의와 기본 성질을 직접 배우고 증명한 뒤 도입하며,
`arith`의 첫 사용 예는 자연수와 정수의 마지막 절에 둔다.
`arith`는 선형 산술, 다항식 등식과 자연수·정수의 몫·나머지 계산을 처리한다.
몫과 나머지를 함께 비교하는 규칙, 나머지의 덧셈·곱셈·정수 뺄셈과 나누어떨어짐도 지원한다.
분자가 음이 아닌 몫의 상한, 곱의 하한, 양수로 곱한 부등식의 소거와 몫의 단조성도 사용한다.
나눗셈과 곱셈의 관계에는 필요한 부호·영이 아닌 조건을 확인하며
이미 등장한 곱과 몫에서 얻는 경계를 가정의 추론에도 연결한다.
`Fin`의 경계를 함께 사용하며 목표에 맞는 정리를 선택한 뒤 그 전제도 산술 계산으로 확인한다.
가정에서의 논리·등식 추론도 수행하지만 다른 구조의 연산 법칙을 산술 규칙에 포함하지 않는다.
내부 추론에는 현재 가정과 교재의 산술 규칙 모음만 사용하며 일반 `grind` 규칙은 가져오지 않는다.
본문에서는 `suffices h : G by ...`로 새 조건 `G`와 원래 목표의 연결을 명시한다.
개인 풀이에 쓰던 짧은 `suffices G`도 유지하며 산술로 연결을 찾지 못하면 실패한다.
전술 사용법은 부록의 “자동 표현 정리”, “산술식의 계산”과 “새 목표의 지정”에 정리했다.

군의 기본 계산을 직접 다룬 뒤 2.7에서 `group_calc G`를 소개한다.
`AlgebraBook.Tactic.Group`와 `open Ample`로 사용할 수 있으며 군 구조 `G`를 명시한다.
곱의 결합법칙, 항등원·역원과 거듭제곱 법칙은 `ample_group_rules`에 별도로 등록한다.
군의 식을 정리하면서 생기는 자연수·정수 지수의 계산에는 `arith`를 사용하며,
`arith`의 규칙에는 군의 법칙을 추가하지 않는다.
본문에서는 `suffices h : G by ...`로 연결 증명을 적고 군 계산이 필요한 곳에서 `group_calc`를 사용한다.
개인 풀이용 짧은 `suffices G`는 기존과 같이 산술로 연결을 증명한다.

집합의 크기 연습문제 뒤에는 별도의 전술 `card`를 소개한다.
`AlgebraBook.Cardinality`와 `open Ample`로 사용할 수 있으며
현재 가정과 `ample_card_rules`에 등록한 크기 관계, 원소 수의 유일성, 유한성·무한성의 전달 정리를 연결한다.
1.7에서는 기수의 등식과 유한성·무한성의 기본 정리를 사용한다.
1.8을 가져오면 부등식의 반사성·추이성과 칸토어 정리도 연결한다.
주어진 등식과 부등식을 먼저 연결한 뒤 등록한 정리를 적용하며 새로운 중간 기수를 임의로 정하여 탐색하지 않는다.
새로운 전단사의 구성과 아직 다루지 않은 기수 산술은 직접 증명한다.
`arith`의 산술 규칙에 기수 정리를 추가하지 않는다.

기수의 등식에서 `ext`를 쓰면 왼쪽 타입에서 오른쪽 타입으로 가는 전단사의 존재가 목표가 된다.
`cardinal A = n`을 번호에서 원소로 가는 함수로 증명하려면 `symm`으로 양변을 바꾼 뒤 `ext`를 쓴다.
가정 `h : cardinal A = n`에서 번호를 붙이는 함수를 꺼낼 때는
`rcases (cardinal_eq_iff (Fin n) A).mp h.symm with ⟨f, hf⟩`로 쓴다.
가산무한성의 가정에서는 같은 방법으로 `cardinal_eq_iff Nat A`를 사용한다.
원소 수의 등식은 `rw`로 옮기고 유한성과 무한성은 `isFinite_transport`, `isInfinite_transport`로 옮길 수 있다.
기존 가정 `hAB : SameCardinality A B`는 `(cardinal_eq_iff A B).mpr hAB`로 등식으로 바꾸어 사용할 수 있다.
새 연습문제 원본은 이 구성에 맞추었으며 기존 `Exercises/` 파일은 보존한다.

역함수의 값, 몫 원소의 대표원, 유한집합의 원소 수와 목록의 확장은
`Classical.choose`로 선택하고 그 조건은 `Classical.choose_spec`으로 증명한다.
교재는 선택한 원소와 그 원소에 대한 증명을 구별하여 두 표현이 필요한 이유를 설명하며,
선택공리에 대한 의존성은 짧게 밝힌다.
역함수, 대표원, 원소 수와 목록의 확장은 각각
`inverseMapData`, `quotientReprData`, `cardinalityData`, `nextListingData`에
값과 성질의 증명을 부분타입으로 함께 담는다.
각 값의 정의는 `.val`을 꺼내고 성질의 정리는 `.property`를 꺼내는 세 단계로 구성한다.
역함수 절은 원상 원소의 존재와 유일성에서 출발하여
원소의 선택, 역함수의 구성과 존재, 유일성, 성질의 순서로 진행한다.
몫집합 위의 함수는 `quotientLiftData`에서 함수와 모든 대표원에 대한 계산 규칙을 함께 구성한다.
`quotientLift`와 `quotientLift_classOf`는 이 둘을 꺼내 사용하며,
`quotientLift_unique`는 같은 규칙을 만족하는 두 함수가 같음을 보인다.

터미널에서도 다음 명령으로 파일을 검사할 수 있다.

```powershell
lake env lean Exercises/Cardinality.lean
```

위 명령의 파일 경로를 바꾸면 다른 절의 풀이도 검사할 수 있다.
풀이 파일은 문서를 다시 생성해도 유지되며
문서 생성 과정에서 다시 쓰는 `_out/example-code/`의 파일과 구별한다.

연습문제 원본은 `ExerciseTemplates/`에 보관하며 풀이를 작성할 때는 `Exercises/`의 파일을 사용한다.
초기화하기 전에 작성한 풀이 파일을 저장하라.
`reset-exercises.bat`를 더블클릭하면 전체 풀이 파일을 원본으로 초기화한다.
초기화할 파일의 현재 내용은 먼저 `exercise-backups/날짜-시간-식별자/`에 백업한다.

한 절만 초기화하려면 프로젝트 폴더의 터미널에서 절의 파일 이름을 지정하라.

```powershell
.\reset-exercises.bat Cardinality
```

PowerShell에서는 여러 절을 함께 지정할 수도 있다.
인수를 생략하거나 `-Section All`로 실행하면 전체를 초기화한다.

```powershell
.\reset-exercises.ps1 -Section Proofs, Sets
```

백업에서 풀이를 되돌리려면 해당 백업 폴더의 `.lean` 파일을 `Exercises/`로 복사하라.


## 자동화의 추론 확인과 검증

필요한 선언 앞에 `set_option trace.Ample.arith true in`을 적으면 성공한 산술 증명의 등록 정리와 조건, 사용한 가정을 확인할 수 있다.
기수와 군 계산에는 각각 `trace.Ample.card`, `trace.Ample.group`를 사용한다.
완성된 증명에 들어 있는 정리 적용만 보고하며 계산 엔진 내부의 모든 추론을 설명하지는 않는다.

본문에서 처음 익힐 전술 용법과 여러 목표를 조립하는 확장 용법은 전술 부록에서 구분한다.
대표적인 실패에는 수정 예제를 함께 제공한다.
검증 명령과 Lean 버전 변경 시 확인할 항목은 [검증 절차](planning/Verification.md)에 정리했다.

## 웹에서 증명 따라가기와 코드 실행

`preview.bat`로 연 교재에서는 코드에 포인터를 놓으면 `단계`, `편집`, `복사` 메뉴가 나타난다.
`단계`로 가정과 목표의 변화를 따라가고, `편집`에서 코드를 수정하면 자동으로 Lean이 실행된다.
가정과 목표는 코드 아래에 표시하며 `Ctrl+Enter`로 즉시 실행할 수도 있다.
힌트와 입문 연습문제의 풀이는 제목을 눌러 펼쳐 본다.

기존 미리보기 서버를 켜 둔 경우에는 `interactive-preview.bat`를 실행하여
`http://127.0.0.1:8001/`에서 사용할 수 있다.
설치 조건, 코드 저장 방식과 새 풀이를 추가하는 방법은 [상호작용 미리보기](web/README.md)에 정리했다.

## PDF 출력

Windows에서는 `export-pdf.bat`를 더블클릭하면 전체 교재를 한 PDF로 만든다.
본문의 Lean 코드와 연습문제를 모두 포함하며, 목차와 문서 안의 링크도 함께 넣는다.
결과 파일은 `output/pdf/lean-algebra-ko.pdf`에 저장된다.
미리보기 서버가 켜져 있으면 <http://127.0.0.1:8000/lean-algebra-ko.pdf>에서도 열 수 있다.

PDF 출력에는 TeX Live의 `LuaLaTeX`, `latexmk`, `luatexko`가 필요하다.
현재 작업 환경에서는 TeX Live 2026을 사용한다.
본문은 Pretendard, 코드는 Cascadia Code, 수학 기호는 Noto Sans Math를 사용한다.
별도의 글꼴 설치나 Python 실행은 필요하지 않으며, 코드 블록 끝의 빈 줄은 출력 과정에서 제거한다.
새로 고친 내용을 PDF에 반영하려면 `export-pdf.bat`를 다시 실행하라.
일반 문서 생성에서는 PDF를 만들지 않으며, PDF 출력은 명시적으로 요청하거나 출력 파일을 실행할 때 수행한다.

PowerShell에서는 다음과 같이 실행할 수도 있다.

```powershell
.\export-pdf.ps1
```

이 스크립트는 Verso의 LaTeX 출력과 예제 코드 검사를 수행한 뒤,
한국어 조판 설정을 적용하고 목차와 참조가 맞춰질 때까지 PDF를 생성한다.

## 파일 구성

| 파일 | 역할 |
|---|---|
| `AlgebraBook.lean` | 교재 첫 페이지와 절의 구성 |
| `AlgebraBook/Foundations.lean` | 군 이전의 내용을 하나로 묶은 준비 장 |
| `AlgebraBook/Introduction.lean` | 함수, 명제와 술어를 소개하는 Lean 초반 튜토리얼 |
| `AlgebraBook/Proofs.lean` | 함의와 전칭명제의 증명 사용을 단계별로 설명하는 절 |
| `AlgebraBook/Sets.lean` | 집합의 직접 정의, 기본 성질의 증명과 연습문제 |
| `AlgebraBook/Functions.lean` | 정의역과 공역, 상과 역상, 단사·전사·전단사, 부분타입, 합성함수와 역함수 |
| `AlgebraBook/Numbers.lean` | 1.5 귀납법, 정수 계산, 약수와 합동, 산술 자동화 |
| `AlgebraBook/Relations.lean` | 1.6 동치관계, 동치류와 몫타입 |
| `AlgebraBook/FiniteCardinality.lean` | 1.7 기수, 유한성, 원소 수의 유일성과 자연수의 무한성 |
| `AlgebraBook/InfiniteCardinality.lean` | 1.8 기수 비교, 가산성, 멱집합과 칸토어 정리 |
| `AlgebraBook/Preliminaries.lean` | 자연수·정수와 동치관계를 함께 가져오는 기존 풀이용 진입점 |
| `AlgebraBook/Cardinality.lean` | 유한집합과 무한집합의 크기를 함께 가져오는 진입점 |
| `Exercises/` | 전체 교재의 연습문제를 직접 풀기 위한 절별 Lean 파일 |
| `ExerciseTemplates/` | 풀이를 초기화할 때 사용하는 연습문제 원본 |
| `reset-exercises.bat`, `reset-exercises.ps1` | 풀이 백업과 전체 또는 개별 절 초기화 |
| `AlgebraBook/Groups.lean` | 2장의 이항연산·군의 정의·계산·구체적인 예·자동화를 묶는 구성 |
| `AlgebraBook/Operations.lean` | 2.1 이항연산: 결합법칙과 교환법칙, 항등원과 역원, 연습문제 |
| `AlgebraBook/GroupExamples.lean` | 2장의 정의와 정리를 풀이 파일에서 함께 가져오는 모듈 |
| `AlgebraBook/Groups/` | 2.2~2.8의 본문과 완성된 증명, 연습문제 |
| `AlgebraBook/Groups/Definition.lean` | 2.2 군의 정의, 정수 덧셈군과 두 원소 군, 유일성과 소거법칙 |
| `AlgebraBook/Groups/Order.lean` | 2.8 유한군과 위수, 원소 수의 계산 |
| `AlgebraBook/GroupBasics.lean` | 군의 기본 성질과 위수를 함께 가져오는 기존 풀이용 진입점 |
| `AlgebraBook/Tactics.lean` | 기본 전술의 설명과 실행 가능한 예제 |
| `../Ample/Ample/Tactic/Auto.lean` | 증명 시작과 각 단계 전후의 자동 표현 정리 |
| `../Ample/Ample/Tactic/Normalize.lean`, `Rules.lean` | 자동 표현 정리의 구현과 규칙 모음 |
| `../Ample/Ample/Tactic/Indisc.lean` | 등식과 비교 조건의 연결, 가정에서의 외연성, 재귀 비교 |
| `../Ample/Ample/Tactic/Rule.lean` | 항목 구조, 명명 패턴, 목표 선택, 전방 정리 적용 |
| `../Ample/Ample/Tactic/Wlog.lean` | mathlib 기반 경우 환원 |
| `../Ample/Ample/Tactic/Ext.lean` | 기본 `ext`와 대표원이 주어진 몫 원소의 등식 비교 |
| `../Ample/Ample/Tactic/Comparison.lean` | 등록한 동치형 정리로 등식과 비교 조건을 연결 |
| `../Ample/Ample/Tactic/Arithmetic.lean` | 교재의 `arith`, `suffices` |
| `../Ample/Ample/Tactic/ArithmeticRules.lean` | 자연수·정수의 산술 규칙 모음 |
| `../Ample/Ample/Tactic/Trace.lean` | 성공한 자동화의 등록 정리·조건·가정 추적 |
| `../Ample/Ample/Tactic/ArithmeticSearch.lean` | 목표에 맞는 산술 정리의 선택과 부목표 탐색 |
| `../Ample/Ample/Tactic/Cardinality.lean` | 등록한 크기 관계와 유한성·무한성 정리를 연결하는 `card` |
| `../Ample/Ample/Tactic/Unfold.lean` | 정의의 선택과 `dsimp` 계산을 수행하는 `expand` |
| `AlgebraBook/Symbols.lean` | 처음 등장하는 절별 기호 입력 부록 |
| `AlgebraBook/Meta/Lean.lean` | 본문의 코드를 추출하는 Verso 확장 |
| `Main.lean` | 문서 생성 설정과 예제 추출 단계 |
| `STYLE.md` | 한국어 문체와 수학적 설명의 기준 |
| `AGENTS.md` | 이후 작업에서 지킬 프로젝트 지침 |
| `preview.bat`, `preview.ps1` | 교재 생성, 예제 검사와 미리보기 서버 실행 |
| `export-pdf.bat`, `export-pdf.ps1` | 전체 교재를 한 PDF로 출력 |
| `assets/pdf/book-style.tex` | 한국어 PDF의 글꼴과 지면 설정 |
| `verso-serve.toml` | 미리보기 경로와 포트 |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | 버전과 의존 패키지 고정 |

## 본문과 코드 작성

먼저 `STYLE.md`를 읽고 한국어 본문을 작성하라.
본문은 하라체로 쓰며, 평서문은 “이다·한다”, 문제와 지시는 “하라·보이라·얻으라”로 통일한다.
집합의 원소 관계와 연산을 직접 정의하고 `∈`, `⊆`, `∅`, `∩`, `∪`, `Sᶜ`, `S \ T` 표기에 연결한다.
본문과 연습문제의 코드에서도 이 기호를 사용한다.
부분집합 다음에는 동치와 두 방향의 함의를 설명한 뒤 집합의 같음을 다룬다.
`funext`와 `propext`의 필요성을 각각 함수와 명제의 예제로 설명한 뒤 집합에 사용하고,
이중 여집합의 반대 포함 관계를 증명할 때 고전논리의 귀류법을 도입한다.
수학적 논법에 Lean의 `Classical`을 사용하지만, ZFC의 공리를 별도로 구현하는 구성은 아니다.
기호 입력법은 기호 부록과 [Lean VS Code 확장 설명서](https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md)에 안내되어 있다.
코드 블록을 `savedLean`으로 표시하면 해당 코드는 문서에 표시되고 별도 파일로 추출된다.
`lean`으로 표시한 블록은 문서에서 검사하고 표시하지만 추출하지 않는다.

연습문제에는 독자가 채울 `by sorry` 코드 골격을 제공한다.
이 블록은 `savedLean -keep`으로 작성하여 이후 본문의 증명에서 사용할 수 없게 한다.
추출한 코드에도 연습문제가 포함되므로 `declaration uses 'sorry'` 경고가 나타난다.
이는 의도한 빈 증명이며, 명제의 문법 검사와 증명의 완성을 구분해야 한다.
본문의 정리와 완성된 예제 증명에는 `sorry`를 사용하지 않는다.

추출한 예제는 `_out/example-code/AlgebraBook/`에 소스 파일별로 생성된다.
이 파일들은 Verso나 mathlib에 의존하지 않는 일반 Lean 코드이다.
예를 들어 입문 장의 코드는 다음과 같이 검사한다.

```powershell
lake env lean _out/example-code/AlgebraBook/Introduction.lean
```

새 절을 만들 때는 `AlgebraBook/`에 문서 모듈을 추가하고,
`AlgebraBook.lean`에서 import한 뒤 `{include 1 새모듈이름}`으로 포함한다.
제목은 한국어로 쓰되, 각 장과 절의 메타데이터에 영어 `file`과 `tag`를 지정한다.
`file`은 URL 경로를, 문서 전체에서 고유한 `tag`는 `#` 뒤의 위치 표시를 정한다.
예를 들어 집합 장의 포함 관계 절은 `/sets/subsets/#sets-subsets`로 연결된다.

Advanced 내용은 관련 장의 하위 절 또는 subsection에 두고, 제목에 `Advanced`를 붙인다.
Advanced가 선택해서 읽는 내용이라는 안내는 교재 첫머리에 두며, 각 subsection에서 반복하지 않는다.
기본 본문에서는 Advanced 내용의 이해나 풀이를 요구하지 않는다.
이후 Advanced 절에서 앞선 Advanced 내용을 사용할 때는 필요한 선수 지식을 명시한다.

## 참고와 외부 구성 요소

- [Verso 공식 문서](https://verso.lean-lang.org/doc/latest/)
- [Verso 공식 교재 템플릿](https://github.com/leanprover/verso-templates/tree/v4.35.0/textbook)
- 외부 코드의 출처와 라이선스는 `THIRD_PARTY_NOTICES.md`에 기록한다.

교재 본문과 예제는 독립적으로 작성한다. Dummit–Foote는 수학 내용의 참고 자료로 사용한다.
현재 구성은 로컬 작성과 미리보기를 위한 환경이다.

본문과 제목은 Pretendard v1.3.9 가변 글꼴을 사용한다.
코드는 Cascadia Code v2407.24의 정체와 이탤릭 가변 웹폰트를 사용한다.
코드 안의 수학 기호는 Noto Sans Math v3.000으로 표시한다.
기호를 약간 확대하고 수학 글꼴의 자연스러운 폭을 사용하여 포함 기호와 화살표를 선명하게 표시한다.
글꼴 파일은 프로젝트에 포함되어 문서와 함께 제공되므로 독자의 기기에 설치할 필요가 없다.
글꼴 설정은 `Main.lean`의 문서 생성 설정에서 변경한다.

Windows에서 의존 패키지의 DLL 연결 오류를 해결하기 위해
`vendor/MD4Lean`에 출처와 변경 내역을 기록한 호환성 수정을 포함한다.
`lakefile.toml`에서 이 사본을 선택하므로 새 환경에서도 같은 수정이 적용된다.
