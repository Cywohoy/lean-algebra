# Lean으로 배우는 기초 수학

수학의 정의와 증명을 Lean으로 옮기는 방법을 배우는 한국어 입문서이다.
Lean을 처음 접하는 독자를 위해 값과 함수에서 시작하여 집합, 정수, 동치관계와 집합의 크기까지 다룬다.
설명과 Lean 코드를 Verso 웹 문서로 함께 제공하며, 연습문제는 `sorry`를 채우는 방식으로 풀 수 있다.

**[웹에서 읽기](https://cywohoy.github.io/lean-algebra/)**

이 저장소는 공개되어 있다. `main`은 기존 대수학 교재의 **1장과 부록만으로 구성한 독립된 책**이다.
군론을 포함한 전체 교재와 이후 집필 계획은 [full-book 브랜치](https://github.com/Cywohoy/lean-algebra/tree/full-book)에 보존한다.

## 내용

1.1 Lean의 기본 문법 · 1.2 증명의 구성과 사용 · 1.3 집합의 구성 · 1.4 함수 ·
1.5 자연수와 정수 · 1.6 동치관계와 몫집합 · 1.7 집합의 크기와 유한성 · 1.8 무한집합의 크기

전술 일람과 기호 입력법은 부록에 모았다.
자세한 학습 순서는 [구성 안내](CURRICULUM.md)에 정리했다.

## 설치와 빌드

[Git](https://git-scm.com/)과 [elan](https://github.com/leanprover/elan)을 설치한 뒤 다음 명령을 실행하라.
Lean과 Verso는 v4.35.0, 전술 라이브러리 [Ample](https://github.com/Cywohoy/ample)은 v0.2.0으로 고정되어 있다.
필요한 패키지는 Lake가 받으므로 Ample을 별도로 복제할 필요는 없다.

```sh
git clone https://github.com/Cywohoy/lean-algebra.git
cd lean-algebra
lake exe textbook
```

결과는 `_out/html-multi/`에 생성된다. 본문에 포함된 Lean 코드도 문서를 만들 때 검사한다.
연습문제의 `sorry` 경고는 독자가 채울 빈 증명을 나타낸다.

## 웹에서 읽기

공개 웹 문서는 [GitHub Pages](https://cywohoy.github.io/lean-algebra/)에서 읽을 수 있다.
본문과 검색, 증명 단계의 가정·목표 보기, 코드 복사를 제공한다.
코드를 수정하여 Lean으로 검사하거나 자동완성을 사용하려면 아래의 로컬 미리보기를 실행하라.
`main`에 반영한 내용은 GitHub Actions에서 빌드와 검사를 통과한 뒤 자동으로 배포된다.

Windows에서는 `preview.bat`를 실행하라. 문서 생성과 예제 검사 후
[로컬 미리보기](http://127.0.0.1:8000/)가 열리며, 실행 창을 열어 둔 동안 서버가 돌아간다.
종료할 때는 `Ctrl+C`를 누른다.

다른 환경에서는 Python 3를 설치한 뒤 다음과 같이 실행할 수 있다.
별도의 Python 패키지는 필요하지 않다.

```sh
python web/serve.py --port 8000
```

증명의 전술을 누르면 그 단계의 가정과 목표를 볼 수 있다.
`편집`에서는 코드를 바꾸어 Lean으로 확인할 수 있으며, 입력을 잠시 멈추면 자동으로 검사한다.
사용법은 [상호작용 미리보기](web/README.md)에 정리했다.
본문을 수정한 뒤에는 `lake exe textbook`으로 다시 만들고 서버를 재시작하라.

## 연습문제

VS Code에 Lean 4 확장을 설치하고 이 프로젝트 폴더를 열어라.
`ExerciseTemplates/`에서 원하는 파일을 `Exercises/`로 복사한 뒤 `sorry`를 증명으로 바꾸면 된다.
커서를 증명 안에 두면 Infoview에서 현재 가정과 목표를 확인할 수 있다.

| 절 | 원본 |
|---|---|
| Lean의 기본 문법 | [Introduction.lean](ExerciseTemplates/Introduction.lean) |
| 증명의 구성과 사용 | [Proofs.lean](ExerciseTemplates/Proofs.lean) |
| 집합의 구성 | [Sets.lean](ExerciseTemplates/Sets.lean) |
| 함수 | [Functions.lean](ExerciseTemplates/Functions.lean) |
| 자연수와 정수 | [Preliminaries.lean](ExerciseTemplates/Preliminaries.lean) |
| 동치관계와 몫집합 | [Relations.lean](ExerciseTemplates/Relations.lean) |
| 집합의 크기와 유한성 | [FiniteCardinality.lean](ExerciseTemplates/FiniteCardinality.lean) |
| 무한집합의 크기 | [InfiniteCardinality.lean](ExerciseTemplates/InfiniteCardinality.lean) |

Windows의 `reset-exercises.bat`는 기존 풀이를 `exercise-backups/`에 백업한 뒤 전체 원본을 복사한다.
한 절만 초기화하려면 `reset-exercises.bat Functions`처럼 파일 이름을 지정하라.
`Exercises/`와 백업, 생성 결과는 Git에 포함하지 않는다.

기존 전체 교재에서 풀던 군론 문제는 `full-book` 브랜치의 모듈을 사용한다.
개인 풀이 파일은 브랜치를 바꾸어도 보존되며, 군론 풀이를 계속할 때는 `git switch full-book`으로 전환하라.
전체 교재 브랜치는 형제 폴더 `../Ample`을 사용하므로 그 브랜치의 설치 안내를 따른다.

## PDF

Windows에서 TeX Live 또는 MiKTeX의 `latexmk`, `lualatex`를 설치한 뒤 `export-pdf.bat`를 실행하라.
결과는 `output/pdf/lean-foundations-ko.pdf`에 저장된다.
웹 문서의 일반 빌드에서는 PDF를 만들지 않는다.

## 개발과 검사

한국어 설명과 코드 작성에는 [STYLE.md](STYLE.md)와 [AGENTS.md](AGENTS.md)를 따른다.
주요 문서 모듈은 `AlgebraBook/`에 있으며, `AlgebraBook.lean`에서 본문과 부록을 연결한다.
본문과 연습문제는 `Ample` 이름공간을 사용한다.
이전 개인 풀이의 `Course` 이름은 교재의 호환 모듈에서 연결한다.

```sh
lake exe textbook
python tests/verify_revision.py
python tests/RevisionDocument.Tests.py
python tests/AutomationTrace.Tests.py
```

GitHub Pages용 문서는 `python scripts/prepare_pages.py --download-wasm`으로 `_out/pages/`에 준비한다.
공개 편집기는 브라우저 안에서 Lean 4.35와 Ample을 실행하며 코드를 실행 서버로 보내지 않는다.
처음 `편집`을 누르면 실행 파일을 내려받는다. 자동완성은 현재 로컬 미리보기에서 제공한다.
실행 기능이 없는 읽기 전용 출력은 `python scripts/prepare_pages.py`로 만들 수 있다.
`python tests/Pages.Tests.py`로 저장소 이름이 붙은 URL에서도 링크가 연결되는지 검사할 수 있다.

Ample의 전술과 수학 모듈은 독립된 공개 라이브러리이며, Ample의 빌드에는 이 교재가 필요하지 않다.
수학 코드를 수정한 뒤 개발용 Ample 체크아웃에 반영하려면 다음 명령을 사용하라.

```sh
python scripts/sync_ample.py --ample-root ../Ample
python scripts/sync_ample.py --ample-root ../Ample --check
```

이 브랜치의 동기화 도구는 기초 수학 모듈 8개만 갱신하며 Ample의 군론 모듈에는 손대지 않는다.
Ample의 새 기능이 필요하면 라이브러리에서 릴리스한 뒤 `lakefile.toml`의 버전과 `lake-manifest.json`을 함께 갱신한다.
설치된 의존 패키지 안에서 직접 코드를 수정하지 않는다.

## 외부 구성 요소

문서 생성은 [Verso](https://github.com/leanprover/verso)를 사용한다.
본문은 Pretendard, 코드는 Cascadia Code, 수학 기호는 Noto Sans Math로 표시한다.
글꼴은 저장소에 포함되어 있으며 독자의 기기에 설치할 필요는 없다.
Windows 빌드를 위한 MD4Lean 수정본은 `vendor/MD4Lean`에 보관한다.
외부 코드와 글꼴의 출처·라이선스는 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)에 정리했다.
