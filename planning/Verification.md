# 교재와 전술의 검증 절차

문서의 설명과 Lean에서 관찰하는 증명 상태를 함께 확인한다. Lean과 Verso는 `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`에서 같은 버전에 맞춘다.

## 본문 수정

`lake exe textbook`으로 웹 문서를 생성하고 `_out/example-code`에 추출한 모든 Lean 파일을 검사한다. `ExerciseTemplates`를 검사하고 기존 `Exercises` 파일을 덮어쓰지 않는다. 본문의 완성된 정의와 증명에 `sorry`가 없는지 확인하며 미완성 문제만 `savedLean -keep`으로 둔다.

## 전술 수정

`tests/RevisionStates.lean`, `RuleStructure.lean`, `ConstructorDual.lean`, `Indiscern.lean`은 목표·가정의 타입과 이름, 목표 결합의 의존성, 실패 뒤 상태 보존을 검사한다. 산술·기수·군 계산은 각 분야의 테스트와 `AutomationTrace.lean`으로 확인한다. 추적 출력은 `AutomationTrace.Tests.py`가 성공한 증명의 정리·조건을 검사한다.

`AutoNormalizeInfoview.Tests.py`는 실제 Lean 서버에서 전술 끝과 다음 줄의 표시를 비교하며 새 문서와 증분 편집을 모두 확인한다. `LearningRoute.lean`과 `FiniteLearningRoute.lean`은 군의 기본 계산에 기수 이론이 필요하지 않고 유한군의 위수에 무한집합 절이 필요하지 않음을 검사한다.

## Lean 버전 변경

버전 변경 전에 현재 검사를 실행하고 결과를 보관한다. 세 버전 파일을 함께 갱신한 뒤 문서·추출 코드·연습문제 원본과 관련 전술 검사를 실행한다. 특히 메타변수 문맥, 지역 가정, 전술 정보 트리와 편집기 표시의 변화를 확인한다.

`Tactic/Wlog.lean`은 mathlib에서 가져와 수정한 구현이므로 파일의 출처와 저작권 표시, `THIRD_PARTY_NOTICES.md`를 보존한다. 기반 구현을 바꾸면 변경 범위와 출처를 기록하고 기존 일반화·전향 용법 테스트를 실행한다. 외부 최신 구현을 검증 없이 덮어쓰지 않는다.

PDF는 명시적인 생성 요청이 있을 때만 출력한다.
