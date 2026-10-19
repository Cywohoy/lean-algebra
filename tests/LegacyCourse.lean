import AlgebraBook.InfiniteCardinality
import AlgebraBook.Groups.Automation

-- 기존 개인 풀이가 사용하는 이름과 설정을 교재 어댑터에서 확인한다.
open Course
open scoped Course.Auto Classical

#check Course.Set
#check Course.singleton
#check Course.Group

example (n : Int) (h : ¬ n < 0) : 0 ≤ n := by
  guard_hyp h : 0 ≤ n
  exact h

example (S : Set Nat) : S ∩ S = S := by
  ext x
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · exact h

example (n : Nat) : 2 * n ≠ 5 := by arith

example (A B : Type) (h : cardinal A = cardinal B) (hA : IsInfinite A) :
    IsInfinite B := by
  card

example {A : Type} (G : Group A) (a : A) : G.op (G.inv a) a = G.id := by
  group_calc G

example : 1 ∈ Course.singleton 1 := by
  expand

-- 호환 별칭은 기존 이름을 새 선언에 연결하며 선언을 중복해서 만들지 않는다.
run_cmd do
  let env ← Lean.getEnv
  if env.contains `Course.Set then
    throwError "The compatibility layer duplicated a mathematical declaration."
  unless (Lean.getAliases env `Course.Set false).contains `Ample.Set do
    throwError "The legacy set name must resolve to Ample.Set."
