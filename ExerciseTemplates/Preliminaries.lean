import AlgebraBook.Numbers
import AlgebraBook.Tactic.Auto

/-! 각 sorry를 자신의 증명으로 바꾸어 완성하라. -/

open Ample
open scoped Ample.Auto Classical
namespace Exercises.Preliminaries
variable {A B C : Type} {m n : Nat}
local infix:50 (priority := high) " ∣ " => Divides
local notation:50 a " ≡ " b " [ZMOD " n "]" => Congruent n a b
theorem exercise_one_add_induction
    (n : Nat) :
    1 + n = n + 1 := by
  sorry

theorem exercise_divides_zero (a : Int) : a ∣ 0 := by
  sorry

theorem exercise_congruent_add_right
    (n a b t : Int)
    (h : a ≡ b [ZMOD n]) :
    a + t ≡ b + t [ZMOD n] := by
  sorry

-- 문제 4: 첫 합동과 본문의 23 ≡ 2 [ZMOD 7]을 연결하라.
theorem exercise_congruent_thirty_seven_two :
    37 ≡ 2 [ZMOD 7] := by
  sorry

theorem exercise_congruent_thirty_seven_twenty_three :
    37 ≡ 23 [ZMOD 7] := by
  sorry

-- 문제 5: 짝수의 합
-- (1) 짝수 두 개의 합은 짝수임을 정의로 증명하라.
-- (2) 첫 결과와 double_is_even을 사용하여 a가 짝수이면
-- a+\operatorname{double}(7)도 짝수임을 보이라.
-- 분배법칙은 Nat.mul_add로 사용할 수 있다.
theorem exercise_even_add (a b : Nat)
    (ha : IsEvenNat a)
    (hb : IsEvenNat b) :
    IsEvenNat (a + b) := by
  sorry

theorem exercise_even_add_double (a : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a + double 7) := by
  sorry

-- 문제 6: 짝수의 배수
-- a가 짝수이면 모든 자연수 b에 대하여 ab도 짝수임을 증명하라.
-- 곱셈의 결합법칙 Nat.mul_assoc을 사용할 수 있다.
-- 이 결과로 \operatorname{double}(3)\cdot b가 짝수임을 보이라.
theorem exercise_even_mul (a b : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a * b) := by
  sorry

theorem exercise_double_mul_even (b : Nat) :
    IsEvenNat (double 3 * b) := by
  sorry

-- 문제 7: 서로를 나누는 정수
-- 3\mid-3과 -3\mid3을 각각 증명하라.
-- 이어서 3\ne-3을 확인하여 정수에서는 a\mid b이고 b\mid a여도
-- a=b를 결론지을 수 없음을 보이라.
theorem exercise_divisibility_sign :
    (3 ∣ -3) ∧ ((-3) ∣ 3) := by
  sorry

theorem exercise_three_ne_negative_three :
    (3 : Int) ≠ -3 := by
  sorry

-- 문제 8: 법의 배수와 합동
-- (1) a\equiv b\pmod{nd}이면 a\equiv b\pmod n임을 증명하라.
-- (2) 20\equiv2\pmod6을 직접 증명한 뒤 첫 결과를 사용하여
-- 20\equiv2\pmod3을 보이라.
theorem exercise_congruent_divisor (n d a b : Int)
    (h : a ≡ b [ZMOD n * d]) :
    a ≡ b [ZMOD n] := by
  sorry

theorem exercise_twenty_mod_six : 20 ≡ 2 [ZMOD 6] := by
  sorry

theorem exercise_twenty_mod_three : 20 ≡ 2 [ZMOD 3] := by
  sorry

end Exercises.Preliminaries
