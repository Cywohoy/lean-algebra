import AlgebraBook.Numbers

open Ample Lean Elab Command

run_cmd do
  for name in [`Ample.Cardinal, `Ample.Relation, `Ample.IsCountablyInfinite, `Ample.Group] do
    if (← getEnv).contains name then
      throwError "The elementary arithmetic route unexpectedly imports {name}."

example (n : Nat) : 2 * n ≠ 5 := by arith

def early_finite_domain : Fin 3 :=
  { val := 2, isLt := by decide }
