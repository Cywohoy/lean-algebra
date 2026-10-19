import AlgebraBook.FiniteCardinality

open Ample Lean Elab Command

run_cmd do
  for name in [`Ample.IsCountablyInfinite, `Ample.powerSet,
      `Ample.Cardinal.le, `Ample.Group] do
    if (← getEnv).contains name then
      throwError "The finite cardinality chapter unexpectedly imports {name}."

example (n : Nat) : IsFinite (Fin n) := by exact fin_isFinite n
