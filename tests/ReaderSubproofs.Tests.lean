import Ample.Tactic
import SubVerso.Highlighting

open Lean Elab Command SubVerso.Highlighting

private partial def readerStates : Highlighted → Array (String × Array (Highlighted.Goal Highlighted))
  | .tactics goals _ _ body => (readerStates body).push (body.toString.trimAscii.toString, goals)
  | .seq items => items.foldl (fun out item => out ++ readerStates item) #[]
  | .span _ body => readerStates body
  | _ => #[]

/-- Check the actual document highlighter, including two nested auxiliary proofs. -/
elab "check_reader_subproof " cmd:command : command => do
  elabCommand cmd
  let trees := (← getInfoState).trees
  let rendered ← liftTermElabM <| highlight cmd #[] trees
  let states := readerStates rendered
  let summary := states.map fun (entry : String × Array (Highlighted.Goal Highlighted)) =>
    (entry.1, entry.2.map fun goal => goal.conclusion.toString)
  for expected in ["exact hP", "exact hpq hp", "exact hq"] do
    unless states.any (fun (text, goals) => text == expected && goals.isEmpty) do
      throwError "Missing completed inner tactic: {expected}\nStates: {repr summary}"
  for expected in ["P", "Q"] do
    unless states.any (fun (text, goals) => text == "by" &&
        goals.any (fun goal => goal.conclusion.toString == expected)) do
      throwError "Missing auxiliary goal: {expected}\nStates: {repr summary}"
  unless states.any (fun (text, goals) => text.startsWith "have hp" &&
      goals.any (fun goal => goal.toString.contains "hp")) do
    throwError "Missing return to enclosing proof\nStates: {repr summary}"

set_option Elab.async false
open Ample
open scoped Ample.Auto

check_reader_subproof theorem nested_reader_example (P Q : Prop)
    (hP : P) (hpq : P → Q) : Q := by
  have hq : Q := by
    have hp : P := by
      exact hP
    exact hpq hp
  exact hq
