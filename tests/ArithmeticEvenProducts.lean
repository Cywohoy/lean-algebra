import AlgebraBook.Preliminaries

open Ample

example : ¬ (∃ n m : Int, Ample.Divides 2 n ∧ Ample.Divides 2 m ∧ n * m = 3) := by
  rintro ⟨n, m, ⟨k, hn⟩, ⟨l, hm⟩, h⟩
  suffices hSuffices : (¬ (2 ∣ n * m)) by arith
  arith

example : ¬ (∃ n m : Int, Ample.Divides 2 n ∧ Ample.Divides 2 m ∧ n * m = 3) := by
  rintro ⟨n, m, ⟨k, hn⟩, ⟨l, hm⟩, h⟩
  rw [hn, hm] at h
  arith
