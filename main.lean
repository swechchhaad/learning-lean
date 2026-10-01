import Mathlib

#check Nat
#check Nat.add
#check (2 + 3 : Nat)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) : P → Q → P := by
  intro hP
  intro hQ
  exact hP

example (a b : Nat) (h : a = b) : b = a := by
  symm
  exact h

example (n : Nat) : n + 0 = n := by
  simp

-- 1. Prove that P implies P.
example (P : Prop) : P → P := by
  intro hP
  exact hP

-- 2. Prove that P ∧ Q implies Q ∧ P.
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hPQ
  rcases hPQ with ⟨hP, hQ⟩ -- turns hPQ : P ∧ Q into hP: P and hQ: Q
  constructor
  · exact hQ
  · exact hP


-- 3. Prove that if a = b and b = c, then a = c.
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
trans b
exact hab
exact hbc
