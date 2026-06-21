-- Proposition
#check Prop
#check (1 + 1 = 3)

-- Predicate
#check (fun n => n + 3 = 39)

-- Boolean is Prop
#check True
#check False

-- True is trivial.
example : True := by trivial

-- use hypothesis
example (P : Prop) (h : P) : P := by
  exact h

-- use assumption
example (P : Prop) (h : P) : P := by
  assumption

-- definition of implication
#eval True → True -- true
#eval True → False -- false
#eval False → True -- true
#eval False → False -- true

-- use implication by using apply
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

-- use implication by using exact
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- Implications behave in a right-associative manner.
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

example (P Q : Prop) (hq : Q) : P → Q := by
  intro h
  exact hq

#eval ¬ True -- false
#eval ¬ False -- true

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

-- use contradiction
example (P : Prop) (hnp : ¬ P) (hp:P) : False := by
  contradiction

example (P : Prop) (hnp : ¬ P) (hp:P) : False := by
  apply hnp
  exact hp

example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  intro hq -- hq : Q
  intro hp -- hp : P
  -- P → ¬ Q := P → Q → False
  -- show P → Q by hp, hq
  -- show False
  exact h hp hq

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso -- ⊢ False
  contradiction
