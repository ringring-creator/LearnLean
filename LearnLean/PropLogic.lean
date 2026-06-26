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

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

-- constructor tactic
example (P Q: Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q: Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  case mp =>
    apply h1
  case mpr =>
    apply h2

example (P Q: Prop) (hp : Q) : (Q → P) ↔ P := by
  constructor
  -- (Q → P) → P
  case mp =>
    intro h -- (Q → P)
    exact h hp
  -- P → (Q → P)
  case mpr =>
    intro hp hq
    exact hp

example (P Q: Prop) (hp : Q) : (Q → P) ↔ P := by
  -- declare `intro h` in the both cases
  constructor <;> intro h
  case mp =>
    exact h hp
  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- rewrite goal by h
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

-- logical product
#eval True ∧ True -- true
#eval True ∧ False --false
#eval False ∧ True --false
#eval False ∧ False --false

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  case left =>
    exact hp
  case right =>
    exact hq

-- logical sum
#eval True ∨ True -- true
#eval True ∨ False -- true
#eval False ∨ True -- true
#eval False ∨ False -- false

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro hpq
  cases hpq with
  | inl hpnot =>
    intro hp
    contradiction
  | inr hq =>
    intro hp
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  -- ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  case mp =>
    intro h -- ¬ (P ∨ Q)
    constructor
    case left => -- P is True
      intro hp -- P
      apply h -- rewrite P ∨ Q
      left
      exact hp
    case right =>
      intro hq
      apply h
      right
      exact hq
  -- ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
  case mpr =>
    intro hpq -- ¬ P ∧ ¬ Q
    intro nothpq -- P ∨ Q → False
    cases nothpq with
    | inl hp =>
      apply hpq.left
      exact hp
    | inr hq =>
      apply hpq.right
      exact hq
