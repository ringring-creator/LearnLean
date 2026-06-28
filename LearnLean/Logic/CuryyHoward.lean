theorem one_add_one_eq_tow : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_tow

example (P Q : Prop) (h: P → Q) (hp : P) : Q := by
  exact h hp

example (P Q : Prop) (hp : P) : Q → P :=
  -- proof is term.
  -- by tacSeq is term
  -- _ means _hp does not use
  fun _hp => hp
