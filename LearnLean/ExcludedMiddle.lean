example (P : Prop) : ¬¬ P → P := by
  intro hn2p

  by_cases h : P
  · exact h
  · contradiction
