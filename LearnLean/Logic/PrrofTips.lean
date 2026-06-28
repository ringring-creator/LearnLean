example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p -- ¬¬¬ P
  intro hp -- P ⊢ False

  -- lemma
  have hn2p : ¬¬ P := by
    intro hnp -- ¬ P → False
    exact hnp hp

  exact hn3p hn2p

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp

  have : ¬¬ P := by
    intro hnp
    contradiction -- hp and hnp are contradictory

  guard_hyp this : ¬¬ P -- verify assumption ¬¬ P

  contradiction -- hn3p hn2p are contradictory

example (P : Prop) : ¬¬ (P ∨ ¬P)  := by
  intro h -- ¬ (P ∨ ¬P) ⊢ False
  suffices hyp : ¬ P from by

    have : P ∨ ¬ P := by
      right
      exact hyp

    exact h this

  guard_target =ₛ ¬ P

  intro hq -- P

  have : P ∨ ¬ P := by
    left
    exact hq

  contradiction

example (P : Prop) : (P → True) ↔ True := by
  exact?
  -- Try this:
  -- [apply] exact imp_true_iff P

example (P : Prop) : (True → P) ↔ P := by
  exact?
  -- Try this:
  -- [apply] exact true_imp_iff

example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

example (P : Prop) : ¬ (P ↔ ¬ P) := by
  exact iff_not_self
