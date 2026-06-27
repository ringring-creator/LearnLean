def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  intro x
  dsimp [P]

example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  exact h 0

def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
  : ∃ x : α, Q x := by
  obtain ⟨y, hy⟩ := h
  exists y
  exact hy.right
