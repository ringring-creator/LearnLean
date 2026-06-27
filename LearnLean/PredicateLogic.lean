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

-- `opaque` is a declaration that defines a new constant.
opaque Human : Type

opaque Love : Human → Human → Prop

-- Define a new infix operator using `@[inherit_doc]`.
-- Specify the parsing precedence with `infix:50`.
@[inherit_doc] infix:50 "-love→" => Love

-- There are idols whom everyone loves.
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -love→ idol

-- Everyone has at least one person they like.
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -love→ tgt

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -love→ h

def EveryoneLover: Prop := ∀ h : Human, ∃ lover : Human, lover -love→ h

example : PhilanExists → EveryoneLover := by
  intro h
  obtain ⟨p,h⟩ := h

  dsimp [EveryoneLover]

  intro human
  exists p
  exact h human

example : IdolExists → EveryoneLovesSomeone := by
  intro hidol
  obtain ⟨idol, hidol⟩ := hidol

  dsimp [EveryoneLovesSomeone]

  intro h
  exists idol

  exact hidol h
