#check Nat.add_zero -- ⊢ ∀ (n : Nat), n + 0 = n
-- The type changes based on the input.
-- this function is dependent function.
-- ∀ (n : Nat) is callled dependent type.
#check Nat.add_zero 0 -- Nat.add_zero 0 : 0 + 0 = 0
#check Nat.add_zero 1 -- Nat.add_zero 1 : 1 + 0 = 1

-- ∀ represents dependent type
example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n) -- (n : Nat) → n + 0 = n : Prop

example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil

-- (α : Type) × α is Dependent Pair.
-- Dependent Pair means The type of b depends on a for a good Cartesian product.
example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩
