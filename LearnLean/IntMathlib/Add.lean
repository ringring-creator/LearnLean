import Mathlib
import LearnLean.MyInt.Basic

def PreInt.add (m n : PreInt) : MyInt :=

  match m, n with
  | (m1, m2), (n1, n2) => ⟦(m1 + n1, m2 + n2)⟧

def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  -- ⊢ ∀ (a₁ b₁ a₂ b₂ : PreInt), a₁ ≈ a₂ → b₁ ≈ b₂ → a₁.add b₁ = a₂.add b₂
  intro (m1, m2) (n1, n2) (m'1, m'2) (n'1, n'2) rm rn
  dsimp [PreInt.add]
  -- rm : (m1, m2) ≈ (m'1, m'2)
  -- rn : (n1, n2) ≈ (n'1, n'2)
  -- ⊢ Quotient.mk PreInt.sr (m1 + n1, m2 + n2) = Quotient.mk PreInt.sr (m'1 + n'1, m'2 + n'2)
  apply Quotient.sound -- ⊢ (m1 + n1, m2 + n2) ≈ (m'1 + n'1, m'2 + n'2)
  notation_simp at *
  -- rm : m1 + m'2 = m2 + m'1
  -- rn : n1 + n'2 = n2 + n'1
  -- ⊢ m1 + n1 + (m'2 + n'2) = m2 + n2 + (m'1 + n'1)
  have : m1 + n1 + (m'2 + n'2) = m2 + n2 + (m'1 + n'1) := calc
    _ = (m1 + m'2) + (n1 + n'2) := by ac_rfl
    _ = (m2 + m'1) + (n1 + n'2) := by rw [rm]
    _ = (m2 + m'1) + (n2 + n'1) := by rw [rn]
    _ = m2 + n2 + (m'1 + n'1) := by ac_rfl
  assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x1 x2 y1 y2 : MyNat)
  : ⟦(x1, y1)⟧ + ⟦(x2, y2)⟧ = (⟦(x1 + x2, y1 + y2)⟧ : MyInt) := by rfl

attribute [notation_simp] PreInt.sr PreInt.r

@[notation_simp, simp] theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl

@[simp]
theorem MyInt.add_zero (m : MyInt) : m + 0 = m := by
  refine Quotient.inductionOn m ?_
  -- ∀ (a : PreInt), Quotient.mk PreInt.sr a + 0 = Quotient.mk PreInt.sr a

  intro (a1, a2)
  apply Quot.sound
  notation_simp
  -- a1 a2 : MyNat
  -- ⊢ a1 + 0 + a2 = a2 + 0 + a1

  ac_rfl

@[simp]
theorem MyInt.zero_add (m : MyInt) : 0 + m = m := by
  refine Quotient.inductionOn m ?_
  intro (a1, a2)
  apply Quot.sound
  notation_simp
  ac_rfl

section
  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a1, a2)
    apply Quot.sound
    notation_simp
  )

  example (m : MyInt) : m + 0 = m := by
    fail_if_success unfold_int₁
    sorry
end

section
  set_option hygiene false
  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a1, a2)
    apply Quot.sound
    notation_simp
  )

  example (m : MyInt) : m + 0 = m := by
    unfold_int₁
    ac_rfl
end

macro "unfold_int₁" : tactic => `(tactic| focus
  intro m
  refine Quotient.inductionOn m ?_
  intro (a1, a2)
  apply Quot.sound
  notation_simp
)

example (m : MyInt) : 0 + m = m := by
  revert m -- ⊢ ∀ (m : MyInt), 0 + m = m
  unfold_int₁
  ac_rfl

macro "unfold_int₂" : tactic => `(tactic| focus
  intro m n
  refine Quotient.inductionOn₂ m n ?_
  intro (a1, a2) (b1, b2)
  apply Quot.sound
  notation_simp
)

macro "unfold_int₃" : tactic => `(tactic| focus
  intro m n k
  refine Quotient.inductionOn₃ m n k ?_
  intro (a1, a2) (b1, b2) (c1, c2)
  apply Quot.sound
  notation_simp
)

theorem MyInt.add_assoc (m n k : MyInt) : m + n + k = m + (n + k) := by
  revert m n k
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (m n : MyInt) : m + n = n + m := by
  revert m n
  unfold_int₂
  ac_rfl

instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

def MyInt.sub (m n : MyInt) : MyInt := m + -n

instance : Sub MyInt where
  sub := MyInt.sub

@[notation_simp, simp]
theorem MyInt.sub_def (x y : MyInt) : x -y = x + -y := rfl

theorem MyInt.neg_add_cancel (m : MyInt) : -m + m = 0 := by
  revert m
  unfold_int₁
  ac_rfl

instance : AddCommGroup MyInt where
  add_assoc := MyInt.add_assoc
  add_comm := MyInt.add_comm
  zero_add := MyInt.zero_add
  add_zero := MyInt.add_zero
  neg_add_cancel := MyInt.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

example (a b : MyInt) : (a + b) - b = a := by
  abel

example (a b c : MyInt) : (a - b) - c + b + c = a := by
  abel
