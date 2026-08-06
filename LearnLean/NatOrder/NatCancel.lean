import LearnLean.NatSemiring.Distrib

variable {l m n : MyNat}

theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero =>
    simp_all
  | succ m ih =>
    -- ih : l + m = n + m → l = n
    -- h : l + (m + 1) = n + (m + 1)
    -- ⊢ l = n
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl

    have : l + m = n + m := by
      injection lem

    exact ih this

theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  -- h : m + l = n + l
  apply MyNat.add_right_cancel h

section
  attribute [local simp] MyNat.add_left_cancel

  -- The proof below results in an error.
  -- example : l + m = l + n → m = n := by
    -- simp
end

@[simp ↓] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h -- h : l = n ⊢ l + m = n + m
    rw [h]

@[simp ↓] theorem MyNat.add_left_cancel_iff : l + m = l + n  ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h -- h : l = n ⊢ l + m = n + m
    rw [h]

example : l + m = l + n → m = n := by
  simp

@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor <;> intro h
  case mpr => simp_all
  case mp =>
    have : m + n = m + 0 := by
      rw [h]
      simp
    simp_all

@[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [
    MyNat.add_comm n m,
    MyNat.add_right_eq_self,
  ]

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [show (m = m + n) ↔ (m + n = m) from by exact eq_comm]
  exact add_right_eq_self

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [
    MyNat.add_comm n m,
    MyNat.self_eq_add_right,
  ]
