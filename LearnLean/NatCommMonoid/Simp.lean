import LearnLean.NatCommMonoid.TypeClass
import LearnLean.NatCommMonoid.Induction

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by
  rfl

example (n : MyNat) : 0 + (n + 0) = n := by
  fail_if_success simp

  rw [MyNat.add_zero, MyNat.zero_add]


attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at * -- h : m = n ⊢ m = n

  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all

@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    simp [ih]

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    simp? [ih]
