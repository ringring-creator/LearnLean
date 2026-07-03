import LearnLean.NatCommMonoid.TypeClass

example (n : MyNat) : n + 0 = n := by
    rfl

-- example (n : MyNat) : 0 + n = n := by
  -- rfl
-- Tactic `rfl` failed: The left-hand side
--   0 + n
-- is not definitionally equal to the right-hand side
--   n
-- n : MyNat
-- ⊢ 0 + n = n

#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl -- ⊢ 0 + MyNat.zero = MyNat.zero
  | succ n' ih =>
    -- ih : 0 + n' = n'
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    rw [MyNat.add_succ] --  (0 + n').succ = n'.succ
    rw [ih] -- (0 + n').succ = (0 + n').succ

example (n : MyNat) : 1 + n = .succ n := by
  induction n
  case zero => rfl
  case succ n' ih =>
    -- ih: 1 + n' = n'.succ
    -- ⊢ 1 + n'.succ = n'.succ.succ
    rw [MyNat.add_succ]
    rw [ih]
