import LearnLean.NatSemiring.Mult

-- Convert it into fully expanded form (the form of a sum of polynomials).

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add]

  -- remain 2 * (m + n)
  guard_target =ₛ m * n + m * 1 + 2 * (m + n) = m * n + 3 * m + 2 * n

  sorry

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add, MyNat.mul_add]

  -- remain 2 * (m + n)
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n

  sorry

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  simp only [MyNat.mul_add]

  -- remain 2 * (m + n)
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n

  sorry

example (m n : MyNat) : m * (n + 1) + (2 + m ) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]

  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m

  sorry

macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib

  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m

  sorry

example (m n : MyNat) : m * (n + 1) + (2 + m ) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]

  -- ac_rfl cannot calculate 2 * m + m = 3 * m
  fail_if_success ac_rfl

  guard_target =ₛ m * n + m + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

example (m n : MyNat) : m * (n + 1) + (2 + m ) * m = m * n + 3 * m + m * m := by
  rw [show 3 = 1 + 2 from rfl]
  rw [show 2 = 1 + 1 from rfl] -- m * (n + 1) + (1 + 1 + m) * m = m * n + (1 + (1 + 1)) * m + m * m
  simp only [MyNat.mul_add, MyNat.add_mul] -- m * n + m * 1 + (1 * m + 1 * m + m * m)
  simp only [MyNat.mul_one, MyNat.one_mul] --  m * n + m + (m + m + m * m) = m * n + (m + (m + m)) + m * m
  ac_rfl

macro "distrib" : tactic => `(tactic| focus
  rw [show 3 = 1 + 2 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat) : m * (n + 1) + (2 + m ) * m = m * n + 3 * m + m * m := by
  distrib

theorem unfoldNatList (x : Nat)
  : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 := rfl

macro "expand_num" : tactic => `(tactic| focus
  simp only [unfoldNatList]
  dsimp only [OfNat.ofNat]
  simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num

  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n

  simp only [MyNat.add_mul]

macro "distrib" : tactic => `(tactic| focus
  expand_num
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat) : (m + 100) * n + n = m * n + 101 * n := by
  distrib

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  -- distrib `simp` made no progress
  sorry

macro "expand_num" : tactic => `(tactic| focus
  try simp only [unfoldNatList]
  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [MyNat.mul_add, MyNat.add_mul,
                 MyNat.mul_zero, MyNat.zero_mul,
                 MyNat.mul_one, MyNat.one_mul]
  try ac_rfl
)

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists n + 4, n + 4
  distrib
