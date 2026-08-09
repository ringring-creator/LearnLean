import LearnLean.NatOrder.NatCancel

inductive MyNat.le (n : MyNat) : MyNat → Prop
  -- ∀ n, n ≤ n
  | refl : MyNat.le n n
  -- n ≤ m → n ≤ m + 1
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

-- use ≤ as MyNat.le
instance : LE MyNat where
  le := MyNat.le

example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
    guard_target =ₛ P m m
    sorry
  | @step n h ih =>
    guard_hyp ih : P m n
    guard_target =ₛ P m (n + 1)
    sorry

@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
  {motive : (a : MyNat) → n ≤ a → Prop}
  (refl : motive n MyNat.le.refl)
  (step : ∀ {m : MyNat} (a : n ≤ m),
    motive m a → motive (m + 1) (MyNat.le.step a))
  (t : n ≤ b) :
  motive b t :=
  match b, t with
  | _, .refl => refl
  | _, .step a => step a (MyNat.le.recAux refl step a)

-- reflexivity
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

-- transitivity
variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with
  | refl =>
    -- hnm : n ≤ m
    -- ⊢ n ≤ m
    exact hnm
  | @step k hmk ih =>
    -- hnm : n ≤ m
    -- k : MyNat
    -- hmk : m ≤ k
    -- ih : n ≤ k
    -- ⊢ n ≤ k + 1
    exact MyNat.le_step ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  rfl

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤  n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left
