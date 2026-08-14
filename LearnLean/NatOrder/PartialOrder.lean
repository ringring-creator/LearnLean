import LearnLean.NatOrder.OrdMonoid

-- a ≤ b → b ≤ a ↔ a = b
variable {n m k : MyNat}

theorem MyNat.lt_trans (h1 : n < m) (h2 : m < k) : n < k := by
  notation_simp at *
  -- h1 : n + 1 ≤ m
  -- h2 : m + 1 ≤ k
  -- ⊢ n + 1 ≤ k
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h1
    _ ≤ m + 1 := by simp
    _ ≤ k := by exact h2
  assumption

theorem MyNat.lt_of_le_of_lt (h1 : n ≤ m) (h2 : m < k) : n < k := by
  notation_simp at *
  -- h1 : n ≤ m
  -- h2 : m + 1 ≤ k
  -- ⊢ n + 1 ≤ k
  have : n + 1 ≤ k := calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := by exact h2
  assumption

theorem MyNat.lt_of_lt_of_le (h1 : n < m) (h2 : m ≤ k) : n < k := by
  notation_simp at *
  -- h2 : m ≤ k
  -- h1 : n + 1 ≤ m
  -- ⊢ n + 1 ≤ k
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h1
    _ ≤ k := by exact h2
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤  ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at h
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  -- hk : n + 1 + k = n ⊢ False
  have : n + (k + 1) = n := calc
    _ = n + 1 + k := by ac_rfl
    _ = n := by rw [hk]
  simp_all

theorem MyNat.le_antisymm (h1: n ≤ m) (h2: m ≤ n) : n = m := by
  induction h1 with
  | refl => rfl
  | @step m h ih =>
    -- h : n ≤ m
    -- ih : m ≤ n → n = m
    -- h2 : m + 1 ≤ n
    -- ⊢ n = m + 1
    have : n < n := calc
      _ ≤ m := by exact h
      _ < m + 1 := by notation_simp; rfl
      _ ≤ n := by exact h2
    simp at this

example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h with
  | inl hp =>
    exact MyNat.le_of_lt hp
  | inr hq =>
    simp [hq]
