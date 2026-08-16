import LearnLean.IntMathlib.LinearOrder

variable {a b c : MyInt}

theorem MyInt.lt.dest (h : a < b) : ∃ k : MyNat, a + (↑k + 1) = b := by
  notation_simp at h
  -- a b : MyInt
  -- h : (∃ k, a + ↑k = b) ∧ ¬∃ k, b + ↑k = a
  -- ⊢ ∃ k, a + (↑k + 1) = b
  obtain ⟨⟨k, hk⟩, h⟩ := h
  -- h : ¬∃ k, b + ↑k = a
  -- k : MyNat
  -- hk : a + ↑k = b
  -- ⊢ ∃ k, a + (↑k + 1) = b
  induction k with
  | zero =>
    exfalso
    replace hk : a = b := by simp_all
    have : ∃ k : MyNat, b + ↑k = a := by
      rw [hk]
      exists 0
      simp
    contradiction
  | succ k _ =>
    push_cast at hk
    use k
    assumption

theorem MyInt.le.intro (a : MyInt) (b : MyNat) : a ≤ a + ↑b := by
  exact ⟨b, rfl⟩

theorem MyInt.lt.intro (h : ∃ k : MyNat, a + (k + 1) = b) : a < b := by
  obtain ⟨k, hk⟩ := h
  simp only [lt_def] -- ⊢ a ≤ b ∧ ¬b ≤ a
  constructor

  case left => -- ⊢ a ≤ b
    notation_simp
    use k + 1
    assumption
  case right => -- ⊢ ¬b ≤ a
    notation_simp
    intro ⟨s, hs⟩
    rw [← hs] at hk
    -- hk : a + (↑k + 1) = b
    -- hs : b + ↑s = a
    -- ⊢ a + (↑k + 1) = b
    have : ↑(s + k) + (1 : MyInt) = 0 := calc
      _ = (↑s + ↑k) + (1 : MyInt) := by push_cast; ac_rfl
      _ = (b + ↑s + (↑k + 1)) - b := by abel
      _ = b - b := by rw [hk]
      _ = 0 := by abel

    replace : (0 : MyInt) > 0 := calc
      _ = ↑(s + k) + (1 : MyInt) := by rw [this]
      _ = (1 : MyInt) + ↑(s + k):= by ac_rfl
      _ ≥ (1 : MyInt) := by apply MyInt.le.intro
      _ > (0 : MyInt) := by decide
    order

theorem MyInt.lt_iff_add : a < b ↔ ∃ k : MyNat, a + (k + 1) = b := by
  constructor
  case mp => exact MyInt.lt.dest
  case mpr => exact MyInt.lt.intro

@[push_cast]
theorem MyInt.ofMyNat_mul (m n : MyNat) : ↑(m * n) = (m : MyInt) * (n : MyInt) := by
  dsimp [MyInt.ofMyNat]
  apply Quotient.sound
  notation_simp
  ring

theorem MyInt.mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [MyInt.lt_iff_add] at *
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  -- hc : 0 + (↑c + 1) = a
  -- hd : 0 + (↑d + 1) = b
  -- ⊢ ∃ k, 0 + (↑k + 1) = a * b
  rw [← hc, ← hd] -- ⊢ ∃ k, 0 + (↑k + 1) = (0 + (↑c + 1)) * (0 + (↑d + 1))
  use c * d + c + d
  push_cast
  ring

theorem MyInt.sub_pos : 0 < a - b ↔ b < a := by
  constructor <;> intro h
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    simp at hk
    use k
    rw [hk]
    abel
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    use k
    rw [← hk]
    abel

theorem MyInt.mul_lt_mul_of_pos_left (h : a < b) (pos : 0 < c)
  : c * a < c * b := by
  suffices 0 < c * (b - a) from by
    -- h : a < b
    -- pos : 0 < c
    -- this : 0 < c * (b - a)
    -- ⊢ c * a < c * b
    rw [MyInt.lt_iff_add] at this ⊢
    -- this : ∃ k, 0 + (↑k + 1) = c * (b - a) ⊢ ∃ k, c * a + (↑k + 1) = c * b
    obtain ⟨k, hk⟩ := this
    simp at hk
    use k
    rw [hk]
    simp [MyInt.left_distrib]
  replace h : 0 < b - a := by
    rw [MyInt.sub_pos]
    assumption
  apply MyInt.mul_pos (ha := pos) (hb := h)

theorem MyInt.mul_lt_mul_of_pos_right (h : a < b) (pos : 0 < c)
  : a * c < b * c := by
  rw [MyInt.mul_comm a c, MyInt.mul_comm b c]
  apply MyInt.mul_lt_mul_of_pos_left (h := h) (pos := pos)

instance : IsStrictOrderedRing MyInt where
  zero_le_one := by decide
  exists_pair_ne := by exists 0, 1
  mul_lt_mul_of_pos_left := by
    intro a ha b c hbc
    exact MyInt.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right := by
    intro c hc a b hab
    exact MyInt.mul_lt_mul_of_pos_right hab hc

example : (1 : MyInt) + 5 = 6 := by ring

example (h : a < b) : a + c < b + c := by
  linarith

example (h1 : 2 * a - b = 1) (h2 : a + b = 5) : a = 2 := by
  linarith

theorem MyInt.mul_le_mul_of_nonneg_left (h : a ≤ b) (nneg: 0 ≤ c)
  : c * a ≤ c * b := by
  nlinarith

theorem MyInt.mul_le_mul_of_nonneg_right (h : a ≤ b) (nneg: 0 ≤ c)
  : a * c ≤ b * c := by
  nlinarith

instance : IsOrderedRing MyInt where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact MyInt.mul_le_mul_of_nonneg_left hbc ha
  mul_le_mul_of_nonneg_right := by
    intro c hc a b hab
    exact MyInt.mul_le_mul_of_nonneg_right hab hc

example (h1 : 3 * a - 2 * b = 5) (h2: 6 * a - 5 * b = 11)
  : b = -1 := by nlinarith
