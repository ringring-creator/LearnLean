import LearnLean.NatOrder.OrderDef

-- m < n
def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

-- enable to use a < b representation
instance : LT MyNat where
    lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
    dsimp [(· < ·),MyNat.lt]
    rfl

-- a < b ∨ b ≤ a

@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
    intro h
    -- h : 1 = 0 ⊢ False
    injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
    intro h
    injection h

-- Natural numbers are greater than or equal to 0.
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
    rw [MyNat.le_iff_add] -- ⊢ ∃ k, 0 + k = n
    exists n -- ⊢ 0 + n = n
    simp

-- The only natural number less than or equal to 0 is 0.
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        -- ih : n ≤ 0 → n = 0
        -- h : n + 1 ≤ 0
        -- ⊢ n + 1 = 0
        exfalso
        rw [MyNat.le_iff_add] at h
        -- ih : n ≤ 0 → n = 0
        -- h : ∃ k, n + 1 + k = 0
        -- ⊢ False
        obtain ⟨k, hk⟩ := h
        simp_all

@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
    constructor <;> intro h
    · apply MyNat.zero_of_le_zero h
    · simp [h]

theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
    induction n with
    | zero =>
        simp
    | succ n ih => -- ih : n = 0 ∨ 0 < n ⊢ n + 1 = 0 ∨ 0 < n + 1
        dsimp [(· < ·), MyNat.lt] at *
        -- ih : n = 0 ∨ 0 + 1 ≤ n ⊢ n + 1 = 0 ∨ 0 + 1 ≤ n + 1
        cases ih with
        | inl ih => -- ih : n = 0 ⊢ n + 1 = 0 ∨ 0 + 1 ≤ n + 1
            simp_all
        | inr ih => -- ih : 0 + 1 ≤ n ⊢ n + 1 = 0 ∨ 0 + 1 ≤ n + 1
            simp_all [MyNat.le_step]

-- n ≤ m ↔ n = m ∨ n < m
theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
    intro h
    dsimp [(· < ·), MyNat.lt]
    -- h : n ≤ m ⊢ n = m ∨ n + 1 ≤ m
    rw [MyNat.le_iff_add] at *
    -- h : ∃ k, n + k = m ⊢ n = m ∨ ∃ k, n + 1 + k = m
    obtain ⟨k, hk⟩ := h
    induction k with
    | zero => simp_all
    | succ k _ =>
        have : ∃ k, n + 1 + k = m := by
            exists k
            rw [← hk]
            ac_rfl
        simp_all

theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
    dsimp [(· < ·), MyNat.lt] at h
    have : a ≤ b := calc
        _ ≤ a + 1 := by simp
        _ ≤ b := by assumption
    -- h : a + 1 ≤ b
    -- this : a ≤ b
    -- ⊢ a ≤ b
    assumption

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
    intro h
    cases h with
    | inl h =>
        rw [h]
    | inr h =>
        exact MyNat.le_of_lt h

theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
    constructor
    · apply MyNat.eq_or_lt_of_le
    · apply MyNat.le_of_eq_or_lt

--a < b ∨ b ≤ a
theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
    dsimp [(· < ·), MyNat.lt]
    -- ⊢ a + 1 ≤ b ∨ b ≤ a
    induction a with
    | zero =>
        suffices 1 ≤ b ∨ b ≤ 0 from by
            simp_all
        have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
        dsimp [(· < ·), MyNat.lt] at this
        -- this : b = 0 ∨ 0 + 1 ≤ b ⊢ 1 ≤ b ∨ b ≤ 0
        cases this <;> simp_all
        -- if b = 0 → b ≤ 0
        -- if 0 + 1 ≤ b → 1 ≤ b

    | succ a ih =>
        -- ih : a + 1 ≤ b ∨ b ≤ a ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
        cases ih with
        | inr h =>
            -- h : b ≤ a ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
            right
            -- h : b ≤ a ⊢ b ≤ a + 1
            exact le_step h

        | inl h =>
            -- a + 1 ≤ b ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
            simp [MyNat.le_iff_eq_or_lt] at h
            -- h : a + 1 = b ∨ a + 1 < b ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
            cases h with
            | inl h =>
                -- h : a + 1 = b ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
                right
                simp_all
            | inr h =>
                -- h : a + 1 < b ⊢ a + 1 + 1 ≤ b ∨ b ≤ a + 1
                dsimp [(· < ·), MyNat.lt] at h
                left
                -- h : a + 1 + 1 ≤ b ⊢ a + 1 + 1 ≤ b
                assumption

-- a < b ↔ a ≤ b ∧ ¬ b ≤ a
theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
    cases (MyNat.lt_or_ge b a) with
    | inl h => assumption
    | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
    intro hle
    dsimp [(· < ·),MyNat.lt] at h
    -- h : a + 1 ≤ b
    -- hle : b ≤ a ⊢ False
    rw [MyNat.le_iff_add] at *
    -- h : ∃ k, a + 1 + k = b
    -- hle : ∃ k, b + k = a ⊢ False
    obtain ⟨k, hk⟩ := h
    obtain ⟨l, hl⟩ := hle

    have : a + (k + l + 1) = a := calc
        _ = a + 1 + k + l := by ac_rfl
        _ = b + l := by rw [hk]
        _ = a := by rw [hl]
    simp at this

theorem MyNat.le_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    constructor <;> intro h
    case mp => simp_all [MyNat.not_le_of_lt, MyNat.le_of_lt]
    case mpr => simp_all [MyNat.lt_of_not_le]

-- a ≤ b ∨ b ≤ a
theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
    cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

example (a : MyNat) : a ≠ a + 1 := by
    simp_all

example (n : MyNat) : ¬ n + 1 ≤ n := by
    intro h
    rw [MyNat.le_iff_add] at *
    -- h : ∃ k, n + 1 + k = n ⊢ False
    obtain ⟨k, hk⟩ := h
    have : n + (1 + k) = n := calc
        _ = n + 1 + k := by ac_rfl
        _ = n := by rw [hk]
    simp_all
