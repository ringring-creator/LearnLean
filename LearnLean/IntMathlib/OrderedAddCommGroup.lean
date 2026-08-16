import LearnLean.IntMathlib.PartialOrder

theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt)
  : a + c ≤ b + c := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h
  use m
  -- hm : a + ↑m = b
  -- ⊢ a + c + ↑m = b + c
  have : a + c + ↑m = b + c := calc
    _ = c + (a + ↑m) := by ac_rfl
    _ = c + b := by rw [hm]
    _ = b + c := by ac_rfl
  assumption

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

example {a : MyInt} (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑k := by
  notation_simp at nneg
  obtain ⟨k, hk⟩ := nneg
  use k
  simp_all
