import LearnLean.NatOrder.NotationSimp
import LearnLean.NatOrder.CompatibleTag

variable {a b m n : MyNat}

theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  -- h : ∃ k, n + k = m
  -- l : MyNat
  -- ⊢ ∃ k, n + k = m
  exists k
  rw [← hk] -- hk : n + k = m ⊢ l + n + k = l + (n + k)
  ac_rfl

theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply MyNat.add_le_add_left h l
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := calc
  _ ≤ m + b := by exact add_le_add_left h2 m
  _ ≤ n + b := by exact add_le_add_right h1 b


example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left h

example (hle : n ≤ m) (l : MyNat) : n + l ≤ m + l := by
  apply MyNat.add_le_add_right hle

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

example (hle : n ≤ m) (l : MyNat) : n + l ≤ m + l := by
  apply MyNat.add_le_add_right <;> assumption

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  apply MyNat.add_le_add <;> assumption

syntax "compatible" : tactic

section

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_left <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_right <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (hle : n ≤ m) (l : MyNat) : n + l ≤ m + l := by
    compatible

  example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
    compatible

end

open Lean Elab Tactic in

elab "compatible" : tactic => do
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "theorem of [compatible] has not been assigned"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)

      return ()
    catch _ =>
      pure ()
  throwError "Unable to close the goal."

attribute [compatible] MyNat.add_le_add_left MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (hle : n ≤ m) (l : MyNat) : n + l ≤ m + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat) : k + m < k + n := by
  notation_simp at *  -- h : m + 1 ≤ n ⊢ k + m + 1 ≤ k + n
  have : k + m + 1 ≤ k + n := calc
    _ = k + (m + 1) := by ac_rfl
    _ ≤ k + n := by compatible

  assumption

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat)
  : m + k < n + k := calc
  _ = k + m := by ac_rfl
  _ < k + n := by compatible
  _ = n + k := by ac_rfl

section
variable (m n k : MyNat)

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  -- h : k + m ≤ k + n ⊢ m ≤ n
  rw [MyNat.le_iff_add] at *
  -- h : ∃ k_1, k + m + k_1 = k + n ⊢ ∃ k, m + k = n
  obtain ⟨d, hd⟩ := h
  exists d -- hd : k + m + d = k + n ⊢ MyNat
  have : m + d + k = n + k := calc
    _ = k + m + d := by ac_rfl
    _ = k + n := by rw [hd]
    _ = n + k := by ac_rfl
  simp_all

theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
  rw [MyNat.add_comm m k, MyNat.add_comm n k]
  apply MyNat.le_of_add_le_add_left

@[simp] theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_left
  · intro h
    compatible

@[simp] theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_right
  · intro h
    compatible

end

variable (m1 m2 n1 n2 l1 l2 : MyNat)

example (h1: m1 ≤ m2) (h2: n1 ≤ n2) (h3: l1 ≤ l2) : l1 + m1 + n1 ≤ l2 + n2 + m2 := calc
  _ = l1 + n1 + m1 := by ac_rfl
  _ ≤ l1 + n1 + m2 := by compatible
  _ ≤ l2 + n1 + m2 := by simp_all
  _ ≤ l2 + n2 + m2 := by simp_all
