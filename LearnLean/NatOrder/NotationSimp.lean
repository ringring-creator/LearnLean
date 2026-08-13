import LearnLean.NatOrder.StrictOrder
import LearnLean.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  attribute [local simp] MyNat.lt_def

  example (m n : MyNat) : m < n := by
    simp_all
    guard_target =ₛ m + 1 ≤ n
    -- Unnecessary simplification rules are also being applied.
    sorry
end

section
open Lean Parser Tactic

syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)
end

attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  notation_simp

  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  notation_simp at *
  assumption

example (m n : MyNat) : m < n := by
  -- `simp` made no progress
  -- simp
