example (P : Prop) : ¬¬ P → P := by
  intro hn2p

  by_cases h : P
  · exact h
  · contradiction

#check Classical.em
#print axioms Classical.em

#check propext
#check Classical.choice
#check Quot.sound
#check Sort

def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

variable {X Y : Type}

noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  intro y

  -- // is called subtype.
  -- A type consisting solely of elements of a certain type that satisfy the predicate `f x = y`.
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨x, hx⟩

  have x := Classical.choice this
  exact x.val

theorem double_negation_of_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬¬ P → P := by
  have h := contra_equiv P True
  rw [show ¬ True ↔ False from by simp] at h
  rw [show True → P ↔ P from by simp] at h

  intro hnnP
  exact h.mp hnnP

#print axioms double_negation_of_contra_equiv
