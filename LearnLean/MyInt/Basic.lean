import LearnLean.NatOrder.DecidableOrd

abbrev PreInt := MyNat × MyNat

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m1, m2), (n1, n2) => m1 + n2 = m2 + n1

theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m1, m2)
  dsimp [r] -- ⊢ m1 + m2 = m2 + m1
  ac_rfl

theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  intro (m1, m2) (n1, n2) h
  dsimp [r] at * -- h : m1 + n2 = m2 + n1 ⊢ n1 + m2 = n2 + m1

  have : n1 + m2 = n2 + m1 := calc
    _ = m2 + n1 := by ac_rfl
    _ = m1 + n2 := by rw [← h]
    _ = n2 + m1 := by ac_rfl
  exact this

theorem PreInt.r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro (l1, l2) (m1, m2) (n1, n2) hlm hmn
  dsimp [r] at *
  -- hlm : l1 + m2 = l2 + m1
  -- hmn : m1 + n2 = m2 + n1
  -- ⊢ l1 + n2 = l2 + n1

  have : m1 + (l1 + n2) = m1 + (l2 + n1) := calc
    _ = m1 + n2 + l1 := by ac_rfl
    _ = m2 + n1 + l1 := by rw [hmn]
    _ = l1 + m2 + n1 := by ac_rfl
    _ = l2 + m1 + n1 := by rw [hlm]
    _ = m1 + (l2 + n1) := by ac_rfl
  simp_all

theorem PreInt.r.equiv : Equivalence r :=
  {
    refl := r.refl
    symm := r.symm
    trans := r.trans
  }

@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩

abbrev MyInt := Quotient PreInt.sr

#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  (Quotient.mk _ a)

namespace PreInt
scoped notation "⟦" a "⟧" => Quotient.mk PreInt.sr a
end PreInt
open scoped PreInt

#check (⟦(1, 3)⟧ : MyInt)

def MyInt.ofNat (n : Nat) : MyInt := ⟦(MyNat.ofNat n, 0)⟧

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)

def PreInt.neg : PreInt → MyInt
  | (m, n) => ⟦(n, m)⟧

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  -- ⊢ ∀ (a b : PreInt), a ≈ b → a.neg = b.neg
  intro (a1, a2) (b1, b2) hab

  suffices (a2, a1) ≈ (b2, b1) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption

  notation_simp at *
  simp_all

instance : Neg MyInt where
  neg := MyInt.neg

@[simp]
theorem MyInt.neg_def (x y : MyNat) : - ⟦(x, y)⟧ = (⟦(y, x)⟧ : MyInt) := by
  dsimp [Neg.neg, MyInt.neg,PreInt.neg]
  rfl

#check (-4: MyInt)
#check_failure -4

#check Setoid

variable {α : Type} {r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
  : ∀ {x y : α}, r x y → r y x := by
  -- refl : ∀ (x : α), r x x
  -- h : ∀ (x y z : α), r x y → r y z → r z x
  -- ⊢ {x y : α} → sorry
  intro x y hxy
  have := h x y y
  exact this hxy (refl y)

private theorem Ex.equiv (refl : ∀ x, r x x)
  (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor

  case refl => exact refl

  case symm =>
    intro x y hxy
    have := h x y y
    exact this hxy (refl y)

  case trans =>
    intro x y z hxy hyz
    have lem := h z y x
    exact lem (Ex.symm refl h hyz) (Ex.symm refl h hxy)
