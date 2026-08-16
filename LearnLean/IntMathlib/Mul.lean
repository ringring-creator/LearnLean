import Mathlib
import LearnLean.IntMathlib.Add
import LearnLean.NatCommMonoid.Induction

instance : Zero MyNat where
  zero := 0

instance : AddCommMonoid MyNat where
  add_assoc := MyNat.add_assoc
  zero_add := MyNat.zero_add
  add_zero := MyNat.add_zero
  add_comm := MyNat.add_comm
  nsmul := nsmulRec

instance: One MyNat where
  one := 1

instance : CommSemiring MyNat where
left_distrib := MyNat.mul_add
right_distrib := MyNat.add_mul
mul_assoc := MyNat.mul_assoc
one_mul := MyNat.one_mul
mul_one := MyNat.mul_one
zero_mul := MyNat.zero_mul
mul_zero := MyNat.mul_zero
mul_comm := MyNat.mul_comm

example (a b c : MyNat) : (a + b) * (a + c) = a * a + (b + c) * a + b * c := by
  ring

-- define multiplication of MyInt
-- (m1 - m2) * (n1 - n2) = m1 * n1 + m2 * n2 - (m1 * n2 + m2 * n1) = (m1 * n1 + m2 * n2, m1 * n2 + m2 * n1)
def PreInt.mul (m n : PreInt) : MyInt :=
  match m, n with
  | (m1, m2), (n1, n2) => ⟦(m1 * n1 + m2 * n2, m1 * n2 + m2 * n1)⟧

def MyInt.mul : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.mul <| by
  -- ⊢ ∀ (a₁ b₁ a₂ b₂ : PreInt), a₁ ≈ a₂ → b₁ ≈ b₂ → a₁.mul b₁ = a₂.mul b₂
  intro (a, b) (c, d) (p, q) (r, s) h1 h2
  dsimp [PreInt.mul]
  apply Quot.sound
  notation_simp at *
  -- h1 : a + q = b + p
  -- h2 : c + s = d + r
  -- ⊢ a * c + b * d + (p * s + q * r) = a * d + b * c + (p * r + q * s)

  generalize hl : a * c + b * d + (p * s + q * r) = lhs
  generalize hr : a * d + b * c + (p * r + q * s) = rhs

  have h3 : lhs + (p * c + q * d + q * c + p * d) = rhs + (p * c + q * d + q * c + p * d) := by
    calc
      lhs + (p * c + q * d + q * c + p * d)
        = a * c + b * d + (p * s + q * r) + (p * c + q * d + q * c + p * d) := by rw [← hl]
      _ = (a + q) * c + (b + p) * d + p * (c + s) + q * (d + r) := by ring
      _ = (b + p) * c + (a + q) * d + p * (d + r) + q * (c + s) := by rw [h1, h2]
      _ = a * d + b * c + (p * r + q * s) + (p * c + q * d + q * c + p * d) := by ring
      _ = rhs + (p * c + q * d + q * c + p * d) := by rw [← hr]

  exact MyNat.add_right_cancel h3

instance : Mul MyInt where
  mul := MyInt.mul

@[notation_simp]
theorem MyNat.toMyNat_one : MyNat.ofNat 1 = 1 := rfl

@[simp]
theorem MyInt.mul_one (m : MyInt) : m * 1 = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.one_mul (m : MyInt) : 1 * m = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.mul_zero (m : MyInt) : m * 0 = 0 := by
  revert m
  unfold_int₁

@[simp]
theorem MyInt.zero_mul (m : MyInt) : 0 * m = 0 := by
  revert m
  unfold_int₁
  ring

theorem MyInt.mul_comm (m n : MyInt) : m * n = n * m := by
  revert m n
  unfold_int₂
  ring

theorem MyInt.mul_assoc (m n k: MyInt) : m * n * k = m * (n * k) := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.left_distrib (m n k : MyInt) : m * (n + k) = m * n + m * k := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.right_distrib (m n k : MyInt) : (m + n) * k = m * k + n * k := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.ofNat_succ (n : Nat) : MyInt.ofNat (n + 1) = MyInt.ofNat n + 1 := by
  apply Quotient.sound
  notation_simp
  simp [MyInt.ofNat, MyNat.ofNat]
  change (MyNat.ofNat n).succ = MyNat.ofNat n + MyNat.succ 0
  exact (MyNat.add_succ (MyNat.ofNat n) 0).symm

instance : CommRing MyInt where
  left_distrib := MyInt.left_distrib
  right_distrib := MyInt.right_distrib
  mul_assoc := MyInt.mul_assoc
  one_mul := MyInt.one_mul
  mul_one := MyInt.mul_one
  zero_mul := MyInt.zero_mul
  mul_zero := MyInt.mul_zero
  mul_comm := MyInt.mul_comm
  zsmul := zsmulRec
  neg_add_cancel := MyInt.neg_add_cancel
  natCast := MyInt.ofNat
  natCast_zero := rfl
  natCast_succ := MyInt.ofNat_succ

example (m n : MyInt) : (m - n) * (m + n) = m * m - n * n := by
  ring

example (m : MyInt) : ∃ s t : MyInt, s * t = m * m * m - 1 := by
  exists m - 1, m * m + m + 1
  ring
