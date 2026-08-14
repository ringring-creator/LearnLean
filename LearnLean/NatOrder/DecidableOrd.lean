import LearnLean.NatOrder.PartialOrder

example : 0 ≤ 3 := by
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.refl

deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by
  decide

#eval 32 + 13 ≠ 46

-- bool less than or equals to
def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => MyNat.ble a b

#eval MyNat.ble 0 0 -- true
#eval MyNat.ble 3 4 -- true
#eval MyNat.ble 4 3 -- false

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n + 1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) : MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by rfl

def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
  (case1 : ∀ (n : MyNat), motive 0 n)
  (case2 : ∀ (n : MyNat), motive (n + 1) 0)
  (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
  (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n => simp
  | case2 n =>
    suffices ¬ n + 1 ≤ 0 from by simp_all
    intro h
    simp_all
  | case3 m n ih =>
    simp [ih]

instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 0 ≤ 0 -- true
#eval 1 ≤ 3 -- true
#eval 3 ≤ 1 -- false

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

example : 1 < 4 := by
  decide

example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
