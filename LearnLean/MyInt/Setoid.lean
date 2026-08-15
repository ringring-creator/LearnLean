structure Point where
  x : Int
  y : Int

#check {x := 1, y := 2 : Point}
#check Point.mk
#check Point.mk 1 2
#eval
  let p := Point.mk 1 2
  p.x

example {α : Type} (r : α → α → Prop) (h: Equivalence r) : ∀ x, r x x := by
  exact h.refl

example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor

  case refl =>
    intro x
    rfl

  case symm =>
    intro x y h
    rw [h]

  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

example {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor
  case refl =>
    intro x
    trivial
  case symm =>
    intro x y h
    trivial
  case trans =>
    intro x y h
    trivial

