-- Peano axioms
inductive MyNat where
    | zero
    | succ(n : MyNat)

-- Check Peano axioms
#check MyNat.zero
#check MyNat.succ
#check MyNat.succ MyNat.zero

-- Define one and two
def MyNat.one := MyNat.succ MyNat.zero
def MyNat.two := MyNat.succ MyNat.one

-- Add
def MyNat.add(m n : MyNat): MyNat :=
    match n with
    | .zero => m
    | .succ n => succ (add m n)

#check MyNat.add .one .one = .two

-- custom reduce comannd
set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one
#reduce MyNat.two

-- prrof
example : MyNat.add .one .one = .two := by
    rfl

example : MyNat.add .one .one = .two := by
    change MyNat.succ (MyNat.add .one .zero) = .two
    change MyNat.succ .one = .two
    change MyNat.succ .one = MyNat.succ .one
    exact Eq.refl (MyNat.succ .one)
