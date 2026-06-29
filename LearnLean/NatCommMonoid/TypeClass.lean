-- Peano axioms
inductive MyNat where
    | zero
    | succ(n : MyNat)

-- Add
def MyNat.add(m n : MyNat): MyNat :=
    match n with
    | .zero => m
    | .succ n => succ (add m n)

def MyNat.ofNat (n : Nat) : MyNat :=
    match n with
    | 0 => MyNat.zero
    | n + 1 => MyNat.succ (MyNat.ofNat n)

-- The numeric literal is interpreted as type MyNat.
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
    ofNat := MyNat.ofNat n

#check 0 -- 0 : MyNat
#check 1 -- 1 : MyNat

instance : Add MyNat where
    add := MyNat.add

def MyNat.one := MyNat.succ MyNat.zero

#check 1 + 1
#check MyNat.one + MyNat.one
#eval 0 + 0 -- MyNat.zero
#eval MyNat.one + MyNat.one -- MyNat.succ (MyNat.succ (MyNat.zero))

def MyNat.toNat (n : MyNat) : Nat :=
    match n with
    | 0 => 0
    | n + 1 => MyNat.toNat n + 1

instance : Repr MyNat where
    reprPrec n _ := repr n.toNat

    #eval 0 + 0
    #eval 1 + 1
