-- Demo

inductive N : Type where
  | zero : N
  | succ : N -> N
  deriving Repr

#check N
#print N

#check N.succ N.zero
#print N.succ
#eval N.succ N.zero

def n3₁ := N.succ (N.succ (N.succ N.zero))
def n3₂ := N.zero.succ.succ.succ

open N

def n3₃ := succ (succ (succ zero))
def n3₄ := zero.succ.succ.succ

#eval n3₄

def add : N -> N -> N
  | x, zero => x
  | x, succ y => succ (add x y)

-- Magic to write 3 rather than succ (succ (succ zero))

def N.ofNat : Nat -> N
  | 0 => zero
  | n + 1 => succ (N.ofNat n)

instance (n : Nat) : OfNat N n where
  ofNat := N.ofNat n

#eval (3 : N)


-- Equality

theorem eq_refl {A} (x : A) : x = x :=
  Eq.refl x

theorem eq_symm {A} (x y : A) (h : x = y) : y = x :=
  Eq.symm h

theorem eq_trans {A} (x y z : A) (h1 : x = y) (h2 : y = z) : x = z :=
  Eq.trans h1 h2

--Theorem proving

theorem theorem1 : add 2 1 = 3 :=
  rfl

theorem theorem2 (n : N) : add n 0 = n :=
  rfl

def add_left_identity : (x : N) -> add zero x = x
  | zero =>
      show add zero zero = zero from
      rfl
  | succ x =>
      show succ (add zero x) = succ x from
      let ih : add zero x = x := add_left_identity x
      congrArg succ ih

def add_left_identity_rw : (x : N) -> add zero x = x
  | zero =>
      rfl
  | succ x => by
      rw [add]
      rw [add_left_identity_rw x]

def add_left_identity_calc : (x : N) -> add zero x = x
  | zero =>
      calc add zero zero = zero
        := rfl
  | succ x =>
      calc add zero (succ x)
      _ = succ (add zero x)
          := by rw [add]
      _ = x.succ
          := by rw [add_left_identity_calc x]

def add_succ : (x y : N) -> add (succ x) y = succ (add x y)
  | x, zero =>
      show add (succ x) zero = succ (add x zero) from
      rfl
  | x, succ y =>
      show add (succ x) (succ y) = succ (add x (succ y)) from
      congrArg succ (add_succ x y)

def add_succ_calc : (x y : N) -> add (succ x) y = succ (add x y)
  | x, zero =>
      calc add (succ x) zero
      _ = succ x
        := by rw [add]
      _ = succ (add x zero)
        := by rw [add]
  | x, succ y =>
      calc add (succ x) (succ y)
      _ = succ (add (succ x) y)
        := by rw [add]
      _ = succ (succ (add x y))
        := by rw [add_succ_calc x y]
      _ = succ (add x (succ y))
        := by rw [<- add]

def add_comm : (x y : N) -> add x y = add y x
  | x, zero =>
      show add x zero = add zero x from
      Eq.symm (add_left_identity x)
  | x, succ y =>
      show add x (succ y) = add (succ y) x from
      let h1 : add x (succ y) = succ (add x y) :=
        rfl
      let h2 : succ (add x y) = succ (add y x) :=
        congrArg succ (add_comm x y)
      let h3 : succ (add y x) = add (succ y) x :=
          Eq.symm (add_succ y x)
      Eq.trans h1 (Eq.trans h2 h3)

def add_comm_calc : (x y : N) -> add x y = add y x
  | x, zero =>
      calc add x zero
      _ = x
        := by rw [add]
      _ = add zero x
        := by rw [add_left_identity x]
  | x, succ y =>
      calc add x (succ y)
      _ = succ (add x y)
        := by rw [add]
      _ = succ (add y x)
        := by rw [add_comm_calc x y]
      _ = add (succ y) x
        := by rw [<- add_succ y x]
