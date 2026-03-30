--
-- Sqrt2Irr.Coquand.PNat
--

import Batteries
import Aesop

import Sqrt2Irr.Coquand.Misc

def PNat := { n : Nat // 0 < n } deriving DecidableEq

/-- The underlying natural number -/
@[coe]
def PNat.val : PNat -> Nat := Subtype.val

instance coePNatNat : Coe PNat Nat :=
  ⟨PNat.val⟩

instance : Repr PNat :=
  ⟨fun n n' => reprPrec n.1 n'⟩

def nz1 : PNat := ⟨1, Nat.one_pos⟩
def nz2 : PNat := ⟨2, by exact Nat.zero_lt_two⟩

def PNat.add : PNat -> PNat -> PNat
  | ⟨a, pa⟩, ⟨b, pb⟩ =>
      ⟨a + b, by exact Nat.add_pos_right a pb⟩

def PNat.mul (m n : PNat) : PNat
  := ⟨m.val * n.val, by exact Nat.mul_pos m.property n.property⟩

theorem PNat.add_assoc (l c r : PNat) : ((l.add c).add r) = l.add (c.add r)
  := Subtype.ext (Nat.add_assoc l.val c.val r.val)

theorem PNat.mul_assoc (l c r : PNat) : l.mul (c.mul r) = (l.mul c).mul r
  := Subtype.ext (Eq.symm $ Nat.mul_assoc l.val c.val r.val)

def PNat.one_mul (n : PNat) : nz1.mul n = n
  := Subtype.ext (Nat.one_mul n.val)

def PNat.mul_comm (m n : PNat) : m.mul n =  n.mul m
  := Subtype.ext (Nat.mul_comm m.val n.val)

theorem PNat.mul_left_cancel (k m n : PNat) (km_kn : k.mul m = k.mul n) : m = n
  :=
  have := calc
        k.val * m.val
    _ = (k.mul m).val := rfl
    _ = (k.mul n).val := congrArg val km_kn
    _ = k.val * n.val := rfl
  Subtype.ext $ Nat.mul_left_cancel k.property this
