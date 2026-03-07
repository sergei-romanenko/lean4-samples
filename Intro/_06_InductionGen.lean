import Batteries
import Aesop

inductive N where
  | zero : N
  | succ (n : N) : N

open N

def N.ofNat : Nat -> N
  | 0 => zero
  | n + 1 => succ (N.ofNat n)

instance (n : Nat) : OfNat N n where
  ofNat := N.ofNat n

example : (3 : N) = zero.succ.succ.succ
  := rfl

def add_acc : N -> N -> N := fun
  | m, zero => m
  | m, succ n => add_acc m.succ n

@[simp]
theorem acc_add_zero (m : N) : add_acc m zero = m
  := rfl

@[simp]
theorem acc_add_succ (m n : N) : add_acc m n.succ = add_acc m.succ n
  := rfl

/-
theorem acc_succ_add₀ (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n with
  | zero =>
      -- simp
      show add_acc m.succ zero = (add_acc m zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc m.succ n'.succ = (add_acc m n'.succ).succ
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = (add_acc m.succ n').succ
      -- ih : add_acc m.succ n' = (add_acc m n').succ
      -- ih is not general enough!
      sorry
 -/

@[simp]
theorem acc_succ_add (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m with
  | zero =>
      -- simp
      show add_acc m.succ zero = (add_acc m zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc m.succ n'.succ = (add_acc m n'.succ).succ
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = (add_acc m.succ n').succ
      -- ih : ∀ (m : Nat), add_acc m.succ n' = (add_acc m n').succ
      exact ih m.succ

theorem acc_succ_add₂ (m n : N) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m <;> aesop

theorem acc_zero_add (n : N) : add_acc zero n = n := by
  induction n with
  | zero =>
      -- simp
      show add_acc zero zero = zero
      rewrite [acc_add_zero]
      show zero = zero
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc zero n'.succ = n'.succ
      show add_acc zero.succ n' = n'.succ
      rewrite [acc_succ_add]
      show (add_acc zero n').succ = n'.succ
      rewrite [ih]
      show n'.succ = n'.succ
      rfl

theorem acc_zero_add₁ (n : N) : add_acc zero n = n := by
  induction n <;> aesop
