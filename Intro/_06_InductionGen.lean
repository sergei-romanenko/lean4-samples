import Batteries
import Aesop

def add_acc : Nat -> Nat -> Nat := fun
  | m, .zero => m
  | m, .succ n => add_acc m.succ n

@[simp]
theorem acc_add_zero (m : Nat) : add_acc m .zero = m
  := rfl

@[simp]
theorem acc_add_succ (m n : Nat) : add_acc m n.succ = add_acc m.succ n
  := rfl

/-
theorem acc_succ_add₀ (m n : Nat) : add_acc m.succ n = (add_acc m n).succ := by
  induction n with
  | zero =>
      -- simp
      show add_acc m.succ .zero = (add_acc m .zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc (m + 1) (n' + 1) = add_acc m (n' + 1) + 1
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = add_acc (m + 1) n' + 1
      -- ih : add_acc m.succ n' = (add_acc m n').succ
      -- ih is not general enough!
      sorry
 -/

@[simp]
theorem acc_succ_add (m n : Nat) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m with
  | zero =>
      -- simp
      show add_acc m.succ .zero = (add_acc m .zero).succ
      rewrite [acc_add_zero, acc_add_zero]
      show m.succ = m.succ
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc m.succ n'.succ = (add_acc m n'.succ).succ
      rewrite [acc_add_succ, acc_add_succ]
      show add_acc m.succ.succ n' = (add_acc m.succ n').succ
      -- ih : ∀ (m : Nat), add_acc m.succ n' = (add_acc m n').succ
      exact ih (m + 1)

theorem acc_succ_add₁ (m n : Nat) : add_acc m.succ n = (add_acc m n).succ := by
  induction n generalizing m <;> aesop

theorem acc_zero_add (n : Nat) : add_acc .zero n = n := by
  induction n with
  | zero =>
      -- simp
      show add_acc .zero .zero = .zero
      rewrite [acc_add_zero]
      show Nat.zero = Nat.zero
      rfl
  | succ n' ih =>
      -- simp [ih]
      show add_acc .zero n'.succ = n'.succ
      show add_acc Nat.zero.succ n' = n'.succ
      rewrite [acc_succ_add]
      show (add_acc Nat.zero n').succ = n'.succ
      rewrite [ih]
      show n'.succ = n'.succ
      rfl

theorem acc_zero_add₁ (n : Nat) : add_acc .zero n = n := by
  induction n <;> aesop

/-
theorem add_acc_eq_add₀ (m n : Nat) : add_acc m n = m + n := by
  induction n with
  | zero =>
      show add_acc m 0 = m + 0
      rfl
  | succ n ih =>
      show add_acc m (n + 1) = m + (n + 1)
      show add_acc (m + 1) n = (m + n) + 1
      -- ih : add_acc m n = m + n
      -- ih is not general enough!
      sorry
 -/

theorem add_acc_eq_add (m n : Nat) : add_acc m n = m + n := by
  induction n generalizing m with
  | zero =>
      show add_acc m 0 = m + 0
      rfl
  | succ n ih =>
      show add_acc m (n + 1) = m + (n + 1)
      show add_acc (m + 1) n = (m + n) + 1
      -- ih : ∀ (m : Nat), add_acc m n = m + n
      rw [ih, Nat.succ_add]

theorem add_acc_eq_add₁ (m n : Nat) : add_acc m n = m + n := by
  induction n generalizing m <;> aesop
