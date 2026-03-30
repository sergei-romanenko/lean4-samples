--
-- Sqrt2Irr.Coquand.Corollary
--

import Batteries
import Aesop

import Sqrt2Irr.Coquand.Misc
import Sqrt2Irr.Coquand.PNat
import Sqrt2Irr.Coquand.TwoDivides
import Sqrt2Irr.Coquand.Cancellative
import Sqrt2Irr.Coquand.Theorem

instance : CAMonoid PNat where
  op := PNat.mul
  neutral := nz1
  op_assoc := PNat.mul_assoc
  op_comm := PNat.mul_comm
  neutral_op := PNat.one_mul
  op_left_cancel := PNat.mul_left_cancel

-- Prime nz2

theorem divides_to_d2 (n : PNat) : Divides nz2 n -> D2 n.val
  := by
  intro ⟨z, eq_2z_n⟩
  have := calc
        2 * z.val
    _ = nz2.mul z  := rfl
    _ = n          := congrArg PNat.val eq_2z_n
    _ = n.val      := rfl
  exact ⟨z.val, this⟩

theorem not_d2_1 : D2 1 -> False
  | ⟨ 0, m2x_1 ⟩ => nomatch m2x_1
  | ⟨ x + 1, m2x_s ⟩ => by omega

theorem d2_to_divides : (n : PNat) -> D2 n.val -> Divides nz2 n
  | ⟨0, gt0⟩, _ => nomatch gt0
  | ⟨1, gt0⟩, d2_1 => False.elim $ not_d2_1 d2_1
  | ⟨n + 2, gt0⟩, ⟨x, m2x_n2⟩ => by
      simp [PNat.val] at m2x_n2
      have px : 0 < x := by omega
      exists ⟨x, px⟩
      simp [nz2, CAMonoid.op, PNat.mul, PNat.val]
      exact Subtype.ext m2x_n2

theorem prime_nz2 : Prime nz2
  | ⟨x, px⟩, ⟨y, py⟩, ⟨z, d2p_xy⟩ => by
      have d2_xy := divides_to_d2 (PNat.mul ⟨x, px⟩ ⟨y, py⟩) ⟨z, d2p_xy⟩
      simp [PNat.mul, PNat.val] at d2_xy
      have d2x'd2y : D2 x ∨ D2 y := d2mn_d2m'd2n x y d2_xy
      exact Or.elim d2x'd2y
        (Or.inl ∘ d2_to_divides ⟨x, px⟩)
        (Or.inr ∘ d2_to_divides ⟨y, py⟩)

def PNat.LT (m n : PNat) : Prop :=
  m.val < n.val

theorem nz2eq_PLT (m n : PNat) (m2_mn : Multiple nz2 m n) : m.LT n
  := by
  have pm := m.property
  have m2_mn_val := congrArg PNat.val m2_mn
  simp [CAMonoid.op, PNat.val, PNat.mul, nz2] at m2_mn_val
  simp [PNat.LT, PNat.val]
  omega

-- Well-founded

theorem subrel_m2_plt : Subrelation (Multiple nz2) PNat.LT
  := by
  intro x y
  exact nz2eq_PLT x y

def PNat.lt_wf_rel : WellFoundedRelation PNat :=
  invImage PNat.val Nat.lt_wfRel

theorem wf_multiple_nz2 : WellFounded (Multiple nz2)
  := Subrelation.wf subrel_m2_plt (PNat.lt_wf_rel.wf)

--
-- Nz2 is not rational.
--

theorem corollary : NotSquare nz2
  := main_theorem nz2 prime_nz2 wf_multiple_nz2
