import Batteries
import Aesop

--
--  Basic setup, inductive trees, and almost-full relations
--

@[aesop unsafe [constructors, cases]]
inductive AlmostFull {X : Type} : (X -> X -> Prop) -> Prop where
  | now : {R : X -> X -> Prop} ->
     (n : ∀ x y, R x y) -> AlmostFull R
  | later : {R : X -> X -> Prop} ->
     (l : ∀ u, AlmostFull (fun x y => R x y ∨ R u x)) -> AlmostFull R
open AlmostFull

@[simp]
theorem af_strengthen
   {X : Type} {A B : X -> X -> Prop} (p : AlmostFull A)
    (a2b : ∀ x y, A x y -> B x y) : AlmostFull B
  :=
  match p with
  | now ha =>
      now fun x y => a2b x y (ha x y)
  | later h =>
      later $
      fun u =>
      af_strengthen (h u) (
        fun x y => fun
        | .inl axy => Or.inl (a2b x y axy)
        | .inr azx => Or.inr (a2b u x azx))

example
   {X : Type} {A B : X -> X -> Prop} (p : AlmostFull A)
    (hab : ∀ x y, A x y -> B x y) : AlmostFull B
  := by
  induction p generalizing B <;> aesop

-- AlmostFull implies that every infinite chain has two related elements

theorem sec_binary_infinite_chain
    {X : Type} {R : X -> X -> Prop} (p : AlmostFull R) (f : Nat -> X) (k : Nat) :
    ∃ m n, k ≤ m ∧ m < n ∧ R (f m) (f n)
  := by
  induction p generalizing k with
  | @now R' rxy =>
      show ∃ m n, k ≤ m ∧ m < n ∧ R' (f m) (f n)
      exists k, k + 1
      simp only [Nat.le_refl, Nat.lt_add_one, true_and]
      exact rxy (f k) (f (k + 1))
  | @later R' p' ih =>
      show ∃ m n, k ≤ m ∧ m < n ∧ R' (f m) (f n)
      specialize ih (f k) (k + 1)
      simp_all only [exists_and_left]
      obtain ⟨m, lekm, x, ltmx, r'r'⟩ := ih
      cases r'r' with
      | inl h1 =>
          exists m
          have : k ≤ m := by omega
          simp [this]
          exists x
      | inr h2 =>
          exists k
          simp
          exists m

theorem af_inf_chain {X : Type} {R : X -> X -> Prop} (p : AlmostFull R)
    (f : Nat -> X):  ∃ m n, m < n ∧ R (f m) (f n)
  := by

  have : ∃ m n, 0 ≤ m ∧ m < n ∧ R (f m) (f n) := by
    apply sec_binary_infinite_chain p f 0
  show ∃ m n, m < n ∧ R (f m) (f n)
  simp at this
  exact this

--
-- From a decidable Well-founded relation to an AlmostFull
--

-- Generalization to an arbitrary decidable well-founded relation

theorem af_iter {X : Type} {R : X -> X -> Prop}
    (decR : DecidableRel R) (z : X) (accX : Acc R z) :
    AlmostFull (fun x y => ¬ R x z ∨ ¬ R y x)
  := by
  induction accX
  rename_i x h ih
  apply later
  intro u
  match decR u x with
  | .isFalse nrux =>
      apply now
      --aesop
      intro _ _
      exact (Or.inr ∘ Or.inl) nrux
  | .isTrue rux =>
      have af_R' := ih u rux
      apply af_strengthen af_R'
      --aesop
      intro _ _
      exact (Or.elim · (Or.inr ∘ Or.inr) (Or.inl ∘ Or.inr))

theorem af_from_wf {X : Type} {R : X -> X -> Prop}
        (w : WellFounded R) (d : DecidableRel R) : AlmostFull (fun x y => ¬ R y x)
    :=
    later fun u =>
    have af_a := af_iter d u (WellFounded.apply w u)
    have ab := fun _ _ => (Or.elim · Or.inr Or.inl)
    af_strengthen af_a ab

--
-- From an AlmostFull relation to a Well-Founded one
--

@[aesop unsafe [constructors, cases]]
inductive ReflTransGen (r : α -> α -> Prop) (a : α) : α -> Prop
  | refl : ReflTransGen r a a
  | tail {b} : Relation.TransGen r a b -> ReflTransGen r a b

local add_aesop_rules unsafe [Relation.TransGen]

@[simp]
theorem rtt_t_tt {X} {T : X -> X -> Prop} {x y u : X}
      (rttxu : ReflTransGen T x u) (tuy: T u y) : Relation.TransGen T x y
  :=
  match rttxu with
  | .refl => Relation.TransGen.single tuy
  | .tail ttxu => Relation.TransGen.tail ttxu tuy

@[simp]
theorem rtt_t_rtt {X} {T : X -> X -> Prop} {x y u : X}
      (rttxu : ReflTransGen T x u) (tuy: T u y) : ReflTransGen T x y
  :=
  ReflTransGen.tail $
  match rttxu with
  | .refl => Relation.TransGen.single tuy
  | .tail ttxu => Relation.TransGen.tail ttxu tuy

@[simp]
theorem acc_from_af
      {X : Type}
      {R : X -> X -> Prop} (p : AlmostFull R) (T : X -> X -> Prop) (x : X)
      (h : ∀ z y, (ReflTransGen T y x ->
                Relation.TransGen T z y -> R y z -> False)) : Acc T x
  := by
  induction p generalizing x with
  | @now R' n =>
      apply Acc.intro
      intro z tzx
      apply False.elim
      apply h z x ReflTransGen.refl (Relation.TransGen.single tzx) (n x z)
  | @later R' l l_ih =>
      apply Acc.intro
      intro z tzx
      apply l_ih x z
      intro u y rttyz ttuy rr
      simp_all
      cases rr with
      | inl ryu =>
          have rttyx : ReflTransGen T y x := rtt_t_rtt rttyz tzx
          apply h u y rttyx ttuy ryu
      | inr rxy =>
          have rttyx: Relation.TransGen T y x := rtt_t_tt rttyz tzx
          exact h y x ReflTransGen.refl rttyx rxy

theorem wf_from_af (X : Type) (R : X -> X -> Prop) (p : AlmostFull R)
      (T : X -> X -> Prop)
      (h : ∀ x y, Relation.TransGen T x y -> R y x -> False)
        : WellFounded T
  := by
  apply WellFounded.intro
  intro y
  apply acc_from_af p T
  intro x z rttzy ttxz
  exact h x z ttxz

--
-- A reassuring lemma
--

def Transitive  {X : Type} (R : X -> X -> Prop) :=
  ∀ {a b c : X},  R a b -> R b c -> R a c

theorem wf_from_wqo (X : Type) (R : X -> X -> Prop)
      (tr : Transitive R) (p : AlmostFull R) :
      WellFounded (fun x y => R x y ∧ ¬ R y x)
  := by

  let P := fun x y => R x y ∧ ¬ R y x

  let rec get_r {x y} : Relation.TransGen P x y -> R x y
    | .single pxy => pxy.left
    | .tail (b := z) h pzy =>
        have rxz : R x z := get_r h
        have rzy : R z y := pzy.left
        tr rxz rzy

  let rec get_false {x y} : Relation.TransGen P x y -> R y x -> False
    | .single pxy, ryx =>
        have nryx : ¬R y x := pxy.right
        nryx ryx
    | .tail (b := z) tpxz pzy, ryx =>
        have ⟨rzy, nryz⟩ := pzy
        have rxz : R x z := get_r tpxz
        have rzx : R z x := tr rzy ryx
        get_false tpxz rzx

  apply wf_from_af X R p P
  apply get_false
