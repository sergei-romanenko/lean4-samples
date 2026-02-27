/-
    Title:      Berghofer.HigmanT2
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004.

    from Isabelle to Lean 4.
-/

import Batteries
import Aesop

-- Words are modelled as lists of letters from
-- the two letter alphabet.

inductive Letter : Type where
  | l0 : Letter
  | l1 : Letter
open Letter

abbrev Word := List Letter

-- The embedding relation on words is defined inductively.
-- Intuitively, a word `v` can be embedded into a word `w`,
-- if we can obtain `v` by deleting letters from `w`.
-- For example,
--   l1 :: l0 :: l1 :: [] ⊴ l0 :: l1 :: l0 :: l0 :: l1 :: []

inductive «<<» : (v w : Word) -> Prop where
  | empty : «<<» [] []
  | drop {v w a}  : «<<» v w -> «<<» v (a :: w)
  | keep {v w a}  : «<<» v w -> «<<» (a :: v) (a :: w)
open «<<»

infix:50 " << " => «<<»

def test1 : l1 :: l0 :: l1 :: [] << l0 :: l1 :: l0 :: l0 :: l1 :: [] :=
  drop $ keep $ drop $ keep $ keep empty

-- [] is embeddable in any word.

def emb_empty : (w : Word) -> [] << w
  | [] => empty
  | _ :: ws => drop $ emb_empty ws

-- We represent a finite sequence w_0, w_1, ... , w_n as
--   w_n :: ... :: w_1 :: w_0 :: []

abbrev WSeq := List Word

-- In order to formalize the notion of a good sequence,
-- we define an auxiliary relation *<<.
--   ws *<< v
-- means that ws contains a word w, such that w << v .

inductive «*<<» : (ws : WSeq) -> (v : Word) -> Prop where
  | eHere  {w ws v} : w << v -> «*<<» (w :: ws) v
  | eThere {w ws v} : «*<<» ws v -> «*<<» (w :: ws) v
open «*<<»

infix:50 " *<< " => «*<<»

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

inductive Good : (ws : WSeq) -> Prop where
  | here  {w ws} : ws *<< w -> Good (w :: ws)
  | there {w ws} : Good ws -> Good (w :: ws)
open Good

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

inductive Bar : WSeq -> Prop where
  | now   {ws}   : Good ws -> Bar ws
  | later {ws} : ((w : Word) -> Bar (w :: ws)) -> Bar ws
open Bar

-- abbrev WBar (ws : WSeq) := (w : Word) -> Bar (w :: ws)

inductive IsLater {xs} : Bar xs -> Prop where
  | isLater {xs} : IsLater (later xs)
open IsLater


-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)

-- The following function adds a letter to each word in a word list.

def «::*» : (a : Letter) -> (ws : WSeq) -> WSeq
  | _, [] => []
  | a, (w :: ws) => (a :: w) :: («::*» a ws)

infixr:67 " ::* " => «::*»

namespace Berghofer's_T

  -- This is the relation `T`, used in the original Berghofer's proof.

  -- `T a vs ws` means that vs is obtained from ws by
  -- (1) first copying the prefix of words starting with the letter b,
  --     where Not(a = b), and
  -- (2) then appending the tails of words starting with a.

inductive T : (a : Letter) -> (vs ws : WSeq) -> Prop where
  | tInit {a b w ws} : Not (a = b) ->
            T a (w ::(b ::* ws)) ((a :: w) :: (b ::* ws))
  | tKeep {a vs ws w} : T a vs ws ->
            T a (w :: vs) ((a :: w) :: ws)
  | tDrop {a b vs ws w} : Not (a = b) ->
            T a vs ws -> T a vs ((b :: w) :: ws)

end Berghofer's_T

-- In Berghofer's proof `T` is always used as a comination
--   `T a xs zs -> T b ys zs -> ...`
-- So, we can simplify the proof by directly defining a relation T2, such that
-- `T2 xs ys zs` is equivalent to `(T a xs zs, T a xs zs)`.

inductive T2 : (zs xs ys : WSeq) -> Prop where
  | init0 {w ys} : T2 (w :: (l1 ::* ys)) ys ((l0 :: w) :: (l1 ::* ys))
  | init1 {w xs} : T2 xs (w :: (l0 ::* xs)) ((l1 :: w) :: (l0 ::* xs))
  | step0 {w xs ys zs} : T2 xs ys zs -> T2 (w :: xs) ys ((l0 :: w) :: zs)
  | step1 {w xs ys zs} : T2 xs ys zs -> T2 xs (w :: ys) ((l1 :: w) :: zs)
open T2

--
-- The proof of Higman’s lemma is divided into several parts, namely
-- prop1, prop2 and prop3.
-- From the computational point of view, these theorems can be thought of
-- as functions transforming trees.

--
-- prop1 : Sequences “ending” with empty word (trivial)
-- A sequence ending with the empty word satisfies predicate Bar,
-- since it can trivially be extended to a good sequence
-- by appending any word.
--

def bar_w_empty (ws : WSeq) : Bar ([] :: ws) :=
  -- later (emb_empty · |> here |> here |> now)
  later $
  show (w : Word) -> Bar (w :: [] :: ws) from
  fun w =>
  have : [] << w := emb_empty w
  have : [] :: ws *<< w := eHere this
  have : Good (w :: [] :: ws) :=  here this
  have : Bar (w :: [] :: ws) := now this
  this

-- Lemmas. w *<< v ... -> (a :: w) *<< v ...

def s_emb_drop {ws v a} : ws *<< v -> ws *<< a :: v
  | eHere w_emb_v => eHere (drop w_emb_v)
  | eThere ws_s_emb_v => eThere (s_emb_drop ws_s_emb_v)

def s_emb_keep {ws v a} : ws *<< v -> (a ::* ws) *<< a :: v := fun
  | eHere w_emb_v => eHere (keep w_emb_v)
  | eThere ws_s_emb_v => eThere (s_emb_keep ws_s_emb_v)

def t2_semb_drop0 {xs ys zs w} : T2 xs ys zs -> xs *<< w -> zs *<< l0 :: w
  | init0 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (s_emb_drop semb_w)
  | init1 => fun
      semb_w => eThere (s_emb_keep semb_w)
  | step0 t2 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (t2_semb_drop0 t2 semb_w)
  | step1 t2 => fun
    | semb_w => eThere (t2_semb_drop0 t2 semb_w)

def t2_semb_drop1 {xs ys zs w} : T2 xs ys zs -> ys *<< w -> zs *<< l1 :: w
  | init0 => fun
    | semb_w => eThere (s_emb_keep semb_w)
  | init1 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere semb_w => eThere (s_emb_drop semb_w)
  | step0 t2 => fun
    | semb_w => eThere (t2_semb_drop1 t2 semb_w)
  | step1 t2 => fun
    | eHere emb_w => eHere (keep emb_w)
    | eThere emb_w => eThere (t2_semb_drop1 t2 emb_w)

-- Lemmas. Good ... -> Good ...

def good_drop {ws a} : Good ws -> Good (a ::* ws) := fun
  | here ws_s_emb_w =>
      here (s_emb_keep ws_s_emb_w)
  | there good_ws =>
      there (good_drop good_ws)

def good_t0 {xs ys zs} : T2 xs ys zs -> Good xs -> Good zs := fun
  | init0 => fun
    | here semb_w => here (s_emb_drop semb_w)
    | there good_l1ys => there good_l1ys
  | init1 => fun
    | gx => there (good_drop gx)
  | step0 t2 => fun
    | here semb_w => here (t2_semb_drop0 t2 semb_w)
    | there gx => there (good_t0 t2 gx)
  | step1 t2 => fun
    | gx => there (good_t0 t2 gx)

def good_t1 {xs ys zs} : T2 xs ys zs -> Good ys -> Good zs := fun
  | init0 => fun
    | gy => there (good_drop gy)
  | init1 => fun
    | here semb_w => here (s_emb_drop semb_w)
    | there good_l0xs => there good_l0xs
  | step0 t2 => fun
    | gy => there (good_t1 t2 gy)
  | step1 t2 => fun
    | here semb_w => here (t2_semb_drop1 t2 semb_w)
    | there gy => there (good_t1 t2 gy)

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on the first letter of the first word following zs.

namespace Take1

def tt_bb {xs ys zs} (t : T2 xs ys zs) : (b_x : Bar xs) -> (b_y : Bar ys) -> Bar zs := fun
  | now nx, _ => now (good_t0 t nx)
  | later lx, now ny => now (good_t1 t ny)
  | later lx, later ly => later $
      show (w : Word) -> Bar (w :: zs) from
      fun
      | [] => bar_w_empty zs
      | l0 :: w => tt_bb (step0 t) (lx w) (later ly)
      | l1 :: w => tt_bb (step1 t) (later lx) (ly w)
termination_by b_x b_y => (b_x, b_y)
-- decreasing_by simp_wf; done

end Take1

namespace Take2

def tt_bb {xs ys} (b_x : Bar xs) (b_y : Bar ys) {zs} (t : T2 xs ys zs) : Bar zs :=
  match b_x, b_y with
  | now nx, _ => now (good_t0 t nx)
  | later lx, now ny => now (good_t1 t ny)
  | later lx, later ly => later $
      show (w : Word) -> Bar (w :: zs) from
      fun
      | [] => bar_w_empty zs
      | l0 :: w => tt_bb (lx w) (later ly) (step0 t)
      | l1 :: w => tt_bb  (later lx) (ly w) (step1 t)
termination_by (b_x, b_y)
-- decreasing_by simp_wf; done

end Take2

namespace Take3

def tt_bb : (xsb : {xs // Bar xs}) -> (ysb : {ys // Bar ys})->
      (zs : WSeq) -> T2 xsb.val ysb.val zs -> Bar zs := fun
  | ⟨ xs, now nx ⟩, ⟨ ys, bys ⟩, zs, t => now (good_t0 t nx)
  | ⟨ xs, later lx ⟩, ⟨ ys, now ny ⟩, zs, t => now (good_t1 t ny)
  | ⟨ xs, later lx ⟩, ⟨ ys, later ly ⟩, zs, t => later $
      show (w : Word) -> Bar (w :: zs) from
      fun
      | [] => bar_w_empty zs
      | l0 :: w' =>
          tt_bb ⟨_, lx w'⟩ ⟨ys, later ly⟩ ((l0 :: w') :: zs) t.step0
      | l1 :: w' =>
          tt_bb  ⟨xs, later lx⟩ ⟨_, ly w'⟩ ((l1 :: w') :: zs) t.step1
-- termination_by xsb ysb => (xsb.snd, ysb.snd)
-- termination_by xsb ysb => (xsb.property, ysb.property)
-- decreasing_by sorry

end Take3

axiom tt_bb {xs ys} (b_x : Bar xs) (b_y : Bar ys) {zs} (t : T2 xs ys zs) : Bar zs

--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws
--

namespace bar_lift1

mutual

def bar_lift (b ws : _) : Bar ws -> Bar (b ::* ws) := fun
  | now n => now $ good_drop n
  | later l => later $ later_lift b ws (later l) ⟨l, rfl⟩
-- termination_by bw => bw

def later_lift (b ws : _) (bw : Bar ws) (lbw : ∃ l, bw = later l) (w : Word) :
      Bar (w :: (b ::* ws)) :=
  show Bar (w :: b ::* ws) from
  let l := lbw.choose
  match b with
  | l0 => match w with
      | [] => bar_w_empty (l0 ::* ws)
      | (l0 :: w) => bar_lift l0 (w :: ws) (l w) -- ===
      | (l1 :: w) => tt_bb (later l) (later_lift l0 ws (later l) lbw w) init1
  | l1 => match w with
      | [] => bar_w_empty (l1 ::* ws)
      | (l0 :: w) => tt_bb  (later_lift l1 ws (later l) lbw w) (later l) init0
      | (l1 :: w) => bar_lift l1 (w :: ws) (l w) -- ===
-- termination_by w

end

end bar_lift1

axiom bar_lift (b ws : _) : Bar ws -> Bar (b ::* ws)

--
-- higman: Main theorem
--

def later_empty :  (w : Word) -> Bar (w :: [])
  | [] => bar_w_empty []
  | c :: w =>
      bar_lift c (w :: []) (later_empty w)

def bar_empty : Bar [] :=
  later later_empty

def bar_ne (w ws : _) : Bar ws -> Bar (w :: ws)
  | now n => now (there n)
  | later l => l w

def higman : (ws : WSeq) -> Bar ws
  | [] => bar_empty
  | (w :: ws) => bar_ne w ws (higman ws)

--
-- good-prefix-lemma
--

inductive Prefix (f : Nat -> Word) : (Nat × WSeq) -> Prop where
  | PZ : Prefix f (0, [])
  | PS {i xs} : Prefix f (i, xs) -> Prefix f (i + 1, f i :: xs)

def good_prefix' (f : Nat -> Word)
    (s : _) (p : Prefix f s) : Bar (s.snd) ->
    {s' // Prefix f s' ∧ Good (s'.snd)}
  | now n =>
      {s // (p ∧ n)}
  | later l =>
      let i := s.fst
      let ws := s.snd
      good_prefix' f (i + 1, f i :: ws) (.PS p) (l (f i))


-- Finding good prefixes of infinite sequences

def good_prefix (f : Nat -> Word) :
    {s // Prefix f s ∧ Good (s.snd)} :=
  good_prefix' f (0, []) .PZ bar_empty
