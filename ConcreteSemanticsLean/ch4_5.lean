import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Basic

import ConcreteSemanticsLean.ch2
import ConcreteSemanticsLean.ch3

/- Ch4.5.1 : An Example: Even Numbers -/
section ch4_5_1

  inductive ev : ℕ → Prop :=
  | ev0   : ev 0
  | evSS  : ev n → ev (n + 2)
  open ev

  theorem ev_4 : ev 4 := evSS (evSS ev0)
  example : ev 0 → ev (0 + 2) → ev ((0 + 2) + 2) = ev 4 := by simp

  /- Rule Induction -/
  def evn : ℕ → Prop
    | 0 => True
    | 1 => False
    | n + 2 => evn n
  #check evn

  example : ev m → evn m := by
    intro evm
    induction evm -- rule induction
    case ev0 => simp [evn]
    case evSS m' _ evn_m =>
      simp [ev, evn]; exact evn_m

  lemma ev_minus2 : ev m → ev (m - 2) := by
    intro h
    induction h <;> simp[ev]
    . apply ev0
    . assumption

  lemma ev_is_evn : ev n → ev (Nat.succ (Nat.succ n)) := by
    intro evn; induction evn
    . exact (evSS ev0)
    . exact (evSS (by assumption))

  example : ev (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := evSS (evSS ev0)
  example : ev (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
    apply evSS; apply evSS; apply ev0

  @[simp] lemma succ_not_ev : ev n → ¬ev (n + 1) := by
    intro h; induction h
    . intro h'; contradiction
    . case _ n' _ ih =>
      intro h';
      apply ev_minus2 at h'; simp at h'; contradiction

  @[simp] lemma succ_not_evn : ∀ n, evn n → ¬evn (n + 1) := by
    intro n h; induction n
    . intro h'; contradiction
    . case _ n' ih =>
      intro h'; contrapose! h;
      exact ih h'

  @[simp] lemma sub_not_evn : ∀ n ≥ 1, evn n → ¬evn (n - 1) := by
    intro n h; induction n
    . contradiction
    . case _ n' ih =>
      intro h'; simp_all [evn];
      contrapose! h'; apply succ_not_evn at h'; exact h'

  lemma evn_is_ev : ∀ n, evn n → ev n :=
    fun n =>
      match n with
      | 0     => fun _ => ev.ev0
      | 1     => fun h => by contradiction
      | n + 2 => fun h =>
          have h'   : evn n        := h
          have ih   : evn n → ev n := evn_is_ev n -- recursive call to the lemma itself
          have ev_n : ev n         := ih h'
          by exact evSS ev_n

  /- Ch4.5.2 The Reflexive Transitive Closure -/
  inductive star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {x : α} : star r x x
  | step {x y z : α} (h₁ : r x y) (h₂ : star r y z) : star r x z
  #check star

  @[simp] lemma star_trans : star r x y → star r y z → star r x z := by
    intro xy yz
    induction xy
    . exact yz
    . case step x' y' z' x'y' _ z'z_y'z =>
      exact star.step x'y' (z'z_y'z yz)

  /- Ch4.5.3 The General Case -/
end ch4_5_1


section q4_2

  inductive palindrome : mylist α → Prop :=
  | pal0                                           : palindrome []
  | pal1 (a : α)                                   : palindrome (a :: [])
  | pal2 (a : α) (l : mylist α) (h : palindrome l) : palindrome (a :: l ++ (a :: []))
  #check palindrome

  lemma pal_is_rev : palindrome l → reverse l = l := by
    intro pal
    induction pal <;> simp [reverse, append]
    case pal2 α a l pal rev =>
      rw [reverse_concat]; simp [reverse, append]
      rw [rev, empty_concat]
      exact append_is_concat l a

end q4_2

section q4_3
  variable (r : α → α → Prop)

  inductive star' {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl' : star' r x x
  | step' : star' r x y → r y z → star' r x z
  -- instead of r x y → star' r y z → star' r x z

  lemma star_star' : star r x y → r y z → star r x z := by
    intro xy yz
    induction xy
    . exact star.step yz star.refl
    . case step x' y' z' x'y' sy'z' z'z_y'z =>
      exact star.step x'y' (z'z_y'z yz)

  lemma star'_star : star' r y z → r x y → star' r x z := by
    intro yz xy
    induction yz
    . apply star'.step'
      . exact star'.refl'
      . exact xy
    . case step' x' y' _ x'y' sxx' =>
      apply star'.step' (by exact sxx')
      exact x'y'

  theorem star'_trans : star' r x y → star' r y z → star' r x z := by
    intro h1
    induction h1
    . exact fun a => a
    . case step' x' y' _ x'y' sy'z' =>
      intro h2
      have h : star' r x' z := by
        apply star'_star; apply h2; exact x'y'
      apply sy'z' h

  theorem star'_forward : star' r x y → star r x y := by
    intro h
    induction h
    . exact star.refl
    . case step' y' z _ y'z sxy' =>
      apply star_star'; exact sxy'; exact y'z

  theorem star'_backward : star r x y → star' r x y := by
    intro h
    induction h
    . exact star'.refl'
    . case step x' y' z x'y' _ s'y'z =>
      apply star'_star; exact s'y'z; exact x'y'

  theorem star_iff_star' : star r x y ↔ star' r x y := by
    constructor
    . apply star'_backward
    . apply star'_forward

end q4_3

section q4_4
end q4_4

section q4_5

  inductive S : mylist Char → Prop
  | empty : S []
  | aSb {w : mylist Char} : S w → S ('a' :: w ++ ('b' :: []))
  | SS {w1 w2 : mylist Char} : S w1 → S w2 → S (w1 ++ w2)

  inductive T : mylist Char → Prop
  | empty : T []
  | TaTb {w : mylist Char} : T w → T ('a' :: w ++ ('b' :: []))

  lemma T_implies_S : ∀ w, T w → S w := by
    intro w tw
    induction tw
    . exact S.empty
    . case TaTb w' _ sw' =>
      apply S.aSb; exact sw'

  lemma S_implies_T : ∀ w, S w → T w := by
    intro w sw
    induction sw
    . exact T.empty
    . case aSb w' sw' tw' =>
      apply T.TaTb; exact tw'

  lemma S_iff_T : ∀ w, S w ↔ T w := by
    intro w; constructor
    . exact S_implies_T w
    . exact T_implies_S w

end q4_5

section q4_6

  inductive aval_rel : aexp → state → Int → Prop
  | num (n : Int) (st : state) : aval_rel (aexp.ANum n) st n
  | str (s : String) (st : state) : aval_rel (aexp.AString s) st (st s)
  | plus (a1 a2 : aexp) (n1 n2 : Int) (st : state) :
      aval_rel a1 st n1 → aval_rel a2 st n2 → aval_rel (aexp.APlus a1 a2) st (n1 + n2)

  #check aval_rel.plus

  lemma aval_rel_is_aval : aval_rel a st n → aval a st = n := by
    intro h
    induction h <;> simp_all

  lemma aval_is_aval_rel : aval a st = n → aval_rel a st n := by
    intro h; induction h; induction a
    . apply aval_rel.num
    . apply aval_rel.str
    . apply aval_rel.plus <;> assumption

  lemma aval_rel_iff_aval : aval_rel a st n ↔ aval a st = n := ⟨aval_rel_is_aval, aval_is_aval_rel⟩

end q4_6

section q4_7
end q4_7
