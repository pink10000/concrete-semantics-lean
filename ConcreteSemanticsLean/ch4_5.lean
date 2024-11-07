import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Basic

/- Ch4.5.1 : An Example: Even Numbers -/
section ch4_5_1

  inductive ev : ℕ → Prop :=
  | ev0   : ev 0
  | evSS  : ev n → ev (n + 2)
  open ev

  theorem ev_4 : ev 4 := evSS (evSS ev0)
  example : ev 0 → ev (0 + 2) → ev ((0 + 2) + 2) = ev 4 := by simp

  /- Rule Induction -/
  def evn (n : ℕ) :=
    match n with
    | 0 => True
    | Nat.succ 0 => False
    | Nat.succ (Nat.succ n) => evn n
  #check evn

  example : ev m → evn m := by
    intro evm
    induction evm -- rule induction
    case ev0 => simp [evn]
    case evSS m' _ evn_m =>
      simp [ev, evn]; exact evn_m

  example : ev m → ev (m - 2) := by
    intro h
    induction h <;> simp[ev]
    . apply ev0
    . assumption

  example : ev n → ev (Nat.succ (Nat.succ n)) := by
    intro evn; induction evn
    . exact (evSS ev0)
    . exact (evSS (by assumption))

  example : ev (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := evSS (evSS ev0)
  example : ev (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
    apply evSS; apply evSS; apply ev0


  lemma evn_is_ev : evn n → ev n := by
    intro evn_n; induction n
    . sorry
    . sorry


  /- Ch4.5.2 The Reflexive Transitive Closure -/
  inductive star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl {x : α} : star r x x
  | step {x y z : α} (h₁ : r x y) (h₂ : star r y z) : star r x z

  @[simp] lemma star_trans : star r x y → star r y z → star r x z := by
    intro xy yz
    induction xy
    . exact yz
    . case step x' y' z' x'y' _ z'z_y'z =>
      exact star.step x'y' (z'z_y'z yz)

  /- Ch4.5.3 The General Case -/
end ch4_5_1


section q4_2
end q4_2

section q4_3
end q4_3

section q4_4
end q4_4

section q4_5
end q4_5

section q4_6
end q4_6

section q4_7
end q4_7
