import ConcreteSemanticsLean.cslib
import Init.Prelude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Basic

section ch3_prelim
  /- Ch3.1.1, Syntax -/
  -- Arithmetic EXPression
  inductive aexp : Type
  | ANum    : Int → aexp
  | AString : String → aexp
  | APlus   : aexp → aexp → aexp
  deriving Repr
  open aexp

  #eval ANum 5
  #eval AString "hello world"
  #eval APlus (AString "hello") (AString "world")
  #eval APlus (ANum 2) (APlus (AString "hello") (ANum 3))

  /- Ch3.1.2, Semantics -/
  -- `val` is `Int`
  -- `vname` is `String`
  -- `state` is `vname → val` or `String → Int`
  def state : Type := String → Int

  @[simp] def aval (a : aexp) (st : state) : Int :=
    match a with
    | ANum n      => n
    | AString str => st str
    | APlus a1 a2 => aval a1 st + aval a2 st

  #eval aval (APlus (ANum 3) (AString "x")) (fun _ => 0)

  -- def upst (a b : Int) (u : st) :=
  --   match a, b with
  --   | 0, 0

  -- notation "f(" a " := " b ")" => sorry

  /- Ch3.1.3, Constant Folding -/
  def asimp_const (a : aexp) : aexp :=
    match a with
    | ANum z      => ANum z
    | AString z   => AString z
    | APlus x y =>
      match asimp_const x, asimp_const y with
      | ANum x, ANum y => ANum (x + y)
      | x, y           => APlus x y

  #eval asimp_const (APlus (ANum 2) (ANum 3))
  #eval asimp_const (APlus (ANum 2) (asimp_const (APlus (ANum 1) (ANum 8))))
  #eval asimp_const (APlus (ANum 2) (asimp_const (APlus (ANum 1) (APlus (ANum 1) (ANum 8)))))

  theorem asimp_const_is_aval : ∀ (a : aexp) (st : state), (aval (asimp_const a) st) = (aval a st) := by
    intro a st
    induction a
    case ANum => simp
    case AString => simp
    case APlus x y ihx ihy =>
      simp [asimp_const]
      split
      · case h_1 _ _ x' y' numx' numy' => -- ANum x, ANum y case
        simp
        simp [numx'] at ihx;
        simp [numy'] at ihy;
        rw [ihx, ihy]
      · case h_2 _ _ _ => simp [asimp_const, ihx, ihy] -- Otherwise

  def aexp_plus (a b : aexp) : aexp :=
    match a, b with
    | ANum x, ANum y => ANum (x + y)
    | ANum x, a      =>
      match x with
      | 0 => a
      | _ => APlus a (ANum x)
    | a, ANum x      =>
      match x with
      | 0 => a
      | _ => APlus a (ANum x)
    | a, b           => APlus a b

  -- holy shit im cooking wtf !!!!!!
  theorem aval_plus : aval (aexp_plus a b) st = aval a st + aval b st := by
    rcases a <;> rcases b <;> simp [aval, aexp_plus] <;> split <;> simp [aval] <;> ring

  def asimp (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | AString x => AString x
    | APlus a b => aexp_plus (asimp a) (asimp b)

  theorem APlus_0 : aval (APlus (ANum 0) a) st = aval a st := by rcases a <;> simp

  -- might be worth trying to rewrite some of the def or removing entirely. idk how to solve!
  theorem asimp_is_asimp_const : aval (asimp a) = aval (asimp_const a) := by
    rcases a <;> simp [asimp, asimp_const, aexp_plus]
    case APlus a b => sorry

  theorem asimp_is_aval : aval (asimp a) st = aval a st := by
    rcases a <;> simp [aval, asimp]
    case APlus x y =>
      rcases x <;> rcases y <;> simp [aval, aexp_plus, asimp] <;> split <;> sorry

  /- Ch3.2 Boolean Expressions -/

end ch3_prelim

section ch3_1 -- p31

end ch3_1

section ch3_2 -- p31
end ch3_2

section ch3_3 -- p31
end ch3_3

section ch3_4 -- p32
end ch3_4

section ch3_5 -- p32
end ch3_5

section ch3_6 -- p32
end ch3_6
