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
    induction a <;> simp
    case APlus x y ihx ihy =>
      simp [asimp_const]
      split
      · case h_1 x' y' numx' numy' => -- ANum x, ANum y case
        simp
        simp [numx'] at ihx;
        simp [numy'] at ihy;
        rw [ihx, ihy]
      · case h_2 => simp [asimp_const, ihx, ihy] -- Otherwise

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

  theorem APlus_0 : aval (APlus (ANum 0) a) st = aval a st := by simp

  theorem asimp_is_aval : aval (asimp a) st = aval a st := by
    induction a <;> simp [asimp]
    case APlus a b ha hb =>
      simp [aexp_plus, aval]
      split
      case h_1 => simp_all only [aval]
      case h_2 x heq x_1 =>
        simp [*] at *; rw [← ha]
        split
        case h_1 x heq_1 => norm_num; exact hb
        case h_2 x x_2 => simp; rw [← hb]; ring
      case h_3 x heq x_1 x_2 =>
        simp [*] at *; rw [← hb]
        split
        case h_1 x heq_1 => norm_num; exact ha
        case h_2 x x_1 => simp; rw [← ha]
      case h_4 => simp [*] at *


  /- Ch3.2 Boolean Expressions -/
  inductive bexp : Type
  | Bc   : Bool → bexp
  | BNot  : bexp → bexp
  | BAnd  : bexp → bexp → bexp
  | BLess : aexp → aexp → bexp
  deriving Repr
  open bexp

  @[simp] def bval (b : bexp) (st : state) : Bool :=
    match b with
    | Bc v        => v
    | BNot b      => ¬(bval b st)
    | BAnd b₁ b₂  => (bval b₁ st ∧ bval b₂ st)
    | BLess a₁ a₂ => (aval a₁ st < aval a₂ st)

  /- Ch3.2.1 Constant Folding -/
  def not (b : bexp) : bexp :=
    match b with
    | Bc true  => Bc false
    | Bc false => Bc true
    | _        => BNot b

  def and (b₁ b₂ : bexp) : bexp :=
    match b₁, b₂ with
    | Bc true, b₂ => b₂
    | b₁, Bc true => b₁
    | Bc false, _ => Bc false
    | _, Bc false => Bc false
    | _, _        => BAnd b₁ b₂

  def less (a₁ a₂ : aexp) : bexp :=
    match a₁, a₂ with
    | ANum n₁, ANum n₂ => Bc (n₁ < n₂)
    | _, _             => BLess a₁ a₂

  def bsimp (b : bexp) : bexp :=
    match b with
    | Bc v => Bc v
    | BNot b => not (bsimp b)
    | BAnd b₁ b₂ => and (bsimp b₁) (bsimp b₂)
    | BLess a₁ a₂ => less (asimp a₁) (asimp a₂)

end ch3_prelim

section ch3_1 -- p31
  open aexp
  def optimal (a : aexp) : Bool :=
    match a with
    | APlus x y =>
      match x, y with
      | ANum _, ANum _  => false
      | exp1, exp2   =>
        match optimal exp1, optimal exp2 with
        | true, true => true
        | _, _ => false
    | ANum _ => true
    | AString _ => true

  theorem asimp_const_is_optimal : optimal (asimp_const a) := by
    induction a <;> simp [optimal, asimp_const]
    case APlus =>
      split
      · case h_1 => simp [optimal] -- Adding two ANums
      · case h_2 left right ihleft ihright _ _ _ => simp [optimal, ihleft, ihright] -- Adding two other things
end ch3_1

section ch3_2 -- p31
end ch3_2

section ch3_3 -- p31
end ch3_3

section ch3_5 -- p32
end ch3_5

section ch3_6 -- p32
end ch3_6

section ch3_7 -- p33
  open aexp
  open bexp

  @[simp] def Eq' (a b: aexp) : bexp :=
    BAnd (BNot (BLess a b)) (BNot (BLess b a))

  def sam_st := (fun (_ : String) => (0 : ℤ ))
  #check sam_st
  #eval bval (Eq' (ANum 4) (ANum 6)) sam_st = (aval (ANum 4) sam_st == aval (ANum 6) sam_st)


  #eval Eq' (ANum 1) (ANum 1)
  def Le' (a b: aexp) : bexp := -- Being less than or equal to requires defining Or, which can be expressed in terms of `not`s and `and`s with De Morgan's i.e. (x + y) = (x'y')' where x and y are expressions in boolean algebra. Our x is "less than" and our y is "equal to"
    BNot (BAnd (BNot (BLess a b)) (BNot (Eq' a b)))

  theorem bval_eq_is_aval_equality : bval (Eq' a b) s = (aval a s - aval b s = 0) := by
    sorry
    /-
    induction a generalizing b <;> simp_all
    case ANum str => sorry



    sorry
    case AString => sorry
    case APlus => sorry
    -/

end ch3_7

section ch3_8
end ch3_8

section ch3_9
end ch3_9

section ch3_10
end ch3_10

section ch3_11
end ch3_11

section ch3_12
end ch3_12
