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

end ch3_prelim
open aexp

section ch3_1 -- p31
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

  -- replace all `x` with `a` in `e`
  def subst (str : String) (a e : aexp) : aexp :=
    match e with
    | AString x  => if x = str then a else e
    | APlus l r  => APlus (subst str a l) (subst str a r)
    | ANum _     => e

  -- def subop [DecidableEq aexp] (f : aexp → aexp) (a e : aexp) :=
  --   fun x => if x = a then e else f a

  -- notation f " ? " a " : " e => subop f a e

  #eval subst "x" (ANum 3) (APlus (AString "x") (AString "y"))
  -- #eval "x" ? (ANum 3) : (APlus (AString "x") (AString "y"))

  lemma subst_eval_is_eval_subst : ∀ (a e : aexp) (st : state) (str : String),
      aval (subst str a e) st = aval e (fun x => if x = str then aval a st else st x) := by
    intros a e st str
    induction e <;> simp [subst, aval]
    . split <;> rfl
    . case APlus e1 e2 ih1 ih2 => rw [ih1, ih2]

  lemma eq_aval_is_eq_subst_aval : ∀ (a₁ a₂ e : aexp) (st : state) (x : String),
    aval a₁ st = aval a₂ st → aval (subst x a₁ e) st = aval (subst x a₂ e) st := by
    intro a₁ a₂ e st x eq_aval
    induction e  <;> simp_all [subst, aval]; split <;> simp_all

  end ch3_3

section ch3_5 -- p32
end ch3_5

section ch3_6 -- p32
end ch3_6

section ch3_7
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
