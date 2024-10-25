-- Doing this section with already defined functions was messing me up, so new file
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Basic

section ch3_4 -- p32
  inductive aexp : Type
  | ANum    : Int → aexp
  | AString : String → aexp
  | APlus   : aexp → aexp → aexp
  | Times   : aexp → aexp → aexp
  deriving Repr
  open aexp

  #eval ANum 5
  #eval AString "hello world"
  #eval APlus (AString "hello") (AString "world")
  #eval APlus (ANum 2) (Times (AString "hello") (ANum 3))

  def state : Type := String → Int

  @[simp] def aval (a : aexp) (st : state) : Int :=
    match a with
    | ANum n      => n
    | AString str => st str
    | APlus a1 a2 => aval a1 st + aval a2 st
    | Times a1 a2 => aval a1 st * aval a2 st

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
    | Times x y =>
      match asimp_const x, asimp_const y with
      | ANum x, ANum y => ANum (x * y)
      | x, y           => Times x y

  #eval asimp_const (Times (ANum 2) (ANum 3))
  #eval asimp_const (APlus (ANum 2) (asimp_const (Times (ANum 2) (ANum 8))))
  #eval asimp_const (APlus (ANum 2) (asimp_const (Times (ANum 2) (APlus (ANum 2) (ANum 8)))))

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
    case Times x t ihx ihy =>
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

  -- kyle was cooking here
  theorem aval_plus : aval (aexp_plus a b) st = aval a st + aval b st := by
    rcases a <;> rcases b <;> simp [aval, aexp_plus] <;> split <;> simp [aval] <;> ring

  def aexp_times (a b : aexp) : aexp :=
    match a, b with
    | ANum x, ANum y => ANum (x * y)
    | ANum x, a      =>
      match x with
      | 0 => ANum 0 -- 0 * a
      | 1 => a      -- 1 * a
      | _ => Times a (ANum x)
    | a, ANum x      =>
      match x with
      | 0 => ANum 0 -- 0 * a
      | 1 => a      -- 1 * a
      | _ => Times a (ANum x)
    | a, b           => Times a b

  -- kyle was cooking here (i literally only did substition on his work)
  theorem aval_times : aval (aexp_times a b) st = aval a st * aval b st := by
    rcases a <;> rcases b <;> simp [aval, aexp_times] <;> split <;> simp [aval] <;> ring

  def asimp (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | AString x => AString x
    | APlus a b => aexp_plus (asimp a) (asimp b)
    | Times a b => aexp_times (asimp a) (asimp b)

  theorem APlus_0 : aval (APlus (ANum 0) a) st = aval a st := by simp

  theorem ATimes_0 : aval (Times (ANum 0) a) st = 0 := by simp

  theorem ATimes_1 : aval (Times (ANum 1) a) st = aval a st := by simp

  -- might be worth trying to rewrite some of the def or removing entirely. idk how to solve!
  theorem asimp_is_asimp_const : aval (asimp a) = aval (asimp_const a) := by
    rcases a <;> simp [asimp, asimp_const, aexp_plus]
    case APlus a b => sorry
    case Times a b => sorry

  theorem asimp_is_aval : aval (asimp a) st = aval a st := by
    rcases a <;> simp [aval, asimp]
    case APlus x y =>
      rcases x <;> rcases y <;> simp [aval, aexp_plus, asimp] <;> split <;> sorry
    case Times x y => sorry
end ch3_4
