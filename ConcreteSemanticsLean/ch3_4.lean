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
    case Times a b ha hb =>
      simp [aexp_times, aval]
      split
      case h_1 => simp_all only [aval]
      case h_2 x heq x_1 =>
        simp [*] at *; rw [← ha]
        split
        case h_1 x heq_1 => norm_num
        case h_2 x x_2 => simp; rw [← hb]
        case h_3 => simp; rw [hb]; rw [mul_comm]
      case h_3 x heq x_1 x_2 =>
        simp [*] at *; rw [← hb]
        split
        case h_1 x heq_1 => norm_num
        case h_2 x x_1 => simp; rw [← ha]
        case h_3 => simp; rw [<- ha]; apply Or.inl; rfl
      case h_4 => simp [*] at *

end ch3_4
