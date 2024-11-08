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

  /- Ch3.3 Stack Machine and Compilation -/
  inductive instr : Type :=
  | LOADI : Int → instr
  | LOAD  : String → instr
  | ADD   : instr
  deriving Repr
  open instr

  def stack : Type := mylist Int

  /-
  Executes one instruction on the stack.
  -/
  @[simp] def exec1 (ins : instr) (st : state) (stk : stack) : stack :=
    match ins, st, stk with
    | LOADI n,  _, stk            => n :: stk
    | LOAD x , st, stk            => (st x) :: stk
    | ADD    ,  _, i :: j :: stk' => (i + j) :: stk'
    | ADD    ,  _, _              => stk -- needed to cover all cases (although this shouldnt happen)

  /-
  Executes the entire stack.
  -/
  @[simp] def exec (insl : mylist instr) (st : state) (stk : stack) : stack :=
    match insl, st, stk with
    | []         ,  _, stk => stk
    | ins :: insl, st, stk => exec insl st (exec1 ins st stk)

  @[simp] def comp (a : aexp) : mylist instr :=
    match a with
    | ANum n      => LOADI n :: []
    | AString s   => LOAD s :: []
    | APlus e₁ e₂ => comp e₁ ++ comp e₂ ++ ADD :: []


  lemma exec_append : exec (l₁ ++ l₂) st stk = exec l₂ st (exec l₁ st stk) := by
    induction l₁ generalizing l₂ st stk <;> simp_all [empty_concat]

  lemma exec_comp_equiv_aval : exec (comp a) st stk = (aval a st) :: stk := by
    induction a generalizing stk <;> simp_all [exec_append, add_comm]
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

  inductive lexp :=
  | Nl    : Int → lexp
  | Vl    : String → lexp
  | Plusl : lexp → lexp → lexp
  | LET   : String → lexp → lexp → lexp
  deriving Repr
  open lexp

  -- value of `LET x e₁ e₂` is bind `x` to `e₁`
  -- on `aval` of `e₂`, when `e₁` is found,
  -- replace with `x`
  -- essentially, replace all `x` with `e₁` in `e₂`
  def lval (l : lexp) (st : state) : Int :=
    match l with
    | Nl n      => n
    | Vl x      => st x
    | Plusl x y => lval x st + lval y st
    | LET x e₁ e₂ => lval e₂ (fun y => if y = x then lval e₁ st else st y)

  #eval lval (LET "x" (Nl 3) (Plusl (Vl "x") (Nl 5))) (fun _ => 0)
  #eval lval (LET "x" (Nl 3) (LET "y" (Nl 5) (Plusl (Vl "x") (Vl "y")))) (fun _ => 0)
  #eval lval (LET "y" (Nl 3) (LET "z" (Nl 5) (Plusl (Vl "x") (Vl "y")))) (fun _ => 0)

  -- stands for lexp_inline
  def linline (l : lexp) : aexp :=
    match l with
    | Nl n      => ANum n
    | Vl x      => AString x
    | Plusl x y => APlus (linline x) (linline y)
    | LET x e₁ e₂ => subst x (linline e₁) (linline e₂)

  lemma lval_is_aval_linline : ∀ (l : lexp) (st : state), lval l st = aval (linline l) st := by
    intro l st
    induction l generalizing st <;> simp_all [lval, aval, linline]
    case LET str a₁ a₂ lva₁ lva₂  =>
      rw [subst_eval_is_eval_subst]
  -- technically you can make it one line since you can move the rw into the simp_all
  -- but also it kinda ruins the fun, and doesn't really show why it works

end ch3_6

section ch3_7 -- p33
  open aexp
  open bexp

  def Eq' (a b: aexp) : bexp :=
    BAnd (BNot (BLess a b)) (BNot (BLess b a))

  def sam_st := (fun (_ : String) => (0 : ℤ ))
  #check sam_st
  #eval bval (Eq' (ANum 4) (ANum 6)) sam_st = (aval (ANum 4) sam_st == aval (ANum 6) sam_st)


  #eval Eq' (ANum 1) (ANum 1)
  def Le' (a b: aexp) : bexp := -- Being less than or equal to requires defining Or, which can be expressed in terms of `not`s and `and`s with De Morgan's i.e. (x + y) = (x'y')' where x and y are expressions in boolean algebra. Our x is "less than" and our y is "equal to"
    BNot (BAnd (BNot (BLess a b)) (BNot (Eq' a b)))

  theorem bval_eq_is_aval_eq : bval (Eq' a b) s = (aval a s = aval b s) := by
    simp
    rw [Int.eq_iff_le_and_ge, and_comm]

  theorem bval_le_is_aval_le : bval (Le' a b) s = (aval a s - aval b s ≤ 0) := by
    simp
    rw [le_iff_lt_or_eq]
end ch3_7

section ch3_8
end ch3_8

section ch3_9
  inductive pbexp : Type :=
  | VAR : String → pbexp
  | NEG : pbexp → pbexp
  | AND : pbexp → pbexp → pbexp
  | OR  : pbexp → pbexp → pbexp
  deriving Repr
  open pbexp

  @[simp] def pbval (p : pbexp) (sb : String → Bool) : Bool :=
    match p with
    | VAR x     => sb x
    | NEG b     => !(pbval b sb)
    | AND b₁ b₂ => (pbval b₁ sb ∧ pbval b₂ sb)
    | OR b₁ b₂  => (pbval b₁ sb ∨ pbval b₂ sb)

  /-
  Check if pbexp is an Negation Normal Form (nnf)
  where there are only NEG on VAR
  -/
  @[simp] def is_nnf (p : pbexp) : Bool :=
    match p with
    | VAR _       => true                   -- `VAR` is nnf
    | NEG (VAR _) => true                   -- `NEG` `VAR` is nnf
    | NEG _       => false                  -- `NEG` anything else is not
    | AND b₁ b₂   => is_nnf b₁ ∧ is_nnf b₂  -- `AND` is nnf if both are nnf
    | OR b₁ b₂    => is_nnf b₁ ∧ is_nnf b₂  -- `OR` is nnf if both are nnf

  #eval is_nnf (AND (VAR "x") (NEG (VAR "y")))
  #eval is_nnf (AND (VAR "x") (NEG (NEG (VAR "y"))))

  /-
  Convert pbexp into nnf as much as possible
  -/
  @[simp] def nnf (p : pbexp) : pbexp :=
    match p with
    | VAR x           => VAR x
    | NEG (VAR x)     => NEG (VAR x)
    | NEG (NEG b)     => nnf b
    | NEG (AND b₁ b₂) => OR (nnf (NEG b₁)) (nnf (NEG b₂))
    | NEG (OR b₁ b₂)  => AND (nnf (NEG b₁)) (nnf (NEG b₂))
    | AND b₁ b₂       => AND (nnf b₁) (nnf b₂)
    | OR b₁ b₂        => OR (nnf b₁) (nnf b₂)

  #eval nnf (AND (VAR "x") (NEG (VAR "y")))
  #eval nnf (AND (VAR "x") (NEG (NEG (VAR "y"))))
  #eval nnf (AND (VAR "x") (NEG (OR (VAR "y") (VAR "z"))))
  #eval nnf (AND (VAR "x") (NEG (AND (VAR "y") (VAR "z"))))

  @[simp] lemma pbval_neg : ∀ b, pbval (NEG b) sb = !(pbval b sb) := by simp_all

  /-
  THIS IS WRONG, `¬` is PROPOSITIONAL NEGATION, NOT BOOLEAN NEGATION
  -/
  @[simp] lemma pbval_neg_nnf' (p : pbexp) (sb : String → Bool) : pbval (nnf (NEG p)) sb = ¬(pbval (nnf p) sb) := by
    induction p <;> simp_all; case AND b1 b2 _ _ =>
    constructor
    . rintro (h1 | h2) <;> simp_all
    . intro h; by_cases (pbval (nnf b1) sb) <;> simp_all

  @[simp] lemma pbval_neg_nnf (p : pbexp) : pbval (nnf (NEG p)) sb = !pbval (nnf p) sb := by
    induction p <;> simp_all

  @[simp] lemma nnf_preserved : pbval (nnf b) sb = pbval b sb := by
    induction b <;> simp_all [nnf, pbval, pbval_neg, pbval_neg_nnf]

  def b : pbexp := VAR "x"
  #eval is_nnf (nnf b)

  /-
  Helper function to chec if `OR` appears after `AND`.
  -/
  @[simp] def conj_of_lit (p : pbexp) : Bool :=
    match p with
    | VAR _     => true
    | OR _ _    => false
    | NEG q     => conj_of_lit q
    | AND p₁ p₂ => conj_of_lit p₁ ∧ conj_of_lit p₂

  /-
  Check if pbexp is in Disjunctive Normal Form (dnf)
  if it is an nnf and no OR occurs below an AND
  -/
  @[simp] def is_dnf (p : pbexp) : Bool :=
    match is_nnf p with
    | false => false
    | true  =>
      match p with
      | VAR _     => true
      | NEG q     => is_dnf q
      | OR q₁ q₂  => is_dnf q₁ ∧ is_dnf q₂
      | AND q₁ q₂ => conj_of_lit q₁ ∧ conj_of_lit q₂

  #eval is_dnf (AND (VAR "x") (NEG (VAR "y")))
  #eval is_dnf (AND (VAR "x") (NEG (NEG (VAR "y"))))
    #eval is_nnf (AND (VAR "x") (NEG (NEG (VAR "y"))))

  /-
  Convert from nnf to dnf
  -/
  @[simp] def dnf_of_nnf (p : pbexp) : pbexp :=
    match p with
    | VAR x     => VAR x
    | NEG q     => NEG (dnf_of_nnf q)
    | OR q₁ q₂  => OR (dnf_of_nnf q₁) (dnf_of_nnf q₂)
    | AND q₁ q₂ =>
      match dnf_of_nnf q₁, dnf_of_nnf q₂ with
      | OR q₁₁ q₁₂, q₂         => OR (AND q₁₁ q₂) (AND q₁₂ q₂)
      | q₁        , OR q₂₁ q₂₂ => OR (AND q₁ q₂₁) (AND q₁ q₂₂)
      | q₁        , q₂         => AND q₁ q₂

  #eval dnf_of_nnf (AND (VAR "x") (NEG (VAR "y")))
  #eval dnf_of_nnf (AND (VAR "x") (NEG (NEG (VAR "y"))))
  #eval dnf_of_nnf (AND (VAR "x") (OR (VAR "y") (VAR "z")))

  @[simp] lemma dnf_of_nnf_preserved : pbval (dnf_of_nnf b) sb = pbval b sb := by
    induction b <;> simp_all [dnf_of_nnf, pbval]
    case AND b1 b2 _ _ =>
      split <;> simp_all
      case h_1 =>
        by_cases (pbval (dnf_of_nnf b1) sb) <;> simp_all
        by_cases (pbval (dnf_of_nnf b2) sb) <;> simp_all
      case h_2 =>
        by_cases (pbval (dnf_of_nnf b1) sb) <;> simp_all

  lemma dnf_of_nnf_conversion : is_nnf b → is_dnf (dnf_of_nnf b) := by
    intro h; contrapose! h; induction b <;> simp_all

end ch3_9

section ch3_10
  open instr
  /-
  Executes one instruction on the stack.
  -/
  @[simp] def exec1_310 (ins : instr) (st : state) (stk : stack) : Option stack :=
    match ins, st, stk with
    | LOADI n,  _, stk            => some (n :: stk)
    | LOAD x , st, stk            => some ((st x) :: stk)
    | ADD    ,  _, i :: j :: stk' => some ((i + j) :: stk')
    | ADD    ,  _, _              => none -- stack underflow

  /-
  Executes the entire stack.
  -/
  @[simp] def exec_310 (insl : mylist instr) (st : state) (stk : stack) : Option stack :=
    match insl, st, stk with
    | []         ,  _, stk => some stk
    | ins :: insl, st, stk =>
      match (exec1_310 ins st stk) with
      | some exec1_stack => exec_310 insl st exec1_stack
      | none => none -- a stack underflow previously occurred and the stack is completely invalid

  def bind (k: α → Option α) (x: Option α) : Option α :=
  match x with
  | some x => k x
  | none => none

  lemma exec_append_310 : exec_310 (l₁ ++ l₂) st stk = bind
   (exec_310 l₂ st) (exec_310 l₁ st stk)
    := by
    induction l₁ generalizing stk
    case nil => rfl
    case cons ins l₁ ih =>
      simp_all
      split
      case h_1 => rfl
      case h_2 => rfl

  lemma exec_comp_equiv_aval_310 : match (exec_310 (comp a) st stk) with
  | some exec_stack => exec_stack = (aval a st) :: stk
  | none => exec_stack = none := by
    induction a generalizing stk <;> simp_all [exec_append, add_comm]
    sorry

end ch3_10

section ch3_11
end ch3_11

section ch3_12
end ch3_12
