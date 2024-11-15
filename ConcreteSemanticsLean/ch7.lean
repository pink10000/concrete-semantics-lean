import Init.Prelude
import ConcreteSemanticsLean.ch3

section ch7_1

  inductive com : Type
  | SKIP
  | Assign (vname: String) (exp: aexp)
  | Seq (cmd1: com) (cmd2: com)
  | If (exp: bexp) (cmd1: com) (cmd2: com)
  | While (exp: bexp) (cmd: com)
  deriving Repr

  open com
  open aexp
  open bexp

  notation x " ::= " a => (Assign x a)
  notation c1 " ;; " c2 => (Seq c1 c2)
  notation "IF " b " THEN " c1 " ELSE " c2 => (If b c1 c2)
  notation "WHILE " b " DO " c => (While b c)

  def test_com1 := "var1" ::= APlus (AString "x") (ANum 5)
  #eval test_com1

  def test_com2 := WHILE Bc true DO test_com1
  #eval test_com2

  #eval test_com1 ;; test_com2

  inductive big_step : (com × state) → state → Prop :=
  | Skip        : big_step (SKIP, s) s
  | Assign      : big_step (x ::= a, s) (s(x := (aval a s)))
  | Seq         : big_step (c1, s1) s2 → big_step (c2, s2) s3 → big_step (c1 ;; c2, s1) s3
  | IfTrue      : bval b s → big_step (c1, s) t → big_step (IF b THEN c1 ELSE c2, s) t
  | IfFalse     : !(bval b s) → big_step (c2, s) t → big_step (IF b THEN c1 ELSE c2, s) t
  | WhileFalse  : !(bval b s) → big_step (WHILE b DO c, s) s
  | WhileTrue   : bval b s1 → big_step (c, s1) s2 → big_step (WHILE b DO c, s2) s3 → big_step (WHILE b DO c, s1) s3
end ch7_1
