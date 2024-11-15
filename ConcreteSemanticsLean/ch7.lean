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

  -- Propositions about state after executing a command
  inductive big_step : (com × state) → state → Prop :=
  | Skip        : big_step (SKIP, s) s
  | Assign      : big_step (x ::= a, s) (s(x := (aval a s)))
  | Seq         : big_step (c1, s1) s2 → big_step (c2, s2) s3 → big_step (c1 ;; c2, s1) s3
  | IfTrue      : bval b s → big_step (c1, s) t → big_step (IF b THEN c1 ELSE c2, s) t
  | IfFalse     : !(bval b s) → big_step (c2, s) t → big_step (IF b THEN c1 ELSE c2, s) t
  | WhileFalse  : !(bval b s) → big_step (WHILE b DO c, s) s
  | WhileTrue   : bval b s1 → big_step (c, s1) s2 → big_step (WHILE b DO c, s2) s3 → big_step (WHILE b DO c, s1) s3
  open big_step

  notation tuple "⟹" state => big_step tuple state
  -- Prove that this example if true statement ends in the state where x = 1
  namespace test_big_step
    def start_state: state := (fun (_: String) => (0: Int))
    def terminate_state: state := (start_state("x" := (aval (ANum 1) start_state)))
    def test_bool_prop : bval (Bc true) start_state = true := by
      simp

    def test_c1 := "x" ::= ANum 1
    def test_c2 := SKIP
    def test_assign_prop : ("x" ::= ANum 1, start_state) ⟹ terminate_state :=
      Assign

    theorem if_true_ends_in_term_state : (IF (Bc true) THEN test_c1 ELSE test_c2, start_state) ⟹ terminate_state := IfTrue test_bool_prop test_assign_prop

    -- what is the equivalent to code_pred in lean?
    -- #eval ["x", "y"].map (("x" ::= ANum 1, start_state) ⟹ terminate_state)
  end test_big_step

  theorem seq_assoc_bidirectional : ((c1 ;; c2 ;; c3, s) ⟹ t) ↔ ((c1 ;; (c2 ;; c3), s) ⟹ t) := by
    constructor <;> intro h <;> cases h <;> case Seq s1 c1_s1 seq_t => apply big_step.Seq; exact c1_s1; exact seq_t

  def equiv_c (c1: com) (c2: com) : Prop :=
    ∀ s t, ((c1, s) ⟹ t) = ((c2, s) ⟹ t)

  notation c1 "~" c2 => equiv_c c1 c2

  theorem equiv_rfl: c ~ c := by
    intro s t
    rfl

  theorem equiv_sym: (c ~ c') → (c' ~ c) := by
    intro h s t
    rw [h]

  example : (WHILE b DO c) ~ IF b THEN c;; WHILE b DO c ELSE SKIP := by
    intro s t
    simp
    constructor
    · intro h
      cases h
      case WhileFalse bfalse => apply big_step.IfFalse; exact bfalse; exact big_step.Skip
      case WhileTrue s2 btrue c_s2 while_t => apply big_step.IfTrue; exact btrue; exact big_step.Seq c_s2 while_t
    · intro h
      cases h
      case IfTrue btrue seq_t => apply big_step.WhileTrue; exact btrue; apply big_step.Seq at seq_t; repeat sorry
      case IfFalse bfalse skip_t => sorry
      -- apply big_step.WhileFalse; exact bfalse; exact big_step.Seq c_s2 while_t


end ch7_1
