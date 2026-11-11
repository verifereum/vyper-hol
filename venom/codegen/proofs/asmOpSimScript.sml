(*
 * Per-Opcode ASM Simulation Lemmas (Layer 3)
 *
 * Shows that for each pure opcode, executing one asm_steps step
 * with AsmOp produces the expected stack result via asm_{binop,unop,ternop}.
 *
 * KEY LEMMAS:
 *   asm_step_one         -- single-step asm_steps reduction
 *   asm_step_asmop       -- AsmOp dispatches to asm_step_op
 *   binop_asm_step       -- parametric: binop one-step simulation
 *   unop_asm_step        -- parametric: unop one-step simulation
 *   ternop_asm_step      -- parametric: ternop one-step simulation
 *   asm_step_op_arith    -- arith group dispatch to asm_step_op
 *   asm_step_op_compare  -- compare group dispatch to asm_step_op
 *   asm_step_op_bitwise  -- bitwise group dispatch to asm_step_op
 *   b2w_eq_bool_to_word  -- bridge between asm b2w and Venom bool_to_word
 *
 * USAGE: To show e.g. ADD simulation, combine:
 *   simp[asm_step_op_def, asm_step_arith_def] (resolves dispatch)
 *   then binop_asm_step (gives the stack result)
 *
 * Or use asm_step_op_arith to go from asm_step_arith SOME to asm_step_op.
 *)


Theory asmOpSim
Ancestors
  asmSem stackModel codegenRel venomExecSemantics list
Libs
  BasicProvers

(* ===== Bridge: b2w = bool_to_word ===== *)

Theorem b2w_eq_bool_to_word:
  !b. b2w b = bool_to_word b : bytes32
Proof
  Cases >> EVAL_TAC
QED

(* ===== Single-step asm_steps reduction ===== *)

Theorem asm_step_one:
  !lo otp prog s1.
    s1.as_pc < LENGTH prog ==>
    asm_steps lo otp prog 1 s1 =
      asm_step lo otp (EL s1.as_pc prog) s1
Proof
  rw[] >>
  `1 = SUC 0` by decide_tac >>
  pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def] >>
  Cases_on `asm_step lo otp (EL s1.as_pc prog) s1` >>
  simp[asm_steps_def]
QED

(* ===== AsmOp dispatches to asm_step_op ===== *)

Theorem asm_step_asmop:
  !lo otp name s1.
    asm_step lo otp (AsmOp name) s1 = asm_step_op otp name s1
Proof
  simp[asm_step_def]
QED

(* ===== Group dispatch: from asm_step_arith/compare/bitwise to asm_step_op ===== *)

(* If asm_step_arith returns SOME, asm_step_op returns the same result *)
Theorem asm_step_op_arith:
  !otp name s1 r.
    asm_step_arith name s1 = SOME r ==>
    asm_step_op otp name s1 = r
Proof
  rw[asm_step_op_def] >>
  Cases_on `asm_step_arith name s1` >> gvs[]
QED

(* If asm_step_compare returns SOME (and arith returns NONE),
   asm_step_op returns the same result *)
Theorem asm_step_op_compare:
  !otp name s1 r.
    asm_step_arith name s1 = NONE /\
    asm_step_compare name s1 = SOME r ==>
    asm_step_op otp name s1 = r
Proof
  rw[asm_step_op_def] >>
  Cases_on `asm_step_arith name s1` >> gvs[]
QED

(* If asm_step_bitwise returns SOME (and arith/compare return NONE),
   asm_step_op returns the same result *)
Theorem asm_step_op_bitwise:
  !otp name s1 r.
    asm_step_arith name s1 = NONE /\
    asm_step_compare name s1 = NONE /\
    asm_step_bitwise name s1 = SOME r ==>
    asm_step_op otp name s1 = r
Proof
  rw[asm_step_op_def] >>
  Cases_on `asm_step_arith name s1` >> gvs[] >>
  Cases_on `asm_step_compare name s1` >> gvs[]
QED

(* ===== Parametric simulation: binop ===== *)

(* If name dispatches to asm_binop f via asm_step_op, and the asm stack
   has a::b::stk, then one asm_steps step produces f a b :: stk. *)
Theorem binop_asm_step:
  !f name lo otp prog s1 a b stk.
    asm_step_op otp name s1 = asm_binop f s1 /\
    s1.as_stack = a :: b :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_binop_def]
QED

(* ===== Parametric simulation: unop ===== *)

Theorem unop_asm_step:
  !f name lo otp prog s1 a stk.
    asm_step_op otp name s1 = asm_unop f s1 /\
    s1.as_stack = a :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_unop_def]
QED

(* ===== Parametric simulation: ternop ===== *)

Theorem ternop_asm_step:
  !f name lo otp prog s1 a b c stk.
    asm_step_op otp name s1 = asm_ternop f s1 /\
    s1.as_stack = a :: b :: c :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b c :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_ternop_def]
QED

(* ===== Convenience: combined dispatch + step ===== *)

(* Go from group dispatch SOME + stack shape directly to asm_steps result.
   Proved uniformly via the parametric lemmas above. *)

Theorem arith_binop_asm_step:
  !f name lo otp prog s1 a b stk.
    asm_step_arith name s1 = SOME (asm_binop f s1) /\
    s1.as_stack = a :: b :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_binop_def]
QED

Theorem compare_binop_asm_step:
  !f name lo otp prog s1 a b stk.
    asm_step_compare name s1 = SOME (asm_binop f s1) /\
    asm_step_arith name s1 = NONE /\
    s1.as_stack = a :: b :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_binop_def]
QED

Theorem bitwise_binop_asm_step:
  !f name lo otp prog s1 a b stk.
    asm_step_bitwise name s1 = SOME (asm_binop f s1) /\
    asm_step_arith name s1 = NONE /\
    asm_step_compare name s1 = NONE /\
    s1.as_stack = a :: b :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_binop_def]
QED

Theorem compare_unop_asm_step:
  !f name lo otp prog s1 a stk.
    asm_step_compare name s1 = SOME (asm_unop f s1) /\
    asm_step_arith name s1 = NONE /\
    s1.as_stack = a :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_unop_def]
QED

Theorem bitwise_unop_asm_step:
  !f name lo otp prog s1 a stk.
    asm_step_bitwise name s1 = SOME (asm_unop f s1) /\
    asm_step_arith name s1 = NONE /\
    asm_step_compare name s1 = NONE /\
    s1.as_stack = a :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_unop_def]
QED

Theorem arith_ternop_asm_step:
  !f name lo otp prog s1 a b c stk.
    asm_step_arith name s1 = SOME (asm_ternop f s1) /\
    s1.as_stack = a :: b :: c :: stk /\
    s1.as_pc < LENGTH prog /\
    EL s1.as_pc prog = AsmOp name ==>
    asm_steps lo otp prog 1 s1 =
      AsmOK (asm_next (s1 with as_stack := f a b c :: stk))
Proof
  rw[asm_step_one, asm_step_asmop, asm_step_op_def, asm_ternop_def]
QED
