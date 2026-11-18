(*
 * Rule branches of the final assembly optimizer that no oracle fixture
 * reaches, each compared with the pinned Python function on the same list.
 * The fixtures themselves are compared, compiled with asm_opt_finalizer,
 * against bytecode/python-o1-asm-opt by the native parity runner
 * (bytecode/native/README.md).
 *
 * Covered: the stack peepholes other than SWAPn SWAPn and SWAP1
 * <commutative>, the fall-through after a SWAPn SWAPn deletion, the ends of
 * the list where Python raises IndexError (NONE here), and _merge_jumpdests'
 * LABEL x LABEL y case.
 *)
Theory asmOptimizerChecks
Ancestors asmOptimizer

Theorem asm_opt_peephole_dup1_swap2_swap1:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "SWAP1"; AsmOp "DUP2"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_dup1_swap1_pop:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"; AsmOp "STOP"; AsmOp "CALLER"] =
    SOME ([AsmOp "STOP"; AsmOp "CALLER"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_pop_pop:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"; AsmOp "STOP"] =
    SOME ([AsmOp "POP"; AsmOp "POP"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_commutative:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"; AsmOp "ADD"; AsmOp "STOP"] =
    SOME ([AsmOp "ADD"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_dup1_swap1:
  stack_peephole_opts
    [AsmOp "SWAP3"; AsmOp "SWAP3"; AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "DUP1"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_dup1_swap1:
  stack_peephole_opts
    [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "STOP"] =
    SOME ([AsmOp "DUP1"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_commutative:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "MUL"; AsmOp "STOP"] =
    SOME ([AsmOp "MUL"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap1_lowercase_commutative:
  stack_peephole_opts
    [AsmOp "SWAP1"; AsmOp "add"; AsmOp "STOP"] =
    SOME ([AsmOp "add"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_swap1_at_end:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "SWAP1"] =
    NONE
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_swap_pair_then_dup1_at_end:
  stack_peephole_opts
    [AsmOp "SWAP2"; AsmOp "SWAP2"; AsmOp "DUP1"] =
    NONE
Proof
  EVAL_TAC
QED

Theorem asm_opt_peephole_no_match:
  stack_peephole_opts
    [AsmOp "CALLER"; AsmOp "SWAP1"; AsmOp "SUB"; AsmOp "STOP"] =
    SOME ([AsmOp "CALLER"; AsmOp "SWAP1"; AsmOp "SUB"; AsmOp "STOP"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_label:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "b"; AsmPushLabel "a"; AsmOp "JUMP"] =
    ([AsmLabel "a"; AsmLabel "b"; AsmPushLabel "b"; AsmOp "JUMP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_same_label:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "a"; AsmPushLabel "a"; AsmOp "JUMPI"] =
    ([AsmLabel "a"; AsmLabel "a"; AsmPushLabel "a"; AsmOp "JUMPI"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_label_unused:
  merge_jumpdests
    [AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"] =
    ([AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"], F)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_renames_earlier_push:
  merge_jumpdests
    [AsmPushLabel "a"; AsmOp "JUMP"; AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"] =
    ([AsmPushLabel "b"; AsmOp "JUMP"; AsmLabel "a"; AsmLabel "b"; AsmOp "STOP"], T)
Proof
  EVAL_TAC
QED

Theorem asm_opt_merge_jumpdests_label_jump:
  merge_jumpdests
    [AsmLabel "a"; AsmPushLabel "b"; AsmOp "JUMP"; AsmPushLabel "a"; AsmOp "JUMPI"] =
    ([AsmLabel "a"; AsmPushLabel "b"; AsmOp "JUMP"; AsmPushLabel "b"; AsmOp "JUMPI"], T)
Proof
  EVAL_TAC
QED
