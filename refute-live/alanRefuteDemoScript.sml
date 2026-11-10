Theory alanRefuteDemo
Ancestors memLocDefs venomInst

Theorem helper_log_zero:
  inst.inst_opcode = LOG /\ inst.inst_operands = [Lit 0w; opn; opd] ==> mem_read_ops inst = NONE
Proof
  cheat
QED

Theorem helper_add_assoc:
  !a b c. (a:num) + (b + c) = (a + b) + c
Proof
  cheat
QED

Theorem demo_add_comm:
  !a b. (a:num) + b = b + a
Proof
  cheat
QED

(* Independent concrete counterexample: zero topics still reads memory. *)
Theorem helper_log_zero_counterexample:
  let inst = mk_inst 0 LOG [Lit 0w; Lit 0w; Lit 0w] [] in
    inst.inst_opcode = LOG /\
    inst.inst_operands = [Lit 0w; Lit 0w; Lit 0w] /\
    mem_read_ops inst <> NONE
Proof
  EVAL_TAC
QED
