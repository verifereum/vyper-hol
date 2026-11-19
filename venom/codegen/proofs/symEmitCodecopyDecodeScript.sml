(* Decode a prepared CODECOPY stack under an arbitrary label map. *)
Theory symEmitCodecopyDecode
Ancestors asmSymBridge asmSymSem asmSem venomState list option

Theorem asm_sym_codecopy_decode:
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
  eval_operands [dst; src; sz] vs = SOME (TAKE 3 cs.as_stack) ==>
  eval_operand dst vs = SOME dw /\ eval_operand sz vs = SOME nw /\
  sval_conc slo sw = eval_operand src vs /\ IS_SOME (eval_operand src vs)
Proof
  strip_tac >>
  gvs[LIST_REL_CONS1, sval_conc_def, eval_operands_def, AllCaseEqs()]
QED
