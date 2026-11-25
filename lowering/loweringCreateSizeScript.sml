Theory loweringCreateSize
Ancestors
  unitMemInv venomRunBounded venomCompilerTypes vyperState arithmetic

(* Backward reachability preserves the evaluated size even at a CREATE
   that aborts before taking an outcome. An oversized lowered site then
   contradicts nonexemption of the matched source evaluation. *)
Theorem lowered_entry_create_size_ok:
  !unit opt entry vs source_result.
    (?name fn lbl.
       opt.cu_context.ctx_entry = SOME name /\
       lookup_function name opt.cu_context.ctx_functions = SOME fn /\
       fn_entry_label fn = SOME lbl) /\
    (!obs. source_result obs <>
       INR (Error (RuntimeError "create initcode too large"))) /\
    (!fn inst s value off sz salt size.
       raw_reachable vs opt.cu_context fn inst s /\
       ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
        (inst.inst_opcode = CREATE2 /\
         inst.inst_operands = [value; off; sz; salt])) /\
       eval_operand sz s = SOME size ==>
       ?obs rfn ri rs rv ro rz rsl.
         raw_reachable (entry obs) unit.cu_context rfn ri rs /\
         ((ri.inst_opcode = CREATE /\ ri.inst_operands = [rv; ro; rz]) \/
          (ri.inst_opcode = CREATE2 /\ ri.inst_operands = [rv; ro; rz; rsl])) /\
         eval_operand rz rs = SOME size) /\
    (!obs fn inst s value off sz salt size.
       raw_reachable (entry obs) unit.cu_context fn inst s /\
       ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
        (inst.inst_opcode = CREATE2 /\
         inst.inst_operands = [value; off; sz; salt])) /\
       eval_operand sz s = SOME size /\
       2 * max_code_size < w2n size ==>
       source_result obs = INR (Error (RuntimeError "create initcode too large")))
    ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s) opt.cu_context vs
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  rewrite_tac[mem_inv_raw_reachable, inst_create_size_ok_def] >>
  BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rewrite_tac[GSYM NOT_LESS] >>
  disch_tac >>
  metis_tac[]
QED
