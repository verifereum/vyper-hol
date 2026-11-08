(* Successful source returns provide a semantic output-write boundary.
   The static namespace proof instead uses the call/return arity premise
   of inliner_input_ok to bound all syntactic return rewrites. *)
Theory functionInlinerReturnBoundary
Ancestors
  functionInlinerOrigin functionInlinerDefs venomExecProofs
  venomExecSemantics venomState venomInst indexedLists rich_list list

Theorem inline_return_arity:
  !rvs pc s vals outs caller t.
    eval_operands (rvs ++ [pc]) s = SOME vals /\
    bind_outputs outs (FRONT vals) caller = SOME t ==>
    LENGTH rvs = LENGTH outs
Proof
  rpt strip_tac >> drule eval_operands_length >>
  gvs[bind_outputs_def] >> simp[listTheory.LENGTH_FRONT]
QED

Theorem inline_return_write_boundary:
  !inst rvs pc s vals outs caller t args ret pi ri x.
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
    inst.inst_operands = rvs ++ [pc] /\
    EVERY (\op. ~is_label_op op) rvs /\
    eval_operands (rvs ++ [pc]) s = SOME vals /\
    bind_outputs outs (FRONT vals) caller = SOME t /\
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) /\
    MEM x ri.inst_outputs ==>
    MEM x outs
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH rvs = LENGTH outs` by metis_tac[inline_return_arity] >>
  `FILTER (\op. ~is_label_op op) rvs = rvs` by simp[FILTER_EQ_ID] >>
  gvs[rewrite_inline_inst_def, is_param_opcode_def, TAKE_APPEND, MEM_MAPi] >>
  `TAKE (LENGTH outs) rvs = rvs` by simp[TAKE_LENGTH_TOO_LONG] >>
  gvs[] >> metis_tac[EL_MEM]
QED

Theorem inline_return_static_arity_bound:
  !inst outs.
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
    raw_return_user_arity inst = SOME (LENGTH (outs:string list)) ==>
    LENGTH (FILTER (\op. ~is_label_op op)
      (TAKE (LENGTH inst.inst_operands - 1) inst.inst_operands)) <=
    LENGTH outs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[callLayoutDefsTheory.raw_return_user_arity_def, AllCaseEqs()] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists `LENGTH (TAKE (LENGTH outs) inst.inst_operands)` >>
  simp[LENGTH_FILTER_LEQ, LENGTH_TAKE_EQ]
QED

Theorem inline_return_static_write_boundary:
  !inst outs args ret pi ri x.
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
    raw_return_user_arity inst = SOME (LENGTH outs) /\
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) /\
    MEM x ri.inst_outputs ==>
    MEM x outs
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (FILTER (\op. ~is_label_op op)
     (TAKE (LENGTH inst.inst_operands - 1) inst.inst_operands)) <= LENGTH outs`
    by metis_tac[inline_return_static_arity_bound] >>
  gvs[rewrite_inline_inst_def, is_param_opcode_def, MEM_MAPi] >>
  metis_tac[EL_MEM, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
