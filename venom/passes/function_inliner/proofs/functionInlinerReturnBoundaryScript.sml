(* Successful source returns, rather than all syntactic returns, bound the
   output indices introduced by inlining. *)
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
