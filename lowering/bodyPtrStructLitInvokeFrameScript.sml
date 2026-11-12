(* Atomic INVOKE preserves caller provenance except instruction outputs.
   Callee memory and taint are intentionally opaque at this boundary. *)
Theory bodyPtrStructLitInvokeFrame
Ancestors ptrSafeRun fragGasPathPtr venomExecSemantics venomInst
  venomState finite_map pred_set fragExec

Theorem invoke_ghost_caller_provenance:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  x NOTIN set inst.inst_outputs ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = FLOOKUP G x
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  simp[FLOOKUP_DRESTRICT]
QED

Theorem invoke_edge_caller_provenance:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  x NOTIN set inst.inst_outputs ==>
  FLOOKUP G' x = FLOOKUP G x
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def] >>
  drule_all invoke_ghost_caller_provenance >>
  disch_then (qspecl_then [`tn`, `fuel`, `PG`, `G`] mp_tac) >>
  qpat_x_assum `(_,_) = ghost_step _ _ _ _ _ _ _` (mp_tac o GSYM) >>
  simp[]
QED

Theorem invoke_memory_return_edge_provenance:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_outputs = [] /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  G' = G
Proof
  strip_tac >> simp[fmap_eq_flookup] >> gen_tac >>
  `x NOTIN set inst.inst_outputs` by simp[] >>
  metis_tac[invoke_edge_caller_provenance]
QED

(* compile_call's memory-return branch uses emit_void INVOKE; the existing
   emitted_insts_emit_void theorem identifies its instruction as this
   output-free mk_inst.  No assumptions on the callee ghost are needed. *)
Theorem invoke_emitted_void_edge_provenance:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid INVOKE ops []) /\
  decode_invoke (mk_inst iid INVOKE ops []) = SOME (nm,argops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands argops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  G' = G
Proof
  strip_tac >>
  ` (mk_inst iid INVOKE ops []).inst_opcode = INVOKE /\
    (mk_inst iid INVOKE ops []).inst_outputs = []` by simp[mk_inst_def] >>
  metis_tac[invoke_memory_return_edge_provenance]
QED
