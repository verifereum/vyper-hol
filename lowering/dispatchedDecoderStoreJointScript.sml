(* Clean store: pointer coverage and actual memory bound are separate. *)
Theory dispatchedDecoderStoreJoint
Ancestors calldataWordStepsPtr calldataOverwritePtr dispatchedDecoderTrace
  bodyPtrDefs abiEncoder fragExec loweringStateRelDefs venomMemDefs instIdxIndep
  emitHelperProps venomExecSemantics venomInst venomState exprLoweringProps

Theorem clean_mstore_accepted_joint:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand v s = SOME w /\
  ptr_covers G tn p s 32 /\ op_taint tn v = {} /\ fresh_vars_wrt sa s /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ w2n dw + 32 <= s.vs_alloca_next ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z) /\
    ptr_covers H u p t 32 /\ mem_word_at (w2n dw) t.vs_memory = w /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u))
Proof
  strip_tac >> drule_all clean_mstore_overwrite_trace_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t.vs_vars = s.vs_vars` by
    (drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_write2_def,
       mk_inst_def, AllCaseEqs()] >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_vars`) >> simp[mstore_def]) >>
  `fresh_vars_wrt sb t` by
    (drule emitted_insts_emit_void >> strip_tac >> fs[fresh_vars_wrt_def]) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED
