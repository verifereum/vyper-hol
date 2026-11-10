(* Pointer ghost boundaries for primitive calldata word instructions. *)
Theory calldataWordStepsPtr
Ancestors calldataOverwritePtr ptrSafetyTransport valueEncodingProps calldataClampPtr calldataDecodePtr abiDecoderContract
  abiEncoder compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep

Theorem calldata_load_prefix_framed:
  emit_op CALLDATALOAD [src] sa = (v,sb) /\
  eval_operand src s = SOME sw /\ fresh_vars_wrt sa s /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    eval_operand v t = SOME (abi_decode_load CALLDATALOAD sw s) /\
    op_taint u v = {} /\ op_prov H v = NONE /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a w. eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule evaluated_operand_not_fresh >>
     goal_assum $ drule_at (Pat `eval_operand`) >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK loaded` >>
  drule_all calldata_load_overwrite_prefix >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `loaded = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ _ = OK loaded` mp_tac >> simp[]) >>
  `fresh_vars_wrt sb t` by fs[fresh_vars_wrt_def] >>
  `!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z` by
    (rpt strip_tac >>
     qpat_x_assum `!a z. eval_operand a s = SOME z ==> eval_operand a loaded = SOME z`
       drule >> simp[eval_op_inst_idx]) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[]
QED

Theorem clean_mstore_prefix_framed:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand v s = SOME w /\
  ptr_covers G tn p s 32 /\ op_taint tn v = {} /\ fresh_vars_wrt sa s /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all clean_mstore_overwrite_prefix >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `t.vs_vars = s.vs_vars` by
    (drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_write2_def,
       mk_inst_def, AllCaseEqs()] >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_vars`) >> simp[mstore_def]) >>
  `fresh_vars_wrt sb t` by
    (drule emitted_insts_emit_void >> strip_tac >> fs[fresh_vars_wrt_def]) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[]
QED
