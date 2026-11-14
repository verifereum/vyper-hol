(* Count loads expose a common fragment/continuation ghost. *)
Theory decoderCountLoadCorePtr
Ancestors wordLoadStorePtr decoderSetupStepPtr decoderNavigationPtr calldataClampPtr typedCopyPtr
  bodyPtrDefs compileEnv loweringStateRelDefs emitHelper venomInst venomExecSemantics venomState
  words list rich_list arithmetic finite_map ptrDiscipline ptrSafeRun
  venomInstProofs codegenRel contextCodegenRel emitHelperProps exprLoweringProps
  fragExec decoderGhostFramePtr abiDecoderContract entryDispatchPtr instIdxIndep fragExecPtr

Theorem emit_count_load_endpoint_joint_core:
  !src sa out sb s t a G tn cx ctx PG R.
  emit_op CALLDATALOAD [src] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?HG u.
    (!D lower ctx' func. allocas_from lower s /\ ~ctx_has_dalloca ctx' ==>
      (!k. inst_seq_ptr D lower ctx' func PG G tn (emitted_insts sa sb)
        (s with vs_inst_idx := k) HG u)) /\
    (!D lower explicit ctx' func.
      ~s.vs_halted /\ fn_has_code sa sb func /\ allocas_from lower s /\
      lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx',func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,u)) /\
    frag_exec_ptr H cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = HG /\ z = u /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov HG out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG HG u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_calldata_load_endpoint_ptr_origin_core_joint >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl_tac [`HG`, `u`] >> simp[] >> metis_tac[]
QED

Theorem emit_count_load_endpoint_ptr_core:
  !src sa out sb s t a G tn cx ctx PG R.
  emit_op CALLDATALOAD [src] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?HG u. frag_exec_ptr H cx ctx PG sa sb
    (\g z v. g = G /\ z = tn /\ v = s)
    (\g z v. g = HG /\ z = u /\
      v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u out = {} /\ op_prov HG out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG HG u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_calldata_load_endpoint_ptr_origin_core_joint >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl_tac [`HG`, `u`] >> simp[] >> metis_tac[]
QED
