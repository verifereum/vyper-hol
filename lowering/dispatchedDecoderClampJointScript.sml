(* Accepted scalar clamp with its actual shared-ghost trace. *)
Theory dispatchedDecoderClampJoint
Ancestors calldataClampPtr dispatchedDecoderTrace abiDecoderContract
  abiDecoderClamp abiEncoder fragExec loweringStateRelDefs venomMemDefs instIdxIndep

Theorem calldata_clamp_accepted_joint:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  eval_operand op s = SOME w /\ abi_decoder_clamp_valid clamp w /\
  fresh_vars_wrt sa s /\ op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_inv s ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s'.vs_memory = s.vs_memory /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    (!a v. eval_operand a s = SOME v ==> eval_operand a s' = SOME v) /\
    fresh_vars_wrt sb s' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv s' /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK s',G',tn'))
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule evaluated_operand_not_fresh >>
     goal_assum $ drule_at (Pat `eval_operand`) >> simp[]) >>
  drule_all abi_decoder_clamp_sequence >> strip_tac >>
  drule_all calldata_clamp_overwrite_trace_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >>
  simp[fresh_vars_wrt_def, eval_op_inst_idx] >>
  fs[fresh_vars_wrt_def, alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def] >> metis_tac[]
QED
