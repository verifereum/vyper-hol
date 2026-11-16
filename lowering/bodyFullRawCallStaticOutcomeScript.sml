(* Static CALL rejection: a single checked exit, before oracle adoption. *)
Theory bodyFullRawCallStaticOutcome
Ancestors
  bodyFullRawCallCallOrigin callReadinessPtr fragGasEmitCtrl
  exprSimRawCallCalldata gasOutcomeFull emitHelperProps
  exprSimDefs gasEvents gasCount fragExec exprLoweringProps
  oracleCallStepPtr ptrDiscipline ptrSafeRun memSafeRun unitTransformDefs
  venomExecSemantics venomInst venomState memLocDefs
  contextCodegenRel bodyPtrDefs gasSummary codegenRel

Theorem raw_call_static_value_outcome_full:
  emit_op CALL [gop;aop;vop;dp;dl;op;Lit(n2w cap)] sa = (ok,sc) /\
  inst = mk_inst sa.cs_next_id CALL [gop;aop;vop;dp;dl;op;Lit(n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)] /\
  fn_has_code sa sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ allocas_from lo s /\
  cx.txn.is_static /\ s.vs_call_ctx.cc_static /\
  ~flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  flags.rcf_max_outsize = cap /\
  0 < amount /\ amount < dimword(:256) /\ cap < dimword(:256) /\
  eval_operand gop s = SOME gw /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME (n2w amount) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\
  es.gas_obs = [] /\ storage_trace_domain cx st0 es.storage_trace /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G tn p s cap) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (cap = 0 \/ w2n ro + cap <= s.vs_alloca_next) /\
  (cap = 0 \/ lo <= w2n ro) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_raw_call cx flags target bytes amount gas) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))
Proof
  strip_tac >>
  `n2w amount <> (0w:256 word)` by simp[wordsTheory.n2w_11] >>
  `!fuel. step_inst fuel ctx inst s =
     Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
         eval_operand_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `sc.cs_current_bb = sa.cs_current_bb` by
       (drule emit_op_extends >> simp[same_blocks_def]) >>
     drule fn_has_code_same_block >>
     disch_then (qspec_then `[inst]` mp_tac) >> simp[] >> metis_tac[]) >>
  `access_ok 0 G func inst s` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`eval_operand dp s = SOME ao`, `eval_operand dl s = SOME az`,
        `eval_operand op s = SOME ro`, `cap < dimword(:256)`,
        `az <> 0w ==> _`, `cap <> 0 ==> _`, `inst = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule call_access_ok_ptr >>
     simp[mk_inst_def, eval_operand_def, wordsTheory.w2n_n2w] >>
     conj_tac >> strip_tac >> gvs[ptr_covers_def] >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `access_ok lo G func inst s` by
    (qpat_x_assum `access_ok 0 _ _ _ _` mp_tac >>
     simp[access_ok_def, mk_inst_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (irule call_taint_ok_ptr >>
     simp[mk_inst_def, source_memory_read_ranges_def, mem_read_ops_def,
          memory_range_of_operands_def, eval_operand_def]) >>
  `mem_safe_step 0 ctx inst s` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def,
         memory_range_of_operands_def, mk_inst_def, eval_operand_def,
         wordsTheory.w2n_n2w] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort (halt_state (set_returndata [] s)),G,tn)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!fuel. step_inst fuel ctx inst s = _`, `inst = _`,
        `lookup_block _ _ = SOME bb`, `get_instruction _ _ = SOME inst`,
        `~s.vs_halted`, `~ctx_has_dalloca ctx`, `alloca_inv s`, `allocas_from lo s`,
        `access_ok lo G func inst s`, `taint_ok func tn inst s`,
        `mem_safe_step 0 ctx inst s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule exit_inst_origin_ptr >> simp[exit_result_def] >>
     gvs[mk_inst_def, gas_events_step_def, gas_count_step_def,
         ptr_inst_ok_def]) >>
  simp[gas_outcome_full_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
    `es`, `Abort ExHalt_abort (halt_state (set_returndata [] s))`, `G`, `tn`] >>
  simp[gas_explicit_def, raw_call_static_value_abort,
       expr_exit_def, halt_exit_def, exit_result_def]
QED
