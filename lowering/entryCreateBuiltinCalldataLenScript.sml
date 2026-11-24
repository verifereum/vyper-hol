(* CALLDATASIZE has no child invocation. Its cut uses installed code alone;
   its scoped outcome preserves the physical result and ghosts of the leaf. *)
Theory entryCreateBuiltinCalldataLen
Ancestors
  bodyFullBuiltinEnvLength entryCreateFocusSpec entryCreateAdminSequence
  entryIntCallStageNeutral entryCreateCompletedCut exprSimFullBundleProps s1PrefixDefs
  exprSimCalldata exprSimHypsDefs vyperTypeBuiltins vyperTypeSystem gasSummary gasExplicitSites
  exprLoweringProps emitHelperProps emitHelper compileEnv abiEncoderProps
  fragExec venomInst venomState
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Theorem calldatalen_admin_layout[local]:
  lower_value compile_expr ce ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode = CALLDATASIZE) (emitted_insts sa sb)
Proof
  simp[lower_value_calldata_len] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  fs[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem calldatalen_value_selected[local]:
  expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (BaseT (UintT 256)) CalldataLen []) es
    (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (bind (eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen [])) (read_result cx))
    (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx (Builtin (BaseT (UintT 256)) CalldataLen [])
      (es,sa,sb,s0,op,G0,tn0)) (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen [])) (read_result cx)) (es,s0)
Proof
  strip_tac >>
  `lower_value compile_expr ce ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
   fn_has_code sa sb func /\ ~s0.vs_halted /\ create_operand_at sa s0` by
    fs[expr_sim_full_hypotheses_def, expr_sim_full_code_def, create_operand_at_def] >>
  drule calldatalen_admin_layout >> strip_tac >>
  reverse conj_tac
  >- (irule create_admin_sequence_cut >> fs[EVERY_MEM]) >>
  irule stage_scoped_initial_domain >>
  simp[storage_trace_frame_bind, cj 5 evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >> strip_tac >>
  drule_all calldatalen_full_witness >> strip_tac >>
  `t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
       by fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[expr_sim_full_post_def, expr_sim_full_endpoint_def]) >>
  `create_operand_full_scope sa sb (gas_explicit_sites ctx shctx) ctx func s0 [] (OK t)` by
    (`EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
                 i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by fs[EVERY_MEM] >>
     drule_all create_admin_sequence_scope >>
     qpat_assum `t.vs_inst_idx = _` (fn th => simp[NoAsms, GSYM th])) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (IntV &LENGTH cx.txn.calldata)`,`es`,`OK t`,`G'`,`tn'`] >>
  simp[calldata_source_all_tails, gas_explicit_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  fs[expr_sim_full_post_def]
QED

Theorem create_calldatalen_value_site:
  expr_body_pre ce cx env (Builtin ann CalldataLen args) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (Builtin ann CalldataLen args) es
    (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (bind (eval_expr cx (Builtin ann CalldataLen args)) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx (Builtin ann CalldataLen args)
      (es,sa,sb,s0,op,G0,tn0)) (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Builtin ann CalldataLen args)) (read_result cx)) (es,s0)
Proof
  strip_tac >>
  `args = [] /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, cj 9 well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> irule calldatalen_value_selected >>
  qexistsl_tac [`sha`,`shb`,`shfunc`,`ty`] >>
  fs[expr_sim_full_pre_def, expr_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  metis_tac[]
QED
