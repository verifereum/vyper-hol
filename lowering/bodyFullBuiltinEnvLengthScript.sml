(* Joint finite-horizon simulation for Len and CalldataLen. *)
Theory bodyFullBuiltinEnvLength
Ancestors
  bodyFullBuiltinEnvLen
  bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame gasOutcomeFullCompose
  bodySimFull exprSimHypsDefs vyperInterpreter vyperStorageTrace exprLoweringProps
  exprSimMemDefs exprSimWordArgs loweringPosts loweringSlice
  vyperStorageFootprint bodyPtrDefs venomExecSemantics stmtSimDefs valueEncoding
  exprSimLen exprSimCalldata exprSimSource exprSimProps exprSimOperands
  fragGasSeqPtr fragGasOriginPtr emitHelperProps allocaHistory
  loweringStateRelDefs ptrSafeRun ptrDiscipline instMemFrontier
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  vyperTypeSystem vyperTypeBuiltins list finite_map emitHelper compileEnv
  fragExec venomInst venomState

Theorem calldatalen_full_path:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE [] [out]) s =
    OK (update_var out w s)) ==>
  ?t G' tn'.
    t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s
          with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) /\
    tn' = step_taint (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> gvs[lower_value_calldata_len] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id CALLDATASIZE []
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s
          with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G inst (update_var (STRING #"%" (toString sa.cs_next_var)) w s),
      step_taint inst s (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn)` by
    (mp_tac (Q.INST [`i` |-> `inst`,
        `u` |-> `update_var (STRING #"%" (toString sa.cs_next_var)) w s`]
        straight_line_origin_ptr_edge) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
          ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def] >>
     simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke,
          update_var_def]) >>
  `~(update_var (STRING #"%" (toString sa.cs_next_var)) w s
       with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[update_var_def]
QED

Theorem calldatalen_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    bt = CalldataLen /\ builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `args = [] /\ a = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, expr_sim_pre_def, well_typed_expr_def,
        well_typed_builtin_app_def] >>
  gvs[] >>
  conj_asm1_tac
  >- (rw[expr_sim_full_def] >>
      irule gas_outcome_full_initial_domain >>
      simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
           storage_trace_frame_read_result] >>
      strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
        gvs[storage_trace_domain_def] >>
      `allocas_from lo s0` by metis_tac[ghost_inv_at_def] >>
      `!out. step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE [] [out]) s0 =
         OK (update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s0)` by
        (simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
         fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
            val_to_w256_def, integer_wordTheory.i2w_def] >> metis_tac[]) >>
      drule_all calldatalen_full_path >>
      disch_then (qspecl_then [`tn0`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `G0`]
        strip_assume_tac) >>
      irule gas_outcome_full_pure >> simp[] >>
      qexistsl_tac [`G'`, `es`, `INL (IntV &LENGTH cx.txn.calldata)`, `t`, `tn'`] >>
      simp[calldata_source_all_tails] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      gvs[lower_value_calldata_len] >>
      drule emitted_insts_emit_op >> strip_tac >>
      `sb.cs_current_bb = sa.cs_current_bb` by
        gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
            comp_ignore_bind_def, comp_return_def, emit_def] >>
      simp[expr_store_bound_def, vyperASTTheory.expr_type_def, is_word_type_def,
           update_var_def, alloca_history_def] >>
      `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
        (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      conj_tac >- suspend "word_post" >>
      conj_tac >- suspend "history" >>
      suspend "ghosts") >>
  irule expr_vv_sim_stack_full >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       compile_calldata_len_stack] >>
  MATCH_ACCEPT_TAC exprLoweringPropsTheory.eval_expr_builtin_value
QED

Resume calldatalen_builtin_sim_full[word_post]:
          irule expr_post_word_intro >>
          simp[vyperASTTheory.expr_type_def, is_word_type_def, word_value_def,
               eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
          simp[pure_frame_def] >>
          conj_tac
          >- (gvs[storage_well_formed_on_def] >>
              rpt gen_tac >> Cases_on `b`
              >- (first_x_assum (qspecl_then [`T`, `slot`, `tv`] mp_tac) >>
                  gvs[vyperStorageBackendTheory.get_storage_def]) >>
              first_x_assum (qspecl_then [`F`, `slot`, `tv`] mp_tac) >>
              gvs[vyperStorageBackendTheory.get_storage_def]) >>
          conj_tac
          >- (irule wb_frame_readonly_tail >>
              qexistsl_tac [`sa`, `s0`] >>
              simp[wb_frame_refl, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
          `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
            (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
          drule_all stmt_state_rel_update_var >>
          disch_then (qspec_then `val_to_w256 (IntV &LENGTH cx.txn.calldata)` mp_tac) >>
          simp[update_var_def] >> strip_tac >>
          `s0 with <|vs_vars := s0.vs_vars |+ (STRING #"%" (toString sa.cs_next_var),
               val_to_w256 (IntV &LENGTH cx.txn.calldata));
               vs_inst_idx := SUC (LENGTH sa.cs_current_insts)|> =
           (s0 with vs_vars := s0.vs_vars |+ (STRING #"%" (toString sa.cs_next_var),
               val_to_w256 (IntV &LENGTH cx.txn.calldata))) with
               vs_inst_idx := SUC (LENGTH sa.cs_current_insts)` by simp[] >>
          metis_tac[stmt_state_rel_inst_idx]
QED

Resume calldatalen_builtin_sim_full[history]:
      fs[alloca_history_def] >> rpt gen_tac >> strip_tac >>
          Cases_on `k < LENGTH sa.cs_current_insts`
          >- metis_tac[] >>
          `k = LENGTH sa.cs_current_insts` by decide_tac >> gvs[] >>
          drule_all fn_has_code_same_block >> strip_tac >>
          first_x_assum (qspec_then `0` mp_tac) >>
          simp[] >> strip_tac >> gvs[mk_inst_def]
QED

Resume calldatalen_builtin_sim_full[ghosts]:
      reverse conj_tac
      >- (simp[ptr_val_ok_def, is_word_type_def, ghost_kept_at_def,
              step_prov_def, out_prov_def, set_prov_def, op_prov_def,
              mk_inst_def, FLOOKUP_DRESTRICT,
              step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
              FLOOKUP_UPDATE, mem_taint_def, new_site_bytes_def,
              step_writes_def, source_memory_write_ranges_def,
              written_taint_def, range_bytes_def] >>
          rpt conj_tac >> rpt gen_tac >> strip_tac >>
          gvs[flookup_thm, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
      irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`] >>
      simp[lookup_var_def, FLOOKUP_UPDATE,
           step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
           FLOOKUP_DRESTRICT, step_taint_def, op_taint_def,
           set_var_taint_def, out_taint_def, mem_taint_def,
           new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
           written_taint_def, range_bytes_def, adopt_reset_def,
           store_taint_def, imm_taint_def] >>
      simp[pred_setTheory.EXTENSION, flookup_thm] >> metis_tac[]
QED

Finalise calldatalen_builtin_sim_full

Theorem length_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = Len \/ bt = CalldataLen) /\
    builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac
  >- (irule len_builtin_sim_full >> simp[] >> metis_tac[])
  >> irule calldatalen_builtin_sim_full >> simp[] >> metis_tac[]
QED
