(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   rooted selfdestruct, including static rejection and certified overflow. *)
Theory bodyMemSelfDestruct
Ancestors
  bodyMemoryPreds exprSimAbortMemory exprSimSource selfdestructHalt
  exprSimMemDefs exprSimHypsDefs exprSimHyps exprSimDefs loweringPosts compileEnv
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperValue
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  gasExemptOrigin gasNormalPrefix fragGasMode fragGasPath fragGasPathMem gasStorage
  exprSimRawRevertCore exprSimSend exprLowering exprLoweringProps emitHelper emitHelperProps builtinSystem
  fragExec instMemFrontier memSafeRun gasCount
  vyperStorageTrace vyperStorageFootprint
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  supportedExprTraverse allocLimits vyperSystemControl
  venomExecSemantics venomExecProps venomInst venomState list rich_list
Libs
  pairLib

Theorem selfdestruct_mem_pre_arg[local]:
  !cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ expr_type e = BaseT AddressT /\
        expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `?e. args = [e] /\ expr_type e = BaseT AddressT` by
    gvs[expr_body_pre_def, well_typed_expr_def, LENGTH_EQ_NUM_compute] >>
  gvs[] >>
  gvs[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
      byte_widths_expr_def, alloc_limits_expr_def,
      expr_has_evm_run_thm, supported_expr_exists_def,
      supported_exprs_exists_every]
QED

Theorem selfdestruct_mem_compile[local]:
  !cenv ty ann e dflt sa vv sb.
    expr_type e = BaseT AddressT /\
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) ==>
    ?op sm. lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
      emit_inst SELFDESTRUCT [op] [] sm = ((),sb)
Proof
  rpt gen_tac >> simp[compile_expr_call, compile_call_def,
    compile_selfdestruct_def, emit_void_def] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> (simp[emitHelperTheory.emit_inst_def])
QED

Theorem selfdestruct_mem_exit_path[local]:
  !ctx func op sa sb t r.
    emit_inst SELFDESTRUCT [op] [] sa = ((),sb) /\
    fn_has_code sa sb func /\ ~t.vs_halted /\
    t.vs_current_bb = sa.cs_current_bb /\
    t.vs_inst_idx = LENGTH sa.cs_current_insts /\
    step_inst_base (mk_inst sa.cs_next_id SELFDESTRUCT [op] []) t = r /\
    exit_result r ==>
    gas_path_mem ctx func t 0 r
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst sa.cs_next_id SELFDESTRUCT [op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule (cj 3 gas_path_mem_rules) >> simp[] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, mk_inst_def,
       mem_safe_step_non_invoke, inst_dload_in_section_other,
       below_frontier_no_ranges] >>
  metis_tac[]
QED

Theorem selfdestruct_mem_vv[local]:
  expr_body_pre cenv cx env (Call ann SelfDestructTarget [e] dflt) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Call ann SelfDestructTarget [e] dflt) es
Proof
  strip_tac >>
  `expr_type e = BaseT AddressT /\ expr_body_pre cenv cx env e es` by
    (drule selfdestruct_mem_pre_arg >> simp[] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all selfdestruct_mem_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_selfdestruct_action] >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      simp[storage_trace_frame_selfdestruct_tail]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- suspend "bad_domain" >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE)) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      first_assum drule >> strip_tac >> gvs[]
      >- suspend "success" >> suspend "exception") >>
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_selfdestruct_action, ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Resume selfdestruct_mem_vv[bad_domain]:
  disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_selfdestruct_action] >>
  irule gas_bad_storage_at_bind_left >>
  simp[storage_trace_frame_selfdestruct_tail] >>
  irule gas_bad_storage_at_counted_prefix >> metis_tac[]
QED

Resume selfdestruct_mem_vv[success]:
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pos (el 2))
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  disch_then drule >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env _`
       (strip_assume_tac o PURE_REWRITE_RULE
         [expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
     first_assum ACCEPT_TAC) >>
  `value_has_type (BaseTV AddressT) v` by
    gvs[expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, evaluate_type_def] >>
  `eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    gvs[post_value_type_word, is_word_type_def, expr_val_rel_def,
        evaluate_type_def] >>
  drule address_typed_dest >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es.storage_trace` by
    (drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `gas_value_prefix (storage_trace_horizon es_end.storage_trace) T
     (ctx,func,cenv,cx) (expr_type e,e) (sa,sm,op)
     (es,s0) marks (v,es_end,t)` by simp[gas_value_prefix_def] >>
  `t.vs_call_ctx.cc_address = cx.txn.target /\
   t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
   t.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  Cases_on `cx.txn.is_static` >- suspend "static" >>
  Cases_on `selfdestruct_overflows cx
     (w2w (typed_val_to_w256 (BaseTV AddressT) v)) es_end.accounts`
  >- suspend "overflow" >> suspend "halt"
QED

Resume selfdestruct_mem_vv[exception]:
  Cases_on `res` >> gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  rewrite_tac[eval_selfdestruct_action] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def, halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def, halt_exit_def]
QED

Resume selfdestruct_mem_vv[static]:
  `step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) t =
     Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def] >>
  `gas_path_mem ctx func t 0
     (Abort ExHalt_abort (halt_state (set_returndata [] t)))` by
    (irule selfdestruct_mem_exit_path >> simp[exit_result_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
    `es_end`, `Abort ExHalt_abort (halt_state (set_returndata [] t))`] >>
  simp[exit_result_def, expr_exit_def, halt_exit_def] >>
  rewrite_tac[eval_selfdestruct_action] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def,
    selfdestruct_tail_def, bind_def, ignore_bind_def, lift_option_type_def,
    check_not_static_def, check_def, assert_def, raise_def, return_def]
QED

Resume selfdestruct_mem_vv[overflow]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`RuntimeError "transfer_value recipient overflow"`,
               `es_end`, `func`, `t`] >>
  irule gas_exempt_cert_origin >>
  rewrite_tac[gas_exempt_origin_def] >> disj2_tac >>
  qexistsl_tac [`storage_trace_horizon es_end.storage_trace`,
    `cenv`, `cx`, `ty`, `ann`, `e`, `dflt`, `sa`, `sb`, `sm`,
    `vv`, `op`, `v`, `w2w (typed_val_to_w256 (BaseTV AddressT) v)`] >>
  simp[]
QED

Resume selfdestruct_mem_vv[halt]:
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     ?u. step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) t = Halt u /\
         u.vs_returndata = [] /\
         halt_rel H cx
           (selfdestruct_final cx
             (w2w (typed_val_to_w256 (BaseTV AddressT) v))
             (es_end with gas_obs := [])) u` by
    (rpt strip_tac >> irule step_selfdestruct_halt_rel >> simp[] >>
     irule halt_rel_from_state_rel >>
     metis_tac[expr_post_def, stmt_state_rel_def]) >>
  first_assum drule >> strip_tac >>
  `gas_path_mem ctx func t 0 (Halt u)` by
    (irule selfdestruct_mem_exit_path >> simp[exit_result_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR HaltException`,
    `selfdestruct_final cx
      (w2w (typed_val_to_w256 (BaseTV AddressT) v)) es_end`, `Halt u`] >>
  conj_tac
  >- (rewrite_tac[eval_selfdestruct_action] >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def] >>
      gen_tac >>
      once_rewrite_tac[GSYM (cj 1 selfdestruct_final_fields)] >>
      irule selfdestruct_tail_halt >> simp[]) >>
  disj2_tac >> simp[exit_result_def, expr_exit_def, halt_exit_def,
    selfdestruct_final_def] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?u. _` drule >>
  simp[selfdestruct_final_def]
QED

Finalise selfdestruct_mem_vv

Theorem selfdestruct_expr_mem:
  !cx ann args dflt tops ctx func cenv env ty es.
    body_exprs_mem_ok cx args /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    expr_sim_mem ctx func cenv cx ty (Call ann SelfDestructTarget args dflt) es /\
    expr_vv_sim_mem ctx func cenv cx ty (Call ann SelfDestructTarget args dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  drule selfdestruct_mem_pre_arg >> strip_tac >> gvs[] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by
    (gvs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty
     (Call ann SelfDestructTarget [e] dflt) es` by
    (irule selfdestruct_mem_vv >> metis_tac[]) >>
  simp[] >> irule expr_sim_mem_of_aborting_vv >>
  simp[selfdestruct_no_success]
QED

Theorem body_selfdestruct_mem_case:
  !cx v24 es v25.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt gen_tac >> disch_tac >>
  rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  irule selfdestruct_expr_mem >> metis_tac[]
QED
