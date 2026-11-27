(* Child outcome composition for account accessors. *)
Theory bodyFullBuiltinEnvAccountCompose
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull exprSimAccounts exprSimSource exprSimHypsDefs
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert bodyFullGhostFrame exprSimMemoryStack
  exprSimWordArgs exprSimWordBuiltins exprBopLowering exprLowering exprLoweringProps builtinSimple
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  gasShadowCompileStmtHelpers gasShadowState gasShadow vyperTyping vyperTypeSystem vyperAST
  fragGasSeqPtr emitHelper emitHelperProps compileEnv allocaHistory
  vyperStorageTrace vyperStorageFootprint fragExec exprSimUnopComposeProps
  vyperContext vyperState vyperInterpreter list bodyFullUnaryValueCompose
  venomInst venomState codegenRel contextCodegenRel unitTransformDefs
  ptrDiscipline memSafeRun ptrSafeRun fragGasOriginPtr
  bodyPtrDefs stateRelProj
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]
Libs
  pairLib

Theorem self_codesize_full_path[local]:
  lower_value compile_expr cenv ty
      (Builtin (BaseT (UintT 256)) (Acc Codesize) [e1]) sa = (op,sb) /\
  is_self_addr e1 /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [out]) s =
    OK (update_var out w s)) ==>
  ?t G' tn'.
    t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s
          with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id CODESIZE []
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) /\
    tn' = step_taint (mk_inst sa.cs_next_id CODESIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> fs[exprSimAccountsTheory.lower_value_self_codesize] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[] >> gen_tac >>
  mp_tac (Q.INST [`opc` |-> `CODESIZE`, `args` |-> `[]:operand list`,
                  `a` |-> `sa`, `b` |-> `sb`, `w` |-> `w`,
                  `D` |-> `D`, `lo` |-> `lo`, `ctx` |-> `ctx`,
                  `func` |-> `func`, `PG` |-> `PG`, `G` |-> `G`,
                  `tn` |-> `tn`, `s` |-> `s`, `explicit` |-> `explicit`]
    typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_emit_op_path) >>
  simp[is_terminator_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
       ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  simp[GSYM mk_inst_def, venomExecSemanticsTheory.step_inst_non_invoke,
       update_var_def] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >> gvs[]
QED

Theorem self_codesize_sim_full[local]:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty es.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    expr_body_pre_mods mods cenv cx env
      (Builtin (BaseT (UintT 256)) (Acc Codesize)
        [Builtin (BaseT AddressT) (Env SelfAddr) []]) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (BaseT (UintT 256)) (Acc Codesize)
        [Builtin (BaseT AddressT) (Env SelfAddr) []]) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_sim_full_def] >>
  irule gas_outcome_full_initial_domain >>
  simp[storage_trace_frame_bind, cj 5 evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `allocas_from lo s0` by metis_tac[ghost_inv_at_def] >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    metis_tac[stateRelProjTheory.stmt_state_rel_state_rel,
              stateRelProjTheory.state_rel_call_ctx_rel] >>
  `s0.vs_code = cx.txn.code` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (ACCEPT_TAC o
       MATCH_MP (cj 3 (iffLR loweringStateRelDefsTheory.accounts_rel_def)) o
       MATCH_MP (cj 6 (iffLR loweringStateRelDefsTheory.state_rel_def)) o
       MATCH_MP stmt_state_rel_state_rel o CONJUNCT1)) >>
  `LENGTH cx.txn.code < dimword (:256)` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     fs[expr_body_pre_split_def, expr_body_pre_mods_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.context_well_typed_def, wordsTheory.dimword_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [out]) s0 =
      OK (update_var out (n2w (LENGTH cx.txn.code)) s0)` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read0_def] >>
  `is_self_addr (Builtin (BaseT AddressT) (Env SelfAddr) [])` by
    simp[is_self_addr_def] >>
  drule_all self_codesize_full_path >>
  disch_then (qspecl_then [`tn0`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `G0`]
    strip_assume_tac) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`, `es`, `INL (IntV (&LENGTH cx.txn.code))`, `t`, `tn'`] >>
  simp[exprSimAccountsTheory.self_codesize_source_bind_all_tails] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  gvs[exprSimAccountsTheory.lower_value_self_codesize, exprSimMemDefsTheory.expr_store_bound_def, expr_type_def,
      is_word_type_def, update_var_def, alloca_history_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[] >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac >- suspend "self_word_post" >>
  conj_tac >- suspend "self_history" >>
  suspend "self_ghosts"
QED

Resume self_codesize_sim_full[self_word_post]:
  irule expr_post_word_intro >>
  simp[expr_type_def, is_word_type_def, loweringSliceTheory.word_value_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[loweringPostsTheory.pure_frame_def] >>
  conj_tac
  >- (gvs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
      rpt gen_tac >> Cases_on `b` >>
      gvs[vyperStorageBackendTheory.get_storage_def] >>
      metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_def,
                vyperStorageBackendTheory.get_storage_def]) >>
  conj_tac
  >- (irule wb_frame_readonly_tail >>
      qexistsl_tac [`sa`, `s0`] >>
      simp[wb_frame_refl, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  drule_all stmt_state_rel_update_var >>
  disch_then (qspec_then `val_to_w256 (IntV (&LENGTH cx.txn.code))` mp_tac) >>
  simp[update_var_def] >> strip_tac >>
  `s0 with <|vs_vars := s0.vs_vars |+ (STRING #"%" (toString sa.cs_next_var),
       val_to_w256 (IntV (&LENGTH cx.txn.code)));
       vs_inst_idx := SUC (LENGTH sa.cs_current_insts)|> =
   (s0 with vs_vars := s0.vs_vars |+ (STRING #"%" (toString sa.cs_next_var),
       val_to_w256 (IntV (&LENGTH cx.txn.code)))) with
       vs_inst_idx := SUC (LENGTH sa.cs_current_insts)` by simp[] >>
  `n2w (LENGTH cx.txn.code) = val_to_w256 (IntV (&LENGTH cx.txn.code))` by
    simp[valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def] >>
  metis_tac[stmt_state_rel_inst_idx]
QED

Resume self_codesize_sim_full[self_history]:
  fs[alloca_history_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `k < LENGTH sa.cs_current_insts`
  >- metis_tac[] >>
  `k = LENGTH sa.cs_current_insts` by decide_tac >> gvs[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_inst_def]
QED

Resume self_codesize_sim_full[self_ghosts]:
  conj_tac
  >- (match_mp_tac ghost_inv_at_exterior_frame >>
      qexistsl_tac [`es`, `G0`, `tn0`, `s0`, `sa`] >>
      simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
           step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
           finite_mapTheory.FLOOKUP_DRESTRICT, step_taint_def, op_taint_def,
           set_var_taint_def, out_taint_def, mem_taint_def,
           new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
           written_taint_def, range_bytes_def, adopt_reset_def,
           store_taint_def, imm_taint_def] >>
      simp[pred_setTheory.EXTENSION, finite_mapTheory.flookup_thm] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono])
  >- (conj_tac
      >- (simp[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def,
               step_prov_def, out_prov_def, set_prov_def, op_prov_def,
               mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT,
               finite_mapTheory.FDOM_DRESTRICT,
               step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
               finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DEF,
               pred_setTheory.EXTENSION, mem_taint_def, new_site_bytes_def,
               step_writes_def, source_memory_write_ranges_def,
               written_taint_def, range_bytes_def])
      >- (irule bodyPtrEnvBuiltinsEdgesTheory.single_output_ghost_kept_at >>
          simp[bodyPtrDefsTheory.ghost_kept_at_def,
               bodyPtrEnvBuiltinsEdgesTheory.step_taint_no_memory_effect,
               mk_inst_def, source_memory_write_ranges_def,
               written_taint_def, update_var_def] >>
          metis_tac[]))
QED

Finalise self_codesize_sim_full

Theorem account_full_from_suffix:
  !mods exps.
  (!item bs ee cx v x sa op sb func st0 cenv s ctx G tn DF lo d explicit PG.
    item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed ee.accounts /\
    unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
      (BytesV bs) ee = INL v /\
    (case item of
       Balance => emit_op BALANCE [x]
     | Codesize => emit_op EXTCODESIZE [x]
     | Codehash => emit_op EXTCODEHASH [x]
     | IsContract => comp_bind (emit_op EXTCODESIZE [x])
                        (\c. emit_op GT [c; Lit 0w])
     | Address => comp_return x | Code => comp_return x) sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    storage_trace_domain cx st0 ee.storage_trace /\ local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    op_taint tn x = {} /\ op_prov G x = NONE /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) ==>
    ?t G' tn'.
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      local_ptrs_reserved cenv sb /\ alloca_history func t /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p)) /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      (!tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
        eval_operand op t = SOME (typed_val_to_w256 tv v)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,G',tn') /\
        stmt_state_rel H ctx func cenv cx ee t /\
        storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty item e es.
    item <> Code /\ expr_type e = BaseT AddressT /\
    body_exprs_full_ok_mods mods exps cx [e] /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env
      (Builtin (account_item_type item) (Acc item) [e]) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_self_codesize (Acc item) [e]`
  >- (`item = Codesize /\
       ?self_ty. e = Builtin self_ty (Env SelfAddr) []` by
        (Cases_on `item` >> gvs[is_self_codesize_def] >>
         qpat_x_assum `is_self_addr e` mp_tac >>
         rewrite_tac[is_self_addr_def] >>
         Cases_on `e` >> gvs[is_self_addr_def] >>
         Cases_on `b` >> gvs[is_self_addr_def] >>
         Cases_on `l` >> Cases_on `e` >> gvs[is_self_addr_def] >>
         qexists_tac `t`) >>
      gvs[account_item_type_def, vyperASTTheory.expr_type_def] >>
      irule self_codesize_sim_full >> metis_tac[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT AddressT) e es` by
    (gvs[body_exprs_full_ok_def] >>
     metis_tac[body_expr_full_ok_def]) >>
  rw[expr_sim_full_def] >>
  drule_all lower_value_acc >> strip_tac >>
  rename1 `lower_value compile_expr cenv (BaseT AddressT) e sa = (x,s1)` >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`cx`, `env`, `es`] mp_tac) >>
     simp[is_word_type_def]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (Cases_on `item` >>
     gvs[comp_return_def, cs_extends_refl, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac emit_op_extends_next_var >>
     metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >>
     qexistsl_tac [`account_item_type item`, `Acc item`] >>
     simp[builtin_args_length_ok_def]) >>
  `~is_self_codesize (Acc item) [gas_shadow_expr e]` by
    (qpat_x_assum `~is_self_codesize (Acc item) [e]` mp_tac >>
     simp[is_self_codesize_def, gasShadowCompileHelpersTheory.gas_shadow_self_addr]) >>
  `?xx sm. lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
      (gas_shadow_expr e) shadow_sa = (xx,sm) /\
    (case item of
       Balance => emit_op BALANCE [xx]
     | Codesize => emit_op EXTCODESIZE [xx]
     | Codehash => emit_op EXTCODEHASH [xx]
     | IsContract => comp_bind (emit_op EXTCODESIZE [xx])
                         (\c. emit_op GT [c; Lit 0w])
     | Address => comp_return xx | Code => comp_return xx) sm = (op,shadow_sb)` by
    (irule lower_value_acc >>
     conj_tac
     >- simp[]
     >- (conj_tac
         >- simp[]
         >- (qexistsl_tac [`account_item_type item`, `ty`] >>
             gvs[gas_shadow_expr_def, gas_shadow_builtin_def]))) >>
  gvs[] >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (sx,ss1)` >>
  `sx = x /\ gas_shadow_state s1 ss1` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = (x,s1)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _`
       (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `sx = x` (SUBST_ALL_TAC o SYM) >>
  `fn_has_code shadow_sa ss1 shadow_func` by
    (qpat_assum `_ ss1 = (op,shadow_sb)` mp_tac >>
     qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` mp_tac >>
     qpat_assum `item <> Code` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `item` >>
     gvs[comp_return_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emit_op_extends >>
     gvs[fn_has_code_def, emitted_blocks_def, same_blocks_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.IS_PREFIX_TRANS]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  simp[] >> disch_then (drule_all_then assume_tac) >>
  `bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e]))
      (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (unop_result cx (account_item_type item) (Acc item)
                   [expr_type e] v ee,ee))` by
    (irule eval_expr_unop_action_general >>
     simp[builtin_args_length_ok_def]) >>
  pop_assum SUBST1_TAC >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_unary_value >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  reverse (rpt conj_tac)
  >~ [`storage_trace_frame _`] >- simp[storage_trace_frame_def, exprSimUnopPropsTheory.unop_result_def]
  >~ [`!H res ee HG tm t. childQ H res ee HG tm t ==> ?v. res = INL v`]
  >- (simp[Abbr `childQ`] >> rpt strip_tac >> goal_assum (drule_at Any))
  >- (simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type,
          exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`,`v`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [Abbr `childQ`] >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` mp_tac) >> simp_tac (srw_ss()) [listTheory.APPEND_NIL] >>
     qpat_assum `res = INL v` (fn th => rewrite_tac [th])) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (irule expr_body_pre_word_value >>
     conj_tac >- simp[is_word_type_def] >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                     `mid with gas_obs := []`] >>
     simp[SF ETA_ss] >>
     qpat_assum `expr_body_pre cenv cx env e es` mp_tac >>
     simp[expr_body_pre_def]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_sim_inv cenv cx env (mid with gas_obs := [])` suffices_by simp[] >>
     irule (cj 1 expr_body_pre_eval) >>
     qexistsl_tac [`e`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `INL (BytesV l)`] >>
     simp[SF ETA_ss] >>
     qpat_assum `expr_body_pre cenv cx env e es` mp_tac >>
     simp[expr_body_pre_def]) >>
  `accounts_well_typed mid.accounts` by gvs[expr_sim_inv_def] >>
  `op_taint tn1 sx = {} /\ op_prov G1 sx = NONE` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def, loweringPostsTheory.post_value_type_word,
          is_word_type_def]) >>
  `unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
      (BytesV l) mid = INL (evaluate_account_op item l
        (lookup_account (word_of_bytes_be l) mid.accounts))` by
    simp[exprSimUnopPropsTheory.unop_result_def, evaluate_builtin_def] >>
  `eval_operand sx t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV l))` by
    (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
          loweringPostsTheory.post_value_type_word,
          is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
          stmt_state_rel H ctx func cenv cx mid t /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
       CONJUNCT1)) >>
  qpat_x_assum `!item bs ee cx v x sa op sb func st0 cenv s ctx G tn DF lo d explicit PG. _`
    (drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac)) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `mid`,
    `INL (evaluate_account_op item l (lookup_account (word_of_bytes_be l) mid.accounts))`,
    `t'`, `tn'`] >>
  simp[exprSimUnopPropsTheory.unop_result_def, evaluate_builtin_def,
       exprSimDefsTheory.halt_exit_def] >>
  qx_gen_tac `H` >> strip_tac >>
  `is_word_type (account_item_type item)` by
    (Cases_on `item` >> gvs[account_item_type_def, is_word_type_def]) >>
  `ptr_val_ok cx (account_item_type item)
    (evaluate_account_op item l (lookup_account (word_of_bytes_be l) mid.accounts))
    op G' tn' t'` by
    (irule bodyPtrDefsTheory.ptr_val_ok_word >> simp[]) >>
  qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  simp[] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
     (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
      qpat_assum `!p. not_fresh_at s1 p ==> _` mp_tac >>
      qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
      qpat_assum `tn'.t_mem = tn1.t_mem` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      gvs[bodyPtrDefsTheory.ghost_kept_at_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_x_assum `mid.gas_obs = []` (fn th => rewrite_tac [GSYM th]) >> simp[]) >>
  simp[expr_type_def, exprSimMemDefsTheory.expr_store_bound_word] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  simp[loweringPostsTheory.expr_post_def, expr_type_def,
       loweringPostsTheory.post_value_type_word,
       loweringPostsTheory.expr_val_at_def,
       loweringPostsTheory.expr_val_rel_def] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  simp[] >>
  conj_tac
  >- (Cases_on `item` >>
         gvs[account_item_type_def, vyperValueTheory.evaluate_type_def] >>
         first_x_assum (qspec_then `BaseTV Uint256T` mp_tac) >>
       simp[vyperValueTheory.evaluate_type_def]) >>
  conj_tac
  >- (qx_genl_tac [`kept`,`value_word`] >> strip_tac >>
      `not_fresh_at s1 kept` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_assum `!p. not_fresh_at s1 p ==> lookup_var p t' = _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!p w. not_fresh_at sa p /\ lookup_var p s0 = SOME w ==> _`
        (qspecl_then [`kept`,`value_word`] mp_tac) >> simp[]) >>
  simp[] >> conj_tac
  >- gvs[exprSimPropsTheory.locals_kept_mem_tail] >>
  conj_tac
  >- (irule exprSimPropsTheory.locals_kept_mem_tail >>
      qexists_tac `t` >> simp[]) >>
  strip_tac >> irule exprSimPropsTheory.pure_frame_mem_tail >>
  qexists_tac `t` >> simp[]
QED
