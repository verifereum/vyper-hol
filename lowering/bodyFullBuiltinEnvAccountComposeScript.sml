(* Child outcome composition for account accessors. *)
Theory bodyFullBuiltinEnvAccountCompose
Ancestors
  bodyFullPreds bodySimFull exprSimAccounts exprSimSource exprSimHypsDefs
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert bodyFullGhostFrame exprSimMemoryStack
  exprSimWordArgs exprLowering exprLoweringProps builtinSimple
  gasShadowCompileStmtHelpers gasShadowState gasShadow vyperTyping vyperTypeSystem vyperAST
  fragGasSeqPtr emitHelper emitHelperProps compileEnv allocaHistory
  vyperStorageTrace vyperStorageFootprint fragExec exprSimUnopComposeProps
  vyperContext list
Libs
  pairLib

Theorem account_full_from_suffix:
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
    op_taint tn x = {} /\ op_prov G x = NONE /\ ~ctx_has_dalloca ctx /\
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
    body_exprs_full_ok cx [e] /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Builtin (account_item_type item) (Acc item) [e]) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
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
  `?sx ss1. lower_value compile_expr cenv (BaseT AddressT)
      (gas_shadow_expr e) shadow_sa = (sx,ss1)` by metis_tac[pairTheory.PAIR] >>
  `sx = x /\ gas_shadow_state s1 ss1` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `BaseT AddressT`, `e` |-> `e`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
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
  `?xx sm. lower_value compile_expr cenv (BaseT AddressT)
      (gas_shadow_expr e) shadow_sa = (xx,sm) /\
    (case item of
       Balance => emit_op BALANCE [xx]
     | Codesize => emit_op EXTCODESIZE [xx]
     | Codehash => emit_op EXTCODEHASH [xx]
     | IsContract => comp_bind (emit_op EXTCODESIZE [xx])
                         (\c. emit_op GT [c; Lit 0w])
     | Address => comp_return xx | Code => comp_return xx) sm = (op,shadow_sb)` by
    (irule lower_value_acc >>
     conj_tac >- simp[] >>
     qexistsl_tac [`account_item_type item`, `ty`] >>
     gvs[gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  gvs[] >>
  rename1 `lower_value compile_expr cenv (BaseT AddressT)
    (gas_shadow_expr e) shadow_sa = (sx,ss1)` >>
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
  disch_then (drule_all_then assume_tac) >>
  `bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e]))
      (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (unop_result cx (account_item_type item) (Acc item)
                   [expr_type e] v ee,ee))` by
    (irule eval_expr_unop_action_general >>
     simp[builtin_args_length_ok_def]) >>
  pop_assum SUBST1_TAC >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >- simp[storage_trace_frame_def, exprSimUnopPropsTheory.unop_result_def]
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G' tn' t. childQ H res ee G' tn' t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [Abbr `childQ`] >>
  strip_tac >> disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
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
  qpat_x_assum `!item bs ee cx v x sa op sb func st0 cenv s ctx G tn DF lo d explicit PG. _`
    (drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac)) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `mid`,
    `INL (evaluate_account_op item l (lookup_account (word_of_bytes_be l) mid.accounts))`,
    `t'`, `tn'`] >>
  simp[exprSimUnopPropsTheory.unop_result_def, evaluate_builtin_def] >>
  qx_gen_tac `H` >> strip_tac >>
  `is_word_type (account_item_type item)` by
    (Cases_on `item` >> gvs[account_item_type_def, is_word_type_def]) >>
  `ptr_val_ok cx (account_item_type item)
    (evaluate_account_op item l (lookup_account (word_of_bytes_be l) mid.accounts))
    op G' tn' t'` by
    (irule bodyPtrDefsTheory.ptr_val_ok_word >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
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
  conj_tac
  >- (Cases_on `item` >>
      gvs[account_item_type_def, vyperValueTheory.evaluate_type_def] >>
      first_x_assum (qspec_then `BaseTV Uint256T` mp_tac) >>
      simp[vyperValueTheory.evaluate_type_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s1 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  simp[] >> conj_tac
  >- gvs[exprSimPropsTheory.locals_kept_mem_tail] >>
  conj_tac
  >- (irule exprSimPropsTheory.locals_kept_mem_tail >>
      qexists_tac `t` >> simp[]) >>
  strip_tac >> irule exprSimPropsTheory.pure_frame_mem_tail >>
  qexists_tac `t` >> simp[]
QED
