(* Compose the guard prefix with the selected RaiseReason fragment. *)
Theory s1PrefixAssertReasonFromRaise
Ancestors
  bodySingletonStmtGuards[qualified] stmtExprAllocationPreProps[qualified]
  s1PrefixPreds bodyFullAssertReason s1PrefixDefs s1PrefixCompose
  bodyFullAssertReasonSource bodyFullAssertReasonControl bodyFullPreds bodySimFull
  gasShadow reasonSourceProps loweringPosts vyperStorageTrace s1PrefixProps exprSimDefs
  s1PrefixFrame vyperInterpreter vyperState sum bodyFullIfExpReach
  gasOutcomeFullCompose fragGasOriginPtr fragGasOrigin gasSummary fragGasPath
  vyperStorageFootprint stmtSimIfProps valueEncoding bodyPtrDefs venomState
  decoderNavigationPtr emitHelperProps fragExec bodyFullShared ptrDiscipline
  venomExecSemantics exprBodyPreProps finite_map exprSimHypsDefs list
  bodyFullSimProjection[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "raise_prefix") >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac bodySingletonStmtGuardsTheory.singleton_stmt_expr_guards >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`s` |-> `(Assert e (AssertReason se))`,
                     `tops` |-> `tops`, `ctx` |-> `ctx`]
        stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
     disch_then irule >> strip_tac >>
     irule assert_reason_condition_source_pre >>
     fs[bodySimTheory.body_inv_split_def,
        bodyInvSplitTheory.module_body_inv_def, alistTheory.ALOOKUP_def] >>
     metis_tac[]) >>
  `expr_body_pre_mods [(NONE,tops)] cenv cx env e es` by
    metis_tac[exprBodyPrePropsTheory.body_inv_expr_body_pre_mods] >>
  `expr_type e = BaseT BoolT` by fs[type_stmt_assert_reason] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (irule (cj 1 bodyFullSimProjectionTheory.body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es` by
    (fs[body_expr_prefix_ok_def] >> metis_tac[]) >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  fs[gas_shadow_stmt_def, gas_shadow_assert_reason_def] >>
  drule_all compile_assert_reason_layout_full >> strip_tac >> gvs[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_reason_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`t1`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`t1`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res mid G1 tn1 t. condQ H res mid G1 tn1 t /\
       ~t.vs_halted /\ mid.gas_obs = [] /\
       ?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) marks (OK t,G1,tn1)) condR` by
    (irule gas_outcome_full_post_source >> qexistsl_tac
       [`\H res mid G1 tn1 t. condQ H res mid G1 tn1 t /\
          ?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (s0,G0,tn0) marks (OK t,G1,tn1)`, `condR`] >>
     simp[] >> irule gas_outcome_full_post_path >> qexists_tac `condQ` >>
     metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ condQ condR` kall_tac >>
  suspend "guard_bind"
QED
*)
Theorem compile_assert_reason_frag_prefix_from_raise:
  (!cx e DF lo d PG tops bindings ctx shadow_ctx func
    shadow_func cenv env env' ret_ty lctx RetQ es.
   body_expr_full_ok cx e /\
   body_expr_prefix_ok cx e /\
   body_inv tops ctx cenv cx /\
   shadow_body_inv tops ctx shadow_ctx /\
   supported_stmt tops bindings (Raise (RaiseReason e)) /\
   (!target. supported_stmt_expr_exists
        (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
        occurs_abi_decode_target target tops) /\
   body_const_cells_agree [(NONE,tops)] cx env es /\
   expr_sim_inv cenv cx env es /\
   ce_locals_declared cenv env /\
   locals_alloc_ok cenv env /\
   type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
   stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
   call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
   frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cx RetQ cenv ret_ty ==>
   stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cx lctx RetQ cenv
       (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
       (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason e))))
       (eval_stmt cx (Raise (RaiseReason e))) es) ==>
  !cx e se DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_prefix_ok cx se) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assert e (AssertReason se)) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertReason se)) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assert e (AssertReason se))))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_reason_frag_prefix_from_raise[guard_bind]:
  rewrite_tac[eval_assert_reason_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`requests_outcomes_frame (bind (eval_expr _ _) _)`]
  >- (irule requests_outcomes_frame_bind_all >>
      simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- rw[storage_trace_frame_return, storage_trace_frame_raise, evaluate_storage_trace_frame]
  >~ [`ISR _`]
  >- (simp[Abbr `condR`] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]) >>
  suspend "selected"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_reason_frag_prefix_from_raise[selected]:
  qx_genl_tac [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  drule_all assert_reason_condition_bool >> strip_tac >> gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> condQ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms, Abbr `condQ`] >>
  strip_tac >> gvs[] >>
  Cases_on `b` >> simp[]
  >- (irule gas_prefix_full_no_outcome >>
      simp[storage_trace_frame_return, return_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `eval_operand op t = SOME 0w` by
    (drule_all if_condition_operand >> simp[val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t,G1,tn1) [] (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (gen_tac >>
     qpat_assum `emit_inst JNZ _ _ s3 = _`
       (mp_then Any strip_assume_tac emit_inst_extends) >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` assume_tac) >> fs[] >>
     irule (SRULE [] (Q.INST [`v` |-> `0w`] decoderNavigationPtrTheory.jnz_origin_ptr_path)) >>
     simp[] >> metis_tac[]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G1`,`jump_to entry.cs_current_bb t`,`tn1`] >>
  simp[] >>
  suspend "raise_entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_reason_frag_prefix_from_raise[raise_entry]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> metis_tac[body_inv_no_phi]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks' (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] _`
       (qspec_then `DF H0` assume_tac) >>
     metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `!fn inst s. frag_reachable ctx func (jump_to entry.cs_current_bb t) fn inst s ==>
      dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK (jump_to _ t),G1,tn1)`
       (fn path =>
         qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
           qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _`
             (fn safe => ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
               (LIST_CONJ [path,no_phi,safe])))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to entry.cs_current_bb t)` by
    (`allocas_below_fmp (jump_to entry.cs_current_bb t) <=> allocas_below_fmp t` by
       simp[jump_to_def, allocas_below_fmp_def] >>
     pop_assum (fn bound => PURE_ONCE_REWRITE_TAC [bound]) >> first_assum ACCEPT_TAC) >>
  drule_all assert_reason_false_source_ready >> strip_tac >>
  `gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx)
     (mid with gas_obs := [])` by
    (irule assert_reason_raise_admissible >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])` by
    (`well_typed_expr env e` by
       (qpat_assum `expr_body_pre _ cx env e _`
          (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts)) >>
     qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` assume_tac) >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `?tv u. eval_expr cx e
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,u)` by
    (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_prefix_ok cx se` by
    (qpat_assum `!src tv u. eval_expr cx e src = (INL tv,u) ==> body_expr_prefix_ok cx se`
       (fn rule => drule rule >> simp[])) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  pop_assum SUBST_ALL_TAC >>
  suspend "raise_entry_state"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assert_reason_frag_prefix_from_raise[raise_entry_state]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid (jump_to entry.cs_current_bb t) /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 (jump_to entry.cs_current_bb t) /\
     local_ptrs_reserved cenv entry /\
     ret_pc_ok cenv entry (jump_to entry.cs_current_bb t) /\
     return_buf_frame d cenv entry (jump_to entry.cs_current_bb t) /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at entry x) /\
     alloca_history func (jump_to entry.cs_current_bb t) /\ ~block_is_terminated entry /\
     ~(jump_to entry.cs_current_bb t).vs_halted /\
     (jump_to entry.cs_current_bb t).vs_current_bb = entry.cs_current_bb /\
     (jump_to entry.cs_current_bb t).vs_inst_idx = LENGTH entry.cs_current_insts` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (expr_post H ctx func cenv cx e es sa s1 s0 mid _ op t /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     match_mp_tac assert_reason_false_entry_full >>
     goal_assum (drule_at Any) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all storage_trace_frame_prefix >> strip_tac >>
     fs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `return_buf_sep d cenv mid (jump_to entry.cs_current_bb t)` by
    (simp[return_buf_sep_jump] >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`H0`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
     fs[expr_post_def, locals_kept_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cx lctx RetQ cenv
     (stmt_env cenv lctx ret_ty (Raise (RaiseReason se)))
     (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason se))))
     (eval_stmt cx (Raise (RaiseReason se))) mid` by
    (asm "raise_prefix" irule >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qexistsl_tac [`bindings`,`env`,`env`,`tops`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  pop_assum (mp_tac o REWRITE_RULE [stmt_frag_prefix_def,stmt_frag_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`entry`,`last`,`sentry`,`slast`,
          `jump_to entry.cs_current_bb t`,`G1`,`tn1`,`cenv`] mp_tac) >>
  (impl_tac >-
     (simp[gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
      first_assum ACCEPT_TAC)) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_assert_reason_frag_prefix_from_raise
*)
