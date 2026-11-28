(* Request-prefix continuation of a captured storage-array For. *)
Theory s1PrefixForCapturedStorageContinue
Ancestors
  forCapturedStorageContinue s1PrefixForCapturedStorageRound s1PrefixForRounds
  s1PrefixForStorage s1PrefixForHandlers s1PrefixPreds s1PrefixCompose
  s1PrefixFrame s1PrefixDefs stmtSimForRounds vyperInterpreter vyperState vyperStorageTrace

val _ = Parse.hide "body";

Theorem for_captured_storage_continue_prefix:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
    sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     storage_well_formed_on cx es (FST H)) /\
  alloca_frame c es sa s0 c em u /\
  ((?w. vv_operand vv = Lit w) \/
   (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
             ~(?ty i. e = TopLevelName ty i))) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e)
                  (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0
    (bind (array_iterator_results cx (expr_type e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))))
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)))
    (em,u,Gu,tu)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST [`exps` |-> `[]`, `Extra` |->
    `\a rs ei s G tn. body_stmts_prefix_ok cx loop_body ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (do v <- read_result cx a; push_scope_with_var id tyv v;
            finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od)
        (ei,s,G,tn)`]
    for_captured_storage_continue_rounds_cut)) >>
  pure_rewrite_tac[boolTheory.FORALL_SIMP, boolTheory.IMP_CLAUSES, boolTheory.AND_CLAUSES] >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
     suspend "round_prefix")) >>
  disch_then (qx_choosel_then [`vs`,`z`,`G`,`tn`,`Inv`,`Done`]
    (map_every assume_tac o CONJUNCTS)) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
       (eval_for cx tyv id loop_body vs) (em,u,Gu,tu)` suffices_by
    (qpat_assum `!tail. array_iterator_results _ _ _ _ = _` (fn replay =>
       qpat_assum `check _ _ = return ()` (fn checked =>
         simp[NoAsms,gas_prefix_full_def,bind_def,ignore_bind_def,replay,checked,return_def]))) >>
  `body_for_prefix_ok cx tyv id loop_body vs` by
    (qpat_assum `!vs. _ ==> body_for_full_ok _ _ _ _ _ /\ _`
       (qspec_then `vs` mp_tac) >> simp[return_def]) >>
  Cases_on `vs` >-
    (simp[Once evaluate_def] >> irule gas_prefix_full_no_outcome >>
     simp[storage_trace_frame_return,return_def]) >>
  rename1 `body_for_prefix_ok cx tyv id loop_body (a::rs)` >>
  reverse (Cases_on `body_stmts_prefix_ok cx loop_body`) >-
    (irule gas_prefix_full_no_outcome >>
     simp[cj 4 evaluate_storage_trace_frame] >>
     rpt gen_tac >>
     Cases_on `read_result cx a (em with gas_obs := gobs)` >>
     rename1 `_ = (rr,er)` >>
     `er = em with gas_obs := gobs` by metis_tac[read_result_state] >>
     Cases_on `rr` >-
       (fs[body_for_prefix_ok_def] >> metis_tac[]) >>
     simp[eval_for_cons_round,bind_def] >> strip_tac >> gvs[]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[NoAsms,cj 4 evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`z`,`tn`] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ Inv _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  irule eval_for_rounds_prefix >>
  conj_tac >-
    (qexists_tac `\rs b. if b then return () else eval_for cx tyv id loop_body rs` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Done`,`Inv`,
    `\H ex ee gt r. for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r`,
    `stmt_res_ok lctx`,
    `\a. do v <- read_result cx a; push_scope_with_var id tyv v;
       finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od`,
    `cx_tops cx`] >>
  BETA_TAC >>
  conj_tac >- suspend "rounds" >>
  conj_tac >- simp[] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> _ /\ Inv _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  first_assum ACCEPT_TAC
QED

(* Match the round contract against the actual captured head. *)
Resume for_captured_storage_continue_prefix[round_prefix]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  `cx_tops cx = tops` by
    (drule_then strip_assume_tac bodyInvExecutionPropsTheory.body_inv_main_support >>
     simp[gasContextTheory.cx_tops_def]) >>
  `body_for_prefix_ok cx tyv id loop_body (a::rs)` by simp[body_for_prefix_ok_def] >>
  qpat_x_assum `cx_tops cx = tops` (SUBST_ALL_TAC o SYM) >>
  irule for_captured_storage_round_from_head_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
  TRY (qexists_tac `bindings` >> first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  qpat_assum `stmts_env _ _ _ (MAP gas_shadow_stmt loop_body) shadow_sb0 = _`
    (irule_at (Pat `stmts_env _ _ _ (MAP gas_shadow_stmt _) _ = _`)) >>
  qpat_assum `type_stmts _ _ loop_body = _`
    (irule_at (Pat `type_stmts _ _ _ = _`)) >>
  qpat_assum `fn_has_code sb0 sb1 func` (irule_at (Pat `fn_has_code sb0 _ func`)) >>
  qpat_assum `gas_admissible (eval_for cx tyv id loop_body (a::rs)) _ ei`
    (irule_at (Pat `gas_admissible _ _ _`)) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at (Pat `gas_shadow_function _ _`)) >>
  simp[]
QED

Resume for_captured_storage_continue_prefix[rounds]:
  rpt gen_tac >> strip_tac >>
  rename1 `gas_admissible (eval_for cx tyv id loop_body (x::xs)) _ ei` >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ round _` >>
  `storage_trace_frame round` by
    (simp[NoAsms,Abbr `round`] >> irule storage_trace_frame_bind_all >>
     simp[NoAsms,storage_trace_frame_read_result,storage_trace_frame_ignore_bind,
       storage_trace_frame_state_updates,storage_trace_frame_finally,
       storage_trace_frame_try,storage_trace_frame_return,storage_trace_frame_loop_handler,
       storage_trace_frame_pop_scope,evaluate_storage_trace_frame]) >>
  Cases_on `storage_trace_domain cx st0 ei.storage_trace` >-
    (simp[NoAsms,Abbr `round`] >>
     qpat_assum `!a rs ei s G tn. _ ==> gas_outcome_full _ _ _ _ _ _ _ _ /\ _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  conj_tac >-
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >> simp[]) >>
  irule s1PrefixInvalidTraceDomainTheory.gas_prefix_full_invalid_trace_domain >> simp[]
QED

Finalise for_captured_storage_continue_prefix
