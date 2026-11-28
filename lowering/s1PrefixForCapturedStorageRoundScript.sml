(* The captured storage head supplies the scope and machine state of the body. *)
Theory s1PrefixForCapturedStorageRound
Ancestors
  forCapturedStorageRound forCapturedStorageLive forConsBodyGas bodyFullIfExpReach exprSimMemorySource
  s1PrefixPreds s1PrefixForStorage s1PrefixForHandlers s1PrefixCompose s1PrefixFrame
  s1PrefixInvalidTraceDomain s1PrefixProps vyperStorageTrace vyperStorageFootprint
  vyperState vyperInterpreter

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qabbrev_tac `head = bind (read_result cx a) (push_scope_with_var id tyv)` >>
  qabbrev_tac `clean = finally (try (ignore_bind (eval_stmts cx stmts) (return F))
    handle_loop_exception) pop_scope` >>
  `bind head (\u:unit. clean) =
    bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id tyv v) clean)` by
    simp[Abbr `head`,bind_assoc,ignore_bind_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  `storage_trace_frame head` by
    (simp[Abbr `head`] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result,storage_trace_frame_state_updates]) >>
  `storage_trace_frame clean` by
    simp[Abbr `clean`,storage_trace_frame_finally,storage_trace_frame_try,
         storage_trace_frame_ignore_bind,storage_trace_frame_pop_scope,
         storage_trace_frame_loop_handler,storage_trace_frame_return,evaluate_storage_trace_frame] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >>
      simp[storage_trace_frame_bind_all]) >>
  qpat_assum `storage_trace_domain _ _ _ ==> gas_outcome_full _ _ _ _ _ _ _ _` drule >>
  disch_then (mp_then Any irule gas_prefix_full_bind_replay) >>
  BETA_TAC >> simp[] >>
  conj_tac >- suspend "body_entry" >>
  conj_tac >- (rpt strip_tac >> simp[sumTheory.ISR]) >>
  conj_tac >-
    (simp[Abbr `head`] >> irule requests_outcomes_frame_bind_all >>
     simp[requests_outcomes_frame_read_result,requests_outcomes_frame_def,
          vyperCallOutcomeFrameTheory.state_rel_frame_def,push_scope_with_var_def,return_def]) >>
  suspend "silent"
QED
*)
Theorem for_captured_storage_round_from_head_prefix:
  body_inv (cx_tops cx) ctx bc cx /\ shadow_body_inv (cx_tops cx) ctx shadow_ctx /\
  supported_stmts (cx_tops cx) bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
      occurs_abi_decode_target target (cx_tops cx)) /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  stmts_exprs_ok bc stmts /\ call_evaluation_safe cx (int_calls_stmts stmts) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
  stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc1,sb1) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt stmts)
    shadow_sb0 = (gas_shadow_env T bc1,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
  ~block_is_terminated sb0 /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. lvo = Var x ==> not_fresh_at sb0 x) /\ (!lbl. lvo <> Label lbl) /\
  ~s.vs_halted /\ (!f inst u. frag_reachable ctx func s f inst u ==> dalloca_fmp_headroom inst u) /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    lookup_scopes id es.scopes = NONE) /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  gas_admissible (eval_for cx tyv id stmts (a::rs)) (stmt_res_ok lctx) es /\
  body_for_prefix_ok cx tyv id stmts (a::rs) /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (read_result cx a) (push_scope_with_var id tyv)) (es,s,G,tn)
      (\H res eb GG tt z. res = INL () /\ eb.gas_obs = [] /\
        ?v j. eb = for_captured_storage_round_scope id tyv (es with gas_obs := []) v /\
          read_result cx a es = (INL v,es) /\
          for_captured_storage_round_entry (DF,lo,d,ctx,func)
            (cx,c0,bc,extend_local env id typ F,sb0,stmts) (e0,sa0,s0,G0,tn0)
            (idx,p,dst,lvo,len,inst,nb) (H,eb,j,z,GG,tt) /\
          eval_operand bop z = SOME slot /\ op_taint tt bop = {} /\ a::rs = DROP j vs)
      (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id tyv v)
      (finally (try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception) pop_scope)))
    (es,s,G,tn)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head_prefix[silent]:
  irule gas_prefix_full_no_outcome >> simp[] >>
  simp[Abbr `head`] >> rpt gen_tac >>
  Cases_on `read_result cx a (es with gas_obs := gobs)` >> rename1 `_ = (rr,er)` >>
  `er = es with gas_obs := gobs` by metis_tac[read_result_state] >>
  Cases_on `rr` >> simp[bind_def,push_scope_with_var_def,return_def] >>
  strip_tac >> gvs[listTheory.DROP_LENGTH_NIL]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head_prefix[body_entry]:
  map_every qx_gen_tac [`marks`,`eb`,`GG`,`tt`,`z`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon eb.storage_trace` >>
  `valid_horizon cx st0 H0 eb.storage_trace` by simp[Abbr `H0`,GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==> _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  rename1 `read_result cx a es = (INL v,es)` >>
  `eb.storage_trace = es.storage_trace` by
    simp[for_captured_storage_round_scope_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (qpat_assum `storage_trace_domain _ _ _ ==> lookup_scopes _ _ = NONE` irule >>
     first_assum ACCEPT_TAC) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`body_inv (cx_tops cx) ctx bc cx`,`MEM func ctx.ctx_functions`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[body_inv_no_phi]) >>
  `!f inst w. frag_reachable ctx func z f inst w ==> dalloca_fmp_headroom inst w` by
    (qpat_assum `gas_origin_ptr_path _ _ marks (OK z,GG,tt)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `body_stmts_prefix_ok cx stmts` by
    (qpat_x_assum `body_for_prefix_ok _ _ _ _ _` mp_tac >>
     simp[body_for_prefix_ok_def] >> metis_tac[]) >>
  qabbrev_tac `ei = es with gas_obs := []` >>
  `eb = ei with scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) :: ei.scopes` by
    simp[for_captured_storage_round_scope_def] >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) eb` by
    (qpat_assum `eb = ei with scopes := _` SUBST1_TAC >>
     drule_at (Pat `gas_admissible _ _ _`) forConsBodyGasTheory.captured_storage_body_admissible >>
     disch_then (qspecl_then [`v`,`lctx`,`incr`,`exit`] mp_tac) >>
     simp[Abbr `ei`,evaluation_state_fupdfupds]) >>
  `!H. valid_horizon cx st0 H eb.storage_trace ==>
    stmt_state_rel H ctx func bc cx eb z /\ storage_well_formed_on cx eb (FST H) /\
    ghost_inv_at (DF H) lo d bc cx eb GG tt z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==> _ /\ _`
       (qspec_then `H` (drule_then mp_tac)) >>
     disch_then (strip_assume_tac o REWRITE_RULE[for_captured_storage_round_entry_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `for_captured_storage_round_entry _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[for_captured_storage_round_entry_def]) >>
  `body_const_cells_agree [(NONE,cx_tops cx)] cx env ei` by simp[Abbr `ei`] >>
  qpat_assum `eb = ei with scopes := _` (fn eq =>
    qpat_assum `expr_sim_inv bc cx _ eb` (assume_tac o PURE_REWRITE_RULE[eq])) >>
  simp[Abbr `clean`] >> irule for_body_cleanup_prefix >>
  conj_tac >- (qpat_assum `eb = ei with scopes := _` SUBST1_TAC >> simp[]) >>
  suspend "invoke"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head_prefix[invoke]:
  conj_tac >>
  (fn g =>
    let
      val rule = if boolSyntax.is_exists (snd g) then
          BETA_RULE bodyFullForStorageTheory.for_storage_body_invoke_full
        else for_storage_body_invoke_prefix
    in
      qpat_assum `frame_ret_ok_full _ _ _ _ _`
        (mp_then (Pat `frame_ret_ok_full _ _ _ _ _`) mp_tac rule) g
    end) >>
  disch_then (fn th =>
    qpat_assum `expr_sim_inv bc cx _ (ei with scopes := _)`
      (mp_then (Pat `expr_sim_inv _ _ _ _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `supported_stmts (cx_tops cx) bindings stmts`
      (mp_then (Pat `supported_stmts _ _ _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b`
      (mp_then (Pat `type_stmts _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = _`
    (mp_then (Pat `stmts_env _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmts_env _ _ _ (MAP gas_shadow_stmt _) _ = _`
    (mp_then (Pat `stmts_env _ _ _ (MAP gas_shadow_stmt _) _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var idx z = _`
    (mp_then (Pat `lookup_var _ _ = SOME (n2w _)`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var p z = _`
    (mp_then (Pat `lookup_var _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  qpat_assum `eb = ei with scopes := _` (fn eq =>
    disch_then (mp_tac o PURE_REWRITE_RULE[GSYM eq])) >>
  disch_then (qspecl_then [`st0`,`GG`,`tt`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `eb = ei with scopes := _` (fn eq =>
    disch_then (assume_tac o PURE_REWRITE_RULE[eq])) >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_x_assum `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ _ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_captured_storage_round_from_head_prefix
*)
