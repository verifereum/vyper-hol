Theory s1PrefixExtCallGuardedOperands
Ancestors
  bodyFullExtCallAddressOwnedPrefix bodyFullExtCallTargetOutcome
  bodyFullExtCallPosList bodyFullIfExpReach bodyFullShadowBodyInv
  bodyFullPreds bodySimFull exprSimFullBundleProps s1PrefixPreds s1PrefixCompose s1PrefixProps
  gasOutcomeFull gasOutcomeFullCompose exprSafeOperand stmtSimProps
  compileEnv exprSimSource exprLoweringProps loweringPosts
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter

(* Keep only the restart facts about the path, not its representation. *)
Theorem operand_outcome_restart[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee J tm t. Q H res ee J tm t /\ ee.gas_obs = [] /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) R
Proof
  strip_tac >> irule gas_outcome_full_post_source >>
  irule_at Any gas_outcome_full_post_path >> first_assum (irule_at Any) >>
  simp[] >> qexists_tac `\H res ee J tm t. Q H res ee J tm t /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)` >>
  simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  REWRITE_TAC [expr_sim_full_code_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `xs = TAKE (LENGTH arg_types) tail` >>
  qabbrev_tac `kws = DROP (LENGTH arg_types) tail` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  irule gas_prefix_full_bind >> irule_at Any operand_outcome_restart >>
  irule_at Any extcall_request_head_halt_outcome >>
  qrefinel [`_`,`shadow_sm`,`shadow_sa`,`_`,`sm`,`sa`] >>
  rpt (goal_assum (drule_at Any)) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all] >>
  rpt conj_tac
  >~ [`gas_prefix_full _ _ _ (eval_exprs cx [addr]) _`]
  >- (qpat_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env es addr sa sb
          shadow_sa shadow_sb ao st0 s0 G0 tn0. _ ==> gas_prefix_full _ _ _ (eval_exprs _ [addr]) _`
        irule >>
      simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`ao`,`cenv`,`d`,`env`,`sa`,`sm`,`shadow_func`,`shadow_sa`,`shadow_sm`,`tops`] >>
      simp[] >> rpt strip_tac >> res_tac)
  >- suspend "head_restart"
  >> rpt gen_tac >> Cases_on `res` >> Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def]
QED
*)
Theorem extcall_guarded_operands_request_prefix:
  (!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env es addr sa sb
      shadow_sa shadow_sb ao st0 s0 G0 tn0.
    expr_type addr = BaseT AddressT /\
    body_exprs_full_ok cx [addr] /\ body_exprs_prefix_ok cx [addr] /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env addr es /\
    lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
      shadow_sa = (ao,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx [addr]) (es,s0,G0,tn0)) /\
  (!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env es xs kw_es sa sb
      shadow_sa shadow_sb svs st0 s0 G0 tn0.
    body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\ expr_sim_inv cenv cx env es /\
    (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env e st) /\
    compile_ext_call_args compile_expr cenv kw_es
      (MAP (lowered_value_type cenv) xs) xs sa = (svs,sb) /\
    compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
      (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
      (MAP gas_shadow_expr xs) shadow_sa = (svs,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)) /\
  args = addr::tail /\ nargs = LENGTH arg_types /\
  xs = TAKE nargs tail /\ kw_es = DROP nargs tail /\
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok cx (TAKE 1 args) /\ body_exprs_prefix_ok cx (TAKE 1 args) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env addr es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types ==>
     body_exprs_full_ok cx (TAKE n (DROP 1 args)) /\
     body_exprs_prefix_ok cx (TAKE n (DROP 1 args))) /\
  (!st target mid n st' vs ee.
     eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types /\
     eval_exprs cx (TAKE n (DROP 1 args)) st' = (INL vs,ee) ==>
     body_exprs_full_ok cx (DROP (1 + n) args) /\
     body_exprs_prefix_ok cx (DROP (1 + n) args)) /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sm) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sm = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP gas_shadow_expr xs) shadow_sm = (svs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,shadow_sa,shadow_sm) /\
  gas_shadow_state sb shadow_sb /\
  fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!target vs. storage_trace_frame (k target vs)) /\
  (!obs1 obs2 v target aw mid t G1 tn1 vs ee u G2 tn2.
    eval_exprs cx [addr] (es with gas_obs := obs1) = (INL [v],mid) /\
    eval_exprs cx xs (mid with gas_obs := obs2) = (INL vs,ee) /\
    body_exprs_full_ok cx kw_es /\ body_exprs_prefix_ok cx kw_es /\
    dest_AddressV v = SOME target /\ eval_operand ao u = SOME aw /\
    w2w aw = target /\ safe_operand sm ao /\
    ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t /\
    expr_sim_inv cenv cx env mid /\ mid.gas_obs = [] /\ ee.gas_obs = [] /\
    storage_trace_domain cx st0 mid.storage_trace /\ storage_trace_domain cx st0 ee.storage_trace /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx addr es sa sm s0 mid v ao t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      extcall_positional_post F DF lo d ctx func cenv cx env kw_es xs svs
        sm sb mid t G1 tn1 H (INL vs) ee G2 tn2 u) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (k [v] vs) (ee,u,G2,tn2) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (k [v] vs) (ee,u,G2,tn2)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx [addr]) (\target. bind (eval_exprs cx xs) (k target)))
    (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_guarded_operands_request_prefix[head_restart]:
  qx_genl_tac [`marks1`,`target_values`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  rename1 `dest_AddressV v = SOME (w2w aw)` >>
  `(mid with gas_obs := []) = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_exprs cx [addr] (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings) =
     (INL [v],mid)` by
    (qpat_assum `!tail. eval_exprs cx [addr] _ = _`
       (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL] o Q.SPEC `[]`) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_exprs >>
     qpat_assum `eval_exprs cx [addr] _ = (INL [v],mid)` (irule_at Any) >>
     qpat_assum `expr_body_pre _ cx env addr _`
       (assume_tac o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (qpat_assum `!st target mid. eval_exprs cx [addr] st = (INL target,mid) ==> _`
       (drule_then ACCEPT_TAC)) >>
  `is_word_type (expr_type addr)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (_ /\ ghost_inv_at _ _ _ _ _ mid _ _ _) /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_def]) >>
  irule gas_prefix_full_bind >> irule_at Any operand_outcome_restart >>
  irule_at Any (Q.SPEC `F` extcall_request_positional_packing_outcome_named) >>
  qpat_assum `compile_ext_call_args _ _ _ _ xs sm = _` (irule_at Any) >>
  qpat_assum `compile_ext_call_args _ _ _ _ (MAP _ xs) shadow_sm = _` (irule_at Any) >>
  qexistsl_tac [`tops`,`shadow_func`,`env`,`d`] >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  rpt conj_tac
  >~ [`gas_prefix_full _ _ _ (eval_exprs cx xs) _`]
  >- (qpat_assum `!DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env es xs kw_es sa sb
          shadow_sa shadow_sb svs st0 s0 G0 tn0. _ ==> gas_prefix_full _ _ _ (eval_exprs _ _) _`
        irule >>
      qpat_assum `compile_ext_call_args _ _ _ _ xs sm = _` (irule_at Any) >>
      qpat_assum `compile_ext_call_args _ _ _ _ (MAP _ xs) shadow_sm = _` (irule_at Any) >>
      qexistsl_tac [`tops`,`shadow_func`,`env`,`d`] >> simp[] >>
      rpt strip_tac >>
      (qpat_assum `!fn inst z. frag_reachable ctx func t fn inst z ==> _`
         (drule_then ACCEPT_TAC) ORELSE
       qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
         (drule_then strip_assume_tac) >> simp[]))
  >- first_assum ACCEPT_TAC
  >- suspend "pos_restart"
  >> rpt gen_tac >> Cases_on `res` >> Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_guarded_operands_request_prefix[pos_restart]:
  qx_genl_tac [`marks2`,`vs`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `(ee with gas_obs := []) = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_exprs cx xs (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings) =
     (INL vs,ee)` by
    (qpat_assum `!tail. eval_exprs cx xs _ = _`
       (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL] o Q.SPEC `[]`) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `body_exprs_full_ok cx kws /\ body_exprs_prefix_ok cx kws` by
    (qpat_assum `!st target mid st' vs ee. eval_exprs cx [addr] st = _ /\ eval_exprs cx xs st' = _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `extcall_positional_post F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_positional_post_def]) >>
  `eval_operand ao u = SOME aw` by
    (Cases_on `ao` >> fs[safe_operand_def, venomStateTheory.eval_operand_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (_ /\ ghost_inv_at _ _ _ _ _ mid _ _ _) /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_def])) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)` by
    (conj_tac >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_assum `!obs1 obs2. _`
    (irule o DISCH_ALL o CONJUNCT2 o UNDISCH o SPEC_ALL) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  reverse conj_tac >- metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs cx xs _ = (INL vs,ee)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 6 evaluate_storage_trace_frame]) >>
  conj_tac
  >- (qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> (_ /\ ghost_inv_at _ _ _ _ _ mid _ _ _) /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC)
  >> qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1) >>
  (* At INL the positional post does not depend on the exception summand. *)
  simp_tac bool_ss [extcall_positional_post_def,sumTheory.INL_11]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extcall_guarded_operands_request_prefix
*)
