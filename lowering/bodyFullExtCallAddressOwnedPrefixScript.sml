Theory bodyFullExtCallAddressOwnedPrefix
Ancestors
  bodyFullShadowBodyInv exprSimFullBundleProps
  bodyFullExtCallTargetOutcome bodyFullExtCallPosList
  gasOutcomeFull gasOutcomeFullCompose gasExemptCert vyperStorageTrace vyperStorageFootprint
  exprSimDefs bodyFullIfExpReach
  exprSimHypsDefs exprSimSource exprSafeOperand exprSimWordArgs exprLoweringProps stmtSimProps
  bodyFullPreds bodySimFull compileEnv loweringPosts vyperInterpreter wordArgsPtr
  evalNoHalt supportedExprTraverse vyperTypeCallGraph list
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* At each bind, expose that the producer's cut has consumed its observations. *)
val operand_bind_tac =
  irule gas_outcome_full_bind_all_path >>
  simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (qx_genl_tac [`left_marks`,`left_values`,`left_es`,`left_t`] >>
      rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      qexistsl [`left_es`,`left_t`,`left_values`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  irule_at Any
    (Q.INST [`Q'` |-> `\H res ee G tn t. ee.gas_obs = [] /\ Q H res ee G tn t`]
      gas_outcome_full_post_source)

(* Keep the target's pointer ownership at the head cut of this execution. *)
Theorem extcall_request_guarded_operand_prefix_address_owned_bundled:
  !mods exps.
  args = addr::tail /\ nargs = LENGTH arg_types /\
  xs = TAKE nargs tail /\ kw_es = DROP nargs tail /\
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok_mods mods exps cx (TAKE 1 args) /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env addr es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types ==> body_exprs_full_ok_mods mods exps cx (TAKE n (DROP 1 args))) /\
  (!st target mid n st' vs ee.
     eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types /\
     eval_exprs cx (TAKE n (DROP 1 args)) st' = (INL vs,ee) ==>
     body_exprs_full_ok_mods mods exps cx (DROP (1 + n) args)) /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==>
     expr_body_pre_mods mods cenv cx env e st) /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sm) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sm = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP gas_shadow_expr xs) shadow_sm = (svs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func)
    (sa,sm,shadow_sa,shadow_sm) /\
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
    body_exprs_full_ok_mods mods exps cx kw_es /\
    dest_AddressV v = SOME target /\ eval_operand ao u = SOME aw /\
    w2w aw = target /\ safe_operand sm ao /\
    ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t /\
    expr_sim_inv_mods mods cenv cx env mid /\ mid.gas_obs = [] /\ ee.gas_obs = [] /\
    storage_trace_domain cx st0 mid.storage_trace /\
    storage_trace_domain cx st0 ee.storage_trace /\
    LENGTH svs = LENGTH xs /\
    EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
    return_buf_frame d cenv sb u /\ ~u.vs_halted /\
    expr_sim_full_endpoint func sb s0 u /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    wb_frame cenv mid ee sm t u /\
    MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
    expr_sim_inv_mods mods cenv cx env ee /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\
      expr_post H ctx func cenv cx addr es sa sm s0 mid v ao t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
      LIST_REL (\(e,sv) v.
        (?si se ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,se) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) se = (sv,ss) /\
          (~copy ==> ~exprs_can_mutate cenv kw_es) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) u = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP u.vs_allocas se.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              se.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes u n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sm.cs_next_var <= si.cs_next_var /\ sm.cs_next_id <= si.cs_next_id /\
          se.cs_next_var <= sb.cs_next_var /\ se.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv u /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
        vv_storage_live H cx sv ee u /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G2 u) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G2 u) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) u = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (k [v] vs) (ee,u,G2,tn2) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_exprs cx [addr]) (\target. bind (eval_exprs cx xs) (k target)))
    (es,s0,G0,tn0) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  REWRITE_TAC [expr_sim_full_code_def, expr_sim_full_endpoint_def] >>
  strip_tac >> gvs[] >>
  qabbrev_tac `xs = TAKE (LENGTH arg_types) tail` >>
  qabbrev_tac `kws = DROP (LENGTH arg_types) tail` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  operand_bind_tac >>
  irule_at Any extcall_request_head_halt_outcome >>
  (* The singleton supplier calls its two output compiler states sb/shadow_sb. *)
  qrefinel [`_`,`shadow_sm`,`shadow_sa`,`_`,`sm`,`sa`] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[] >>
      metis_tac[expr_exit_INR_type, halt_exit_def]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[halt_exit_def] >>
      metis_tac[expr_exit_INR_type, expr_exit_def]) >>
  qx_genl_tac [`marks1`,`target_values`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path _ (s0,G0,tn0) marks1 (OK t,G1,tn1)`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks1 (OK t,G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> mid.gas_obs = [] /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
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
  `body_exprs_full_ok cx xs` by metis_tac[] >>
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
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ mid _ _ _`
       (drule_then strip_assume_tac) >> fs[expr_post_def]) >>
  operand_bind_tac >>
  irule_at Any extcall_request_positional_packing_outcome >>
  qpat_assum `compile_ext_call_args _ _ _ _ xs sm = _` (irule_at Any) >>
  qpat_assum `compile_ext_call_args _ _ _ _ (MAP _ xs) shadow_sm = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d`] >>
  asm_rewrite_tac[] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_INR_type, halt_exit_def]) >>
  qx_genl_tac [`marks2`,`pos_values`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path _ (t,G1,tn1) marks2 (OK u,G2,tn2)`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then assume_tac)) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) marks2 (OK u,G2,tn2)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func t fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ee.gas_obs = [] /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `(ee with gas_obs := []) = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_exprs cx xs (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings) =
     (INL vs,ee)` by
    (qpat_assum `!tail. eval_exprs cx xs _ = _`
       (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL] o Q.SPEC `[]`) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `body_exprs_full_ok cx kws` by metis_tac[] >>
  `eval_operand ao u = SOME aw` by
    (Cases_on `ao` >> fs[safe_operand_def, venomStateTheory.eval_operand_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H ctx func cenv cx addr es sa sm s0 mid v ao t`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_def])) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)` by
    (conj_tac >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_assum `!obs1 obs2. _` irule >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`gas_explicit marks1 s0.vs_gas_readings`,
                `gas_explicit marks2 t.vs_gas_readings`,`t`,`tn1`] >>
  simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs cx xs _ = (INL vs,ee)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 6 evaluate_storage_trace_frame]) >>
  simp[]
QED

Theorem extcall_request_guarded_operand_prefix_address_owned:
  !mods exps.
  args = addr::tail /\ nargs = LENGTH arg_types /\
  xs = TAKE nargs tail /\ kw_es = DROP nargs tail /\
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok_mods mods exps cx (TAKE 1 args) /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env addr es /\
  (!st target mid n. eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types ==> body_exprs_full_ok_mods mods exps cx (TAKE n (DROP 1 args))) /\
  (!st target mid n st' vs ee.
     eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
     n = LENGTH arg_types /\
     eval_exprs cx (TAKE n (DROP 1 args)) st' = (INL vs,ee) ==>
     body_exprs_full_ok_mods mods exps cx (DROP (1 + n) args)) /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==>
     expr_body_pre_mods mods cenv cx env e st) /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sm) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sm = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP gas_shadow_expr xs) shadow_sm = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func /\
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
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!target vs. storage_trace_frame (k target vs)) /\
  (!obs1 obs2 v target aw mid t G1 tn1 vs ee u G2 tn2.
    eval_exprs cx [addr] (es with gas_obs := obs1) = (INL [v],mid) /\
    eval_exprs cx xs (mid with gas_obs := obs2) = (INL vs,ee) /\
    body_exprs_full_ok_mods mods exps cx kw_es /\
    dest_AddressV v = SOME target /\ eval_operand ao u = SOME aw /\
    w2w aw = target /\ safe_operand sm ao /\
    ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t /\
    expr_sim_inv_mods mods cenv cx env mid /\ mid.gas_obs = [] /\ ee.gas_obs = [] /\
    storage_trace_domain cx st0 mid.storage_trace /\
    storage_trace_domain cx st0 ee.storage_trace /\
    LENGTH svs = LENGTH xs /\
    EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
    return_buf_frame d cenv sb u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    wb_frame cenv mid ee sm t u /\
    MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
    expr_sim_inv_mods mods cenv cx env ee /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\
      expr_post H ctx func cenv cx addr es sa sm s0 mid v ao t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
      LIST_REL (\(e,sv) v.
        (?si se ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,se) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) se = (sv,ss) /\
          (~copy ==> ~exprs_can_mutate cenv kw_es) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) u = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP u.vs_allocas se.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              se.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes u n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sm.cs_next_var <= si.cs_next_var /\ sm.cs_next_id <= si.cs_next_id /\
          se.cs_next_var <= sb.cs_next_var /\ se.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv u /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
        vv_storage_live H cx sv ee u /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G2 u) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G2 u) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) u = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (k [v] vs) (ee,u,G2,tn2) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_exprs cx [addr]) (\target. bind (eval_exprs cx xs) (k target)))
    (es,s0,G0,tn0) Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  mp_tac extcall_request_guarded_operand_prefix_address_owned_bundled >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- simp[expr_sim_full_code_def] >>
    qx_genl_tac [`obs1`, `obs2`, `v`, `target`, `aw`, `mid`, `t`,
      `G1`, `tn1`, `vs`, `ee`, `u`, `G2`, `tn2`] >>
    qpat_assum `!obs1 obs2 v target aw mid t G1 tn1 vs ee u G2 tn2. _`
      (qspecl_then [`obs1`, `obs2`, `v`, `target`, `aw`, `mid`, `t`,
        `G1`, `tn1`, `vs`, `ee`, `u`, `G2`, `tn2`] mp_tac) >>
    REWRITE_TAC [expr_sim_full_endpoint_def] >>
    disch_then (fn continuation => strip_tac >> irule continuation) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
