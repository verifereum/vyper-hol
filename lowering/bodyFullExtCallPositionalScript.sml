Theory bodyFullExtCallPositional
Ancestors
  bodyFullExtCallTargetOutcome bodyFullExtCallPosList
  gasOutcomeFullCompose gasExemptCert vyperStorageTrace vyperStorageFootprint
  exprSimSource exprSafeOperand exprSimWordArgs exprLoweringProps stmtSimProps
  bodySimFull compileEnv loweringPosts vyperInterpreter wordArgsPtr

(* Both cuts return lists. Abort and exempt suffixes do not enter the
   continuation, and the normal premise is at one fixed physical state. *)
Theorem extcall_bind_values_at_cut[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (source : evaluation_state -> value list evaluation_result) (es,s,G,tn)
    P (\H res ee gt r. expr_exit res r) /\
  (!H res ee G' tn' t. P H res ee G' tn' t ==> ?vs. res = INL vs) /\
  storage_trace_frame source /\ (!vs. storage_trace_frame (next vs)) /\
  (!marks vs mid G1 tn1 t.
     source (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
       (INL vs,mid) /\ mid.gas_obs = [] /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> P H (INL vs) mid G1 tn1 t) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
       (next vs) (mid,t,G1,tn1) Q (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind source next) (es,s,G,tn) Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >> irule gas_outcome_full_bind_all >> simp[] >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  qexists_tac `\H res ee G' tn' t.
    ee.gas_obs = [] /\ P H res ee G' tn' t` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >>
      simp[] >> metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> disj1_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H res ee G' tn' t. _ ==> ?vs. res = INL vs`
    (drule_then (qx_choose_then `vs` assume_tac)) >>
  qexists_tac `vs` >> simp[] >> first_x_assum irule >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexists_tac `marks` >>
  `(mid with gas_obs := []) = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_x_assum `!tail. source _ = _` (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem extcall_address_operand_frame[local]:
  safe_operand sm ao /\ eval_operand ao t = SOME aw /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
         lookup_var x u = SOME w) ==>
  eval_operand ao u = SOME aw
Proof
  Cases_on `ao` >> simp[safe_operand_def, venomStateTheory.eval_operand_def]
QED

(* The positional IH is guarded by the actual successful target evaluation.
   Its continuation sees the actual successful positional evaluation too. *)
Theorem extcall_request_positional_prefix:
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env addr es /\
  (!st target mid. eval_exprs cx [addr] st = (INL target,mid) ==>
     body_exprs_full_ok cx xs) /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  EVERY (\e. ~expr_has_effect e) (xs ++ kw_es) /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sm) /\
  lower_value compile_expr cenv (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sm) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sm = (svs,sb) /\
  compile_ext_call_args compile_expr cenv (MAP gas_shadow_expr kw_es)
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
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    dest_AddressV v = SOME target /\ eval_operand ao u = SOME aw /\
    w2w aw = target /\ safe_operand sm ao /\
    expr_sim_inv cenv cx env mid /\ mid.gas_obs = [] /\ ee.gas_obs = [] /\
    storage_trace_domain cx st0 mid.storage_trace /\
    storage_trace_domain cx st0 ee.storage_trace /\
    LENGTH svs = LENGTH xs /\
    EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
    return_buf_frame d cenv sb u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    pure_frame cenv func mid sm t u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
    (mid with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\
      expr_post H ctx func cenv cx addr es sa sm s0 mid v ao t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
      LIST_REL (\(e,sv) w.
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
         (?p si sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
           lowered_value_type cenv e = expr_type e /\
           compile_expr cenv (expr_type e) e si = (sv,sm0) /\
           sm.cs_next_var <= si.cs_next_var /\ sm.cs_next_id <= si.cs_next_id /\
           sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
        (?raw. read_result cx raw ee = (INL w,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
          vv_at cenv cx (lowered_value_type cenv e) sm sb ee raw sv u /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
          vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv u) /\
        vv_storage_live H cx sv ee u /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G2 u) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G2 u) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w0. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) u = SOME w0 ==>
            w2n w0 + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
              val_in_memory rt w (w2n w0) mem))) (ZIP (xs,svs)) vs) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (k [v] vs) (ee,u,G2,tn2) Q (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_exprs cx [addr]) (\target. bind (eval_exprs cx xs) (k target)))
    (es,s0,G0,tn0) Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  irule extcall_bind_values_at_cut >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  irule_at Any extcall_request_head_outcome >>
  qrefinel [`_`,`shadow_sm`,`shadow_sa`,`_`,`sm`,`sa`] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qx_genl_tac [`marks1`,`target_values`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
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
  irule extcall_bind_values_at_cut >> simp[evaluate_storage_trace_frame] >>
  irule_at Any extcall_request_positional_outcome >>
  qpat_assum `compile_ext_call_args _ _ _ _ xs sm = _` (irule_at Any) >>
  qpat_assum `compile_ext_call_args _ _ _ _ (MAP _ xs) shadow_sm = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qx_genl_tac [`marks2`,`vs`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `eval_operand ao u = SOME aw` by
    (irule extcall_address_operand_frame >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ mid _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_def])) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)` by
    (conj_tac >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_assum `!obs1 obs2. _` irule >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`gas_explicit marks1 s0.vs_gas_readings`,
                `gas_explicit marks2 t.vs_gas_readings`,`t`,`tn1`] >>
  simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs cx xs _ = (INL vs,ee)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  simp[]
QED
