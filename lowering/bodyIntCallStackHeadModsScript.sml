Theory bodyIntCallStackHeadMods
Ancestors
  bodyIntCallStagePacketMods bodyFullIntCallArgs bodyFullPredsMods
  bodyForcedStorageFrameMods gasOutcomeFullBindPathMods gasOutcomeFullPostMods
  exprSimFullBundleProps bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprOperandVar exprSimWordArgs wordArgsPtr bodyFullIfExpReach
  vyperEvalExprPreservesScopesDom vyperEvalScopesProgress exprSimSliceCompose
  vyperTypeInvariants vyperTypeExprSoundness valueEncodingTyping
  stmtSimForRounds freshWrites loweringPosts bodyPtrDefs ptrDiscipline list
  loweringStateRelDefs loweringShapeDefs bodyFullPostsMods gasExemptCertMods
  bodyMemoryDefs exprBodyPreProps exprSimDefs exprSimProps exprLoweringProps
  vyperStorageFootprint vyperState gasOutcomeFullMods fragGasOriginPtr
  fragGasOrigin fragGasMode fragGasPath

(* The old prefix is transported through the forced expression's actual
   variable, allocation, and ghost frame. No operand is evaluated again. *)
Theorem stack_keep_prefix[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) /\
  wb_frame cenv esi mid si s t /\ ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  si.cs_next_var <= cu.cs_next_var /\ si.cs_next_id <= cu.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!n b k. local_region cenv esi.scopes s n b k <=>
           local_region cenv mid.scopes t n b k) /\ t.vs_labels = s.vs_labels /\
  (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
      lookup_var rb s = SOME (n2w b) /\
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
      not_fresh_at si rb /\
      (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
        b+k <= lb \/ lb+sz <= b)) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
    (ops,ws,vals,ptys,pflags) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
      lookup_var rb t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < cu.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
      not_fresh_at cu rb /\
      (!n lb sz. local_region cenv mid.scopes t n lb sz ==>
        b+k <= lb \/ lb+sz <= b))
Proof
  pure_rewrite_tac [intcall_stage_ops_mods_def] >> strip_tac >>
  `!j. j < LENGTH ops ==> op_prov G1 (EL j ops) = op_prov G (EL j ops)` by
    (rpt strip_tac >> `MEM (EL j ops) ops` by simp[EL_MEM] >>
     Cases_on `EL j ops` >> gvs[op_prov_def,ghost_kept_at_def]) >>
  `!lbl. FLOOKUP t.vs_labels lbl = FLOOKUP s.vs_labels lbl` by simp[] >>
  drule_all_then mp_tac (SIMP_RULE bool_ss []
    (Q.INST [`clean_words` |-> `T`] intcall_args_prefix_frame)) >>
  simp[] >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac
  >- (qpat_assum `!j. j < LENGTH ops /\ ~EL j pflags ==> _`
        (drule_all_then strip_assume_tac) >>
      qexistsl_tac [`b`,`cap`,`aid`] >>
      `FLOOKUP t.vs_allocas aid = SOME (b,cap)` by fs[wb_frame_def] >>
      `aid < cu.cs_next_id` by decide_tac >> simp[] >> metis_tac[]) >>
  qpat_assum `!i j b k c l. _ ==> regions_disjoint b k c l` irule >>
  qexistsl_tac [`i`,`j`] >> simp[] >>
  `i < LENGTH ops` by decide_tac >>
  qpat_assum `!j. j < LENGTH ops ==> op_prov G1 _ = _`
    (fn th => simp[GSYM th])
QED

Theorem stack_locals_compose[local]:
  (!n b sz. local_region cenv es.scopes s n b sz ==>
             local_region cenv es1.scopes t n b sz) /\
  locals_kept cenv es es1 s t /\ locals_kept cenv es1 es2 t u ==>
  locals_kept cenv es es2 s u
Proof
  strip_tac >> fs[locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[scopes_progress_trans]
  >- (rpt strip_tac >>
      `?e e1. lookup_scopes n es.scopes = SOME e /\
              lookup_scopes n es1.scopes = SOME e1` by
        (gvs[local_region_def] >> metis_tac[optionTheory.option_CASES]) >>
      `e1 = e` by
        (qpat_x_assum `scopes_progress es.scopes _`
           (qspecl_then [`n`,`e`,`e1`] mp_tac o REWRITE_RULE [scopes_progress_def]) >>
         qpat_x_assum `scopes_progress es1.scopes _`
           (qspecl_then [`n`,`e1`,`e`] mp_tac o REWRITE_RULE [scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!n b sz entry' h. local_region _ es1.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz entry' h. local_region _ es.scopes _ _ _ _ /\ _ ==> _`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `n` >> fs[])
  >- simp[] >> metis_tac[]
QED

Theorem stack_keep_frame[local]:
  wb_frame cenv es0 esi sa s0 s /\ wb_frame cenv esi mid si s t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\ ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  sa.cs_next_id <= si.cs_next_id /\ sa.cs_next_var <= si.cs_next_var /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv esi.scopes s n b sz) ==>
  wb_frame cenv es0 mid sa s0 t /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (fs[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >> `aid < si.cs_next_id` by decide_tac >> metis_tac[]) >>
      irule stack_locals_compose >> qexistsl_tac [`esi`,`s`] >> simp[]) >>
  irule ghost_kept_at_trans >> qexistsl_tac [`G`,`esi`,`s`,`si`,`tn`] >>
  fs[wb_frame_def] >> metis_tac[]
QED

val head_post = ``
  ?v. (res : value + vyperState$exception) = INL v /\
      expr_post_mods (H : (bool # 256 word # type_value) list # num list)
        ctx func cenv cx e esi si cu s mid v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      t.vs_current_bb = cu.cs_current_bb /\ t.vs_inst_idx = LENGTH cu.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
      ghost_kept_at lo cenv esi si G tn s G1 tn1 /\ mid.gas_obs = []``;

Theorem stack_child_run[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env esi /\ expr_body_pre_mods mods cenv cx env e esi /\
  lower_value compile_expr cenv (expr_type e) e si = (op,cu) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shi = (op,shu) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,cu,shi,shu) /\
  local_ptrs_reserved cenv si /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok esi /\
  return_buf_frame d cenv si s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H esi.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esi s /\ immutable_frame_mods func cenv cx esi s /\
     storage_well_formed_on cx esi (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx esi G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\ s.vs_inst_idx = LENGTH si.cs_current_insts /\
  (!H exc ee gt r.
    expr_exit (INR exc : value + vyperState$exception) r /\
    halt_exit H cx ee (INR exc : value + vyperState$exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (esi,s,G,tn)
    (\H res mid G1 tn1 t. ^head_post)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)
Proof
  strip_tac >> fs[expr_sim_full_code_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e esi` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
      (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e) e esi /\
      expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e) e esi` by
       (first_x_assum irule >> simp[] >> conj_tac
        >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`si`,`cu`,`shi`,`shu`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> gen_tac >> Cases >> simp[exprSimDefsTheory.expr_exit_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[exprSimDefsTheory.expr_exit_def]
QED

Theorem stack_read_source[local]:
  expr_body_pre_mods mods cenv cx env e esi /\ body_const_cells_agree_mods mods cx env esi /\
  (!tail. bind (eval_expr cx e) (read_result cx) (esi with gas_obs := obs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] ==>
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt ==>
     value_has_type rt v /\ val_wf rt v /\ val_footprint rt v <= type_memory_size rt) /\
  MAP FDOM esi.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  `expr_body_pre_mods mods cenv cx env e (esi with gas_obs := obs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (esi with gas_obs := obs)` by simp[] >>
  `MAP FDOM esi.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx e) _ (esi with gas_obs := obs) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bind_def,AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_at (Pos last) write_index_read_source_mods >>
  disch_then (qspecl_then [`mods`,`env`,`cenv`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  drule expr_sim_inv_mods_env >>
  simp[env_consistent_def,env_context_consistent_def] >> strip_tac >>
  fs[value_runtime_typed_def] >>
  metis_tac[value_has_type_val_wf,val_footprint_le]
QED

Theorem stack_word_operand[local]:
  is_word_type dty /\ type_widens_to (get_tenv cx) (expr_type e) dty /\
  expr_post_mods H ctx func cenv cx e esi si cu s mid v op t /\
  ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
  lower_value compile_expr cenv (expr_type e) e si = (op,cu) /\ local_ptrs_reserved cenv si ==>
  expr_type e = dty /\ op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
  (!x. op = Var x ==> not_fresh_at cu x) /\
  ?w. eval_operand op t = SOME w /\
      !rt. evaluate_type (get_tenv cx) dty = SOME rt ==> w = typed_val_to_w256 rt v
Proof
  strip_tac >>
  `expr_type e = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `post_value_type cenv e = dty` by metis_tac[post_value_type_word] >>
  drule compile_lower_value_var >> simp[] >> strip_tac >> fs[ptr_val_ok_def] >>
  gvs[expr_post_mods_def,expr_post_def,expr_val_rel_def]
QED

Theorem stack_read_geometry[local]:
  (!tail. bind (eval_expr cx e) (read_result cx) (esi with gas_obs := obs ++ tail) =
     (INL v,mid with gas_obs := tail)) /\
  valid_horizon cx st0 H mid.storage_trace /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  local_ptrs_reserved cenv si /\ MAP FDOM esi.scopes = MAP FDOM mid.scopes /\
  expr_post_mods H ctx func cenv cx e esi si cu s mid v op t ==>
  wb_frame cenv esi mid si s t /\
  !n b sz. local_region cenv esi.scopes s n b sz <=> local_region cenv mid.scopes t n b sz
Proof
  strip_tac >>
  `wb_frame cenv esi mid si s t` by
    (fs[expr_post_mods_def,expr_post_def,wb_frame_def] >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  simp[] >>
  `valid_horizon cx st0 H esi.storage_trace` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_at (Pat `f st = (res,st')`) valid_horizon_frame >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  fs[intcall_stage_frame_mods_def] >>
  qpat_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all wb_frame_local_regions >> simp[]
QED

Theorem stack_extend_frame[local]:
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  ci_mono si cu /\ wb_frame cenv esi mid si s t /\
  ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  (!n b sz. local_region cenv esi.scopes s n b sz <=> local_region cenv mid.scopes t n b sz) /\
  MAP FDOM esi.scopes = MAP FDOM mid.scopes /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
      lookup_var rb t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < cu.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
      not_fresh_at cu rb /\
      (!n lb sz. local_region cenv mid.scopes t n lb sz ==> b+k <= lb \/ lb+sz <= b)) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = cu.cs_current_bb /\ t.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t) ==>
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cu,mid,t,G1,tn1) pin
Proof
  pure_rewrite_tac [intcall_stage_frame_mods_def,ci_mono_def] >> strip_tac >>
  drule_all_then strip_assume_tac stack_keep_frame >> simp[] >>
  `return_buf_frame d cenv cu t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`si`] >>
     fs[wb_frame_def]) >>
  `sa.cs_next_id <= cu.cs_next_id /\ sa.cs_next_var <= cu.cs_next_var /\
   s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  simp[] >> rpt strip_tac >> res_tac
QED

(* The continuation is entered only after the forced read, with its exact
   marks and the original caller frame extended to the new cut. *)
Theorem intcall_stage_stack_head_mods:
  is_word_type dty /\ type_widens_to (get_tenv cx) (expr_type e) dty /\
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env esi /\ expr_body_pre_mods mods cenv cx env e esi /\
  lower_value compile_expr cenv (expr_type e) e si = (op,cu) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shi = (op,shu) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,cu,shi,shu) /\
  local_ptrs_reserved cenv si /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next) P esi /\
  (!exc. P (INR exc) ==> expr_res_ok (INR exc)) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) /\
  (!mid t G1 tn1 w v.
    intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin (ops,ws,vals,ptys,pflags) /\
    eval_operand op t = SOME w /\ op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
    (!x. op = Var x ==> not_fresh_at cu x) /\
    (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
       value_has_type rt v /\ val_wf rt v /\ val_footprint rt v <= type_memory_size rt /\
       w = typed_val_to_w256 rt v) ==>
    intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
      (ops ++ [op],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [T])) /\
  (!v. storage_trace_frame (next v)) /\
  (!H exc ee gt r.
    expr_exit (INR exc : value + vyperState$exception) r /\
    halt_exit H cx ee (INR exc : value + vyperState$exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) /\
  (!marks v mid t G1 tn1 w.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1)) /\
    gas_path ctx func s (LENGTH marks) (OK t) /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (cu,mid,t,G1,tn1) pin /\
    intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
      (ops ++ [op],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [T]) /\
    body_const_cells_agree_mods mods cx env mid /\ expr_sim_inv_mods mods cenv cx env mid /\
    gas_admissible (next v) P mid /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next v) (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (esi,s,G,tn) Q R
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok esi` by
    (irule slice_gas_admissible_bind_head >> conj_tac >- simp[expr_res_ok_def] >>
     qexistsl_tac [`P`,`next`] >> simp[]) >>
  `ci_mono si cu` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`si`] ci_mono_lower_value_compile_expr) >> simp[]) >>
  irule gas_outcome_full_mods_bind_all_path >>
  reverse (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  qexists_tac `\H res mid G1 tn1 t. ^head_post` >> BETA_TAC >>
  conj_tac >- suspend "continue" >>
  suspend "start"
QED

Resume intcall_stage_stack_head_mods[start]:
  irule stack_child_run >> fs[intcall_stage_frame_mods_def] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H esi.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`shadow_func`,`shi`,`shu`] >> simp[]) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED

Resume intcall_stage_stack_head_mods[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?v. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  drule_all_then strip_assume_tac stack_read_source >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac stack_word_operand >>
  qpat_assum `intcall_stage_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [intcall_stage_frame_mods_def]) >>
  drule_all_then strip_assume_tac stack_read_geometry >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (drule_then assume_tac) >>
  drule_then assume_tac gas_origin_ptr_path_erase >>
  `t.vs_labels = s.vs_labels` by (drule gas_path_labels >> simp[]) >>
  `si.cs_next_var <= cu.cs_next_var /\ si.cs_next_id <= cu.cs_next_id` by fs[ci_mono_def] >>
  drule_all_then strip_assume_tac stack_keep_prefix >>
  `~t.vs_halted` by (drule gas_path_normal >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  `intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (cu,mid,t,G1,tn1) pin` by
    (irule stack_extend_frame >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G`,`esi`,`s`,`si`,`tn`] >> simp[]) >>
  `gas_admissible (next v) P mid` by
    (drule_all gas_admissible_bind_tail >> simp[evaluation_state_component_equality]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >>
     disch_then (fn th => rpt strip_tac >> irule th >>
       conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `fn` >> simp[])) >>
  qpat_assum `!marks v mid t G1 tn1 w. _ ==> gas_outcome_full_mods _ _ _ _ (next v) _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `marks` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `w` >>
  qpat_assum `!mid t G1 tn1 w v. _ ==> intcall_stage_ops_mods _ _ _ _ _ _ _` irule >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!rt. evaluate_type _ (expr_type e) = SOME rt ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Finalise intcall_stage_stack_head_mods
