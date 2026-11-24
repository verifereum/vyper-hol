(* The selected raw arm is evaluated once. Its successful conversion
   supplies the zero-reading machine path for conditional_result. *)
Theory bodyIfExpConditionalMods
Ancestors
  bodyFullPostsMods bodyPtrIfExpConditionalSource exprSimIfExp
  gasOutcomeFullBindMods gasOutcomeFullPostMods
  vyperEvalExprPreservesScopesDom fragGasOriginPtrExec bodyFullHashKeccakFixed
  gasContext gasExemptCertMods gasSummary vyperState vyperInterpreter exprSimDefs
  vyperStorageTrace vyperStorageFootprint context exprLowering exprSimMemDefs
  loweringPosts bodyFullShadowBodyInv bodyPtrDefs fragExec vyperAST words
  ptrDiscipline allocaHistory contextRawReachable compileEnv venomState
  gasShadow gasShadowState fragGasOriginPtr gasOutcomeFullMods
Libs monadsyntax

Theorem conditional_raw_admissible[local]:
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  qpat_x_assum `!gs. _` (qspec_then `gs` mp_tac) >>
  Cases_on `res` >> simp[bind_def, expr_vv_res_ok_def] >>
  rename1 `INL raw` >> Cases_on `raw` >>
  simp[conditional_result_def, raise_def, expr_vv_res_ok_def]
QED

Theorem conditional_value_or_memory[local]:
  conditional_result cx raw ee = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  tv = Value v \/ (tv = raw /\ ?id path. tv = PlaceR (MemoryPlace id path))
Proof
  strip_tac >> drule ifexp_conditional_result_place >>
  strip_tac >> gvs[read_result_def,return_def]
QED

Theorem ifexp_arm_conditional_from_step_mods:
  (!ee tv z G tn.
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
    (!id path. tv = PlaceR (MemoryPlace id path) ==>
      same_memory_layout cenv (lowered_value_type cenv e) t) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es1 sa sm u ee tv vv z /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn z) /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv z /\
    z.vs_current_bb = sm.cs_current_bb /\
    z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
      ~is_bytestring_type (post_value_type cenv e) ==>
        vv_own cenv cx (post_value_type cenv e) sa sm ee tv vv z) /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn z /\
    (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G z) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G z) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) z = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u G tn /\
    (!v. read_result cx tv ee = (INL v,ee) ==>
      value_has_type rty v /\
      !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
        value_has_type ptv v) ==>
    ?v z' Gz tf.
      read_result cx tv ee = (INL v,ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,G,tn) [] (OK z',Gz,tf) /\
        expr_post_mods H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tf z') /\
      (~is_word_type t ==>
        vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z') /\
      (~is_word_type t ==> !id path. tv = PlaceR (MemoryPlace id path) ==>
        vv_place_ptr cenv cx ee z' tv (LocatedValue t (mk_ptr op LocMemory))) /\
      (!ctv v. conditional_result cx tv ee = (INL ctv,ee) /\
        ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
        vv_own cenv cx t sa sb ee ctv
          (LocatedValue t (mk_ptr op LocMemory)) z') /\
      expr_store_bound cx t v op z' /\
      z'.vs_current_bb = sb.cs_current_bb /\
      z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
      ptr_val_ok cx t v op Gz tf z' /\
      (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
      (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op z' = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es1 /\
  expr_type e = t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es1 /\
  return_buf_frame d cenv sa u /\ alloca_history func u /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es1 u /\
    immutable_frame_mods func cenv cx es1 u /\
    storage_well_formed_on cx es1 (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es1 G1 tn1 u) /\
  ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs raw ee. eval_expr cx e (es1 with gas_obs := gs) = (INL raw,ee) ==>
    eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs) =
    (INL v,ee) ==>
    value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
      value_has_type ptv v) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (conditional_result cx))
    (es1,u,G1,tn1)
    (\H res ee G tn z. ?tv v. res = INL tv /\
      read_result cx tv ee = (INL v,ee) /\
      MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
      expr_post_mods H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z /\
      (~is_word_type t ==>
        vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z) /\
      (~is_word_type t ==>
        vv_place_ptr cenv cx ee z tv (LocatedValue t (mk_ptr op LocMemory))) /\
      (!v. tv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
        vv_own cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx t v op z /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      u.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx t v op G tn z /\
      (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G z) /\
      (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_then assume_tac conditional_raw_admissible >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ armQ armR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >- simp[storage_trace_frame_conditional_result] >>
  qexists `\H res ee G tn z. armQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ armQ armR` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `armR`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  suspend "selected"
QED

Resume ifexp_arm_conditional_from_step_mods[selected]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`z`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `armQ`] >> BETA_TAC >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists `tv` >> simp[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es1 with gas_obs := gas_explicit marks u.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => pure_rewrite_tac[th]) >>
     disch_tac >> first_assum ACCEPT_TAC) >>
  `eval_result_typed (env,cx,ee) tv (Type (expr_type e))` by
    (qpat_assum `!gs raw ee. eval_expr _ _ _ = _ ==> eval_result_typed _ _ _`
       drule >> simp[]) >>
  `MAP FDOM es1.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
     value_has_type rty v /\
     !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
       value_has_type ptv v` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!gs v ee. bind _ _ _ = _ ==> _`
       (qspecl_then [`gas_explicit marks u.vs_gas_readings`,`v`,`ee`] mp_tac) >> simp[bind_def]) >>
  `!id path. tv = PlaceR (MemoryPlace id path) ==>
    same_memory_layout cenv (lowered_value_type cenv e) t` by
    (rpt strip_tac >> gvs[] >> drule ifexp_raw_place_layout >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?tv. _) /\ _`
    (assume_tac o SIMP_RULE (srw_ss()) [FORALL_AND_THM, IMP_CONJ_THM]) >>
  qpat_x_assum `!ee tv z G tn. _`
    (qspecl_then [`ee`,`tv`,`z`,`G`,`tn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "pure"
QED

Resume ifexp_arm_conditional_from_step_mods[pure]:
  Cases_on `conditional_result cx tv ee` >>
  rename1 `conditional_result cx tv ee = (cr,ces)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
      (qspec_then `gas_explicit marks u.vs_gas_readings` mp_tac o
       REWRITE_RULE [gas_admissible_def]) >> simp[bind_def]) >>
  drule_all ifexp_conditional_source_success >>
  disch_then (qx_choose_then `ctv` strip_assume_tac) >>
  `conditional_result cx tv ee = (INL ctv,ee)` by
    (qpat_assum `!tail. conditional_result _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => pure_rewrite_tac[th]) >>
     simp[]) >>
  rename1 `expr_store_bound cx t v op zf` >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gz`,`ee`,`INL ctv`,`zf`,`tf`] >>
  simp[] >> suspend "post"
QED

Resume ifexp_arm_conditional_from_step_mods[post]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zf` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ zf` mp_tac >>
     simp[NoAsms,expr_post_mods_def,expr_post_def] >> strip_tac >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `~zf.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> strip_tac) >>
  simp[] >>
  conj_tac
  >- (strip_tac >> irule ifexp_vv_at_conditional >>
      qexistsl [`tv`,`v`] >> simp[] >>
      drule_all conditional_value_or_memory >> strip_tac >> gvs[]) >>
  conj_tac
  >- (strip_tac >> drule_all conditional_value_or_memory >>
      strip_tac >> gvs[vv_place_ptr_def,mk_ptr_def]) >>
  conj_tac
  >- (qx_gen_tac `cv` >> strip_tac >>
      qpat_assum `!ctv v. _ ==> vv_own _ _ _ _ _ _ ctv _ _`
        (qspecl_then [`ctv`,`cv`] mp_tac) >> gvs[]) >>
  strip_tac >> qx_genl_tac [`result_ty`,`addr`] >> strip_tac >>
  qpat_assum `~is_word_type t ==> !rt w. _`
    (mp_tac o SIMP_RULE (srw_ss()) []) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`result_ty`,`addr`] mp_tac) >>
  (impl_tac >- simp[]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise ifexp_arm_conditional_from_step_mods
