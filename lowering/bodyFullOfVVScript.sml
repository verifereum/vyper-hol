(* The value judgment from the vv judgment on the full (finite-horizon)
   family: lower_value is compile_expr then unwrap_value, whose code reads
   no GAS (unwrap_value_origin_ptr).
 *
 * TOP-LEVEL:
 *   expr_sim_full_of_vv -- expr_sim_full from expr_vv_sim_full
 *)
Theory bodyFullOfVV
Ancestors
  bodyFullUnwrap bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasShadowCompile exprSimMemorySource exprSimDefs exprLowering
  exprLoweringProps loweringPosts compileEnv context vyperTypeSystem
  vyperAST vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

Theorem expr_sim_full_of_vv:
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es ==>
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_def] >> rpt strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty (gas_shadow_expr e) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (vv', shadow_sm)` >> simp[] >> strip_tac >>
  `vv' = vv /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`cenv`,`ty`,`e`,`T`] mp_tac (cj 1 gas_shadow_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qpat_assum `compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >> fs[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  suspend "read"
QED

Resume expr_sim_full_of_vv[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>

  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `sm`, `sc` |-> `sb`, `G` |-> `G1`,
    `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL unwrap_value_origin_ptr)) >>
  impl_tac >- simp[] >>
  suspend "unwrap"
QED

Resume expr_sim_full_of_vv[unwrap]:
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Finalise expr_sim_full_of_vv
