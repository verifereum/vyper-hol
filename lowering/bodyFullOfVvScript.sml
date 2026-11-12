(* The value judgment from the vv judgment: lower_value is compile_expr
   then unwrap_value, whose code reads no GAS.  The shared joint
   unwrap_value lemma and the shadow side's compile spine are premises
   until they land.
 *
 * TOP-LEVEL: expr_sim_full_of_vv
 *)
Theory bodyFullOfVv
Ancestors
  logArgsRunPtr fragGasOrigin fragGasMode fragGasPath
  bodySimFull exprLowering compileEnv gasOutcomeFullCompose gasOutcomeFull
  gasShadowState exprSimMemorySource exprSimUnwrap exprOperandVar
  exprLoweringProps gasExemptCert gasContext exprSimDefs fragExec
  vyperEvalExprPreservesScopesDom vyperState

Theorem expr_sim_full_of_vv:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
       compile_expr cenv ty e sa = (vv,sm) /\
       sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
       unwrap_value cenv vv sb = (op,sc) /\
       local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
       fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
       ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
       (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
       (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       ~is_word_type (post_value_type cenv e) ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
       type_memory_size rt < 2**64) /\
       evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
       (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
       vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
       vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv_at D lo d cenv cx ee G tn s /\
       ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
       (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op0 G s) /\
       (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
       (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory rt val (w2n w) mem)) /\
       ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
       (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
       ?v H tf z.
       read_result cx tv ee = (INL v, ee) /\
       gas_origin_ptr_path (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       (s, G, tn) [] (OK z, H, tf) /\
       expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
       expr_store_bound cx (post_value_type cenv e) v op z /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\
       alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at D lo d cenv cx ee H tf z /\
       ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
       (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand op z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
       ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
       (!x. not_fresh_at sb x ==>
            lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
            op_taint tf (Var x) = op_taint tn (Var x)) /\
       wb_frame cenv ee sb s z /\
       ghost_kept_at lo cenv ee sb G tn s H tf) /\
  (!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
             (compile_expr cenv ty' (gas_shadow_expr e))) /\
  post_value_type cenv e = expr_type e /\
  (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
        ~is_word_type (expr_type e) ==>
        type_memory_bytes cenv (expr_type e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
  expr_sim_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_def] >> rpt strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv ty (gas_shadow_expr e) _ = _`
    mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (vv', shadow_sm)` >> simp[] >> strip_tac >>
  `vv' = vv /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `!ty' e. gas_shadow_compiles _ _`
       (qspecl_then [`ty`,`e`] mp_tac) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qpat_assum `compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >>
     simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  match_mp_tac gas_outcome_full_bind >> conj_tac
  >- (drule_then match_mp_tac gas_outcome_full_post_source >> conj_tac
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >> suspend "read") >>
      rpt gen_tac >> Cases_on `res` >> simp[] >>
      metis_tac[expr_exit_INR_type]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule gas_exempt_cert_bind_result >> simp[] >>
  disch_then irule >> simp[]
QED

Resume expr_sim_full_of_vv[read]:
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := xs) = (INL tv,ee)` by
    metis_tac[listTheory.APPEND_NIL] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    metis_tac[] >>
  qpat_x_assum `!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
                  compile_expr _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`e`,`ty`,`sa`,`vv`,`sm`,`sm`,`op`,`sb`,`es`,`ee`,`s0`,`t`,
                  `tv`,`rty`,`G'`,`tn'`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
  strip_tac >>
  rename1 `read_result cx tv ee = (INL rv,ee)` >>
  drule read_result_gas_obs >> strip_tac >>
  irule gas_outcome_full_pure >>
  first_assum (irule_at Any) >>
  qexistsl_tac [`INL rv`,`ee`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  BETA_TAC >> simp[] >> gvs[]
QED

Finalise expr_sim_full_of_vv
