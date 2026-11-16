(* EC arithmetic uses a single joint child/staging/suffix execution.
   The memory aggregate unwrap emits no instructions. *)
Theory bodyFullBuiltinECArith
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull bodyFullUnwrapIdentity
  bodyInvNoDalloca stmtSimProps exprSimECArith bodyFullBuiltinECArithCompose
  bodyFullBuiltinECArithSuffix bodyFullBuiltinECArithStaging
  gasOutcomeFull gasOutcomeFullCompose gasShadowCompile
  exprSimHypsDefs exprSimHyps exprSimSource exprSimUnwrap exprSimMemorySource
  exprLowering loweringPosts compileEnv vyperAST list

val _ = Parse.hide "body";

Theorem ec_arith_builtin_vv_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  match_mp_tac ec_arith_vv_from_tail_full >>
  match_mp_tac ec_arith_tail_full_from_staging >>
  MATCH_ACCEPT_TAC ec_arith_staging_full_conditional
QED

Theorem ec_arith_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `~ctx_has_dalloca ctx` by (drule body_inv_no_dalloca >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a bt args) es` by
    (match_mp_tac ec_arith_builtin_vv_sim_full >>
     qexistsl_tac [`tops`, `env`] >> asm_rewrite_tac []) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   ?e1 e2. args = [e1;e2]` by
    (Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qpat_x_assum `a = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `lower_value compile_expr cenv ty _ sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2]) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >>
  `?p. vv = LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ptr p LocMemory)` by
    (Cases_on `bt = ECAdd` >> gvs[] >>
     imp_res_tac compile_ec_operands >> gvs[as_ptr_val_def] >> metis_tac[]) >>
  qpat_x_assum `lower_value compile_expr cenv ty (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (gas_shadow_expr (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2])) shadow_sa` >>
  rename1 `_ = (shadow_vv,shadow_sm)` >> simp[] >> strip_tac >>
  `shadow_vv = vv /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`cenv`,`ty`,`Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2]`,`T`] mp_tac
       (cj 1 gas_shadow_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `bt = ECAdd \/ bt = ECMul` kall_tac >>
  fs[unwrap_value_def, comp_return_def, contextTheory.mk_ptr_def, is_word_type_def] >>
  `shadow_sm = shadow_sb` by
    (qpat_assum `unwrap_value _ _ shadow_sm = _` mp_tac >>
     gvs[unwrap_value_def, comp_return_def, contextTheory.mk_ptr_def, is_word_type_def]) >>
  qpat_assum `compile_expr _ _ (Builtin _ _ _) sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  `fn_has_code sm sm func` by
    (qspecl_then [`sa`,`sm`,`sm`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[cs_extends_refl]) >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. vv_operand (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ptr p LocMemory)) = Var x ==>
       not_fresh_at sm x` by
    (qpat_assum `compile_expr _ _ (Builtin _ _ _) sa = _`
       (mp_then (Pos hd) mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.mk_ptr_def]) >>
  `gas_admissible (eval_expr cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2])) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
     `LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ptr p LocMemory)`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[contextTheory.mk_ptr_def] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      simp[] >> disch_then irule >> simp[])
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> first_assum ACCEPT_TAC)
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res`
      >- gvs[] >>
      fs[exprSimDefsTheory.halt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  suspend "memory_read"
QED

Resume ec_arith_builtin_sim_full[memory_read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> fs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >> fs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
     value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v` by
    (rpt strip_tac >>
     `expr_body_pre cenv cx env (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2])
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all expr_body_pre_runtime_typed >>
     simp[expr_type_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2]) es sa sm s0 ee tv
        (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ptr p LocMemory)) s /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [
    `e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt [e1;e2]`,
    `vv` |-> `LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ptr op LocMemory)`,
    `t` |-> `ArrayT (BaseT (UintT 256)) (Fixed 2)`, `p` |-> `mk_ptr op LocMemory`,
    `rty` |-> `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`,
    `sb` |-> `sm`, `sc` |-> `sm`, `G` |-> `G1`, `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] (SPEC_ALL unwrap_memory_origin_ptr)) >>
  (impl_tac >-
    (gvs[unwrap_value_def, comp_return_def, contextTheory.mk_ptr_def, is_word_type_def,
       expr_type_def, post_value_type_def, vyperValueTheory.evaluate_type_def,
       type_memory_bytes_def, valueEncodingTheory.type_memory_size_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> fs[expr_type_def]
QED

Finalise ec_arith_builtin_sim_full
