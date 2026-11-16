(* Immediate-read nonword snapshots on the joint judgment. *)
Theory bodyFullExtCallRequestSnapshotFullLocated
Ancestors
  bodyFullExtCallRequestPositional bodyFullExtCallRequestSource
  bodyFullPreds gasOutcomeFullCompose gasOutcomeFull bodySimFull
  exprSimMemDefs loweringPosts bodyPtrDefs gasShadowCompile compileEnv
  exprSimUnwrap exprSimMemorySource fragExec exprLowering exprSimDefs stmtSimProps
  exprSimHyps exprSimSource bodyMemoryDefs fragGasOriginPtr
  exprPtrUnwrapStorageShape abiEncodeMaterialize bodyPtrIfExpMemoryTransport exprSimConvert
  contextRawReachable ptrDiscipline unitMemInv

(* Retain the allocation/local witness when the argument is retagged. *)
Theorem extcall_snapshot_owned_retag:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx (post_value_type ce e) sa sb ee raw vv s ==>
  vv_at ce cx (lowered_value_type ce e) sa sb ee raw
    (ext_call_arg_value (lowered_value_type ce e) vv) s
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >>
     Cases_on `e = Call ty (IntCall fid) args drv` >> gvs[expr_has_effect_thm]) >>
  Cases_on `lowered_value_type ce e = expr_type e`
  >- (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_at_def]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by
    metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word,
      membership_element_word_boundary] >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     qexistsl [`cx`,`es`,`ee`] >> simp[vyperStateTheory.bind_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?dv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dv /\
        value_has_type dv v` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  suspend "ownership"
QED

Resume extcall_snapshot_owned_retag[ownership]:
  `expr_val_at ce cx (expr_type e) sa sb ee v (vv_operand vv) s` by
    (Cases_on `vv`
     >- gvs[vv_at_def, contextTheory.vv_operand_def] >>
     rename1 `LocatedValue tag p` >>
     `p.ptr_location = LocMemory` by
       metis_tac[compile_nonmemory_lowered_value_type] >>
     gvs[contextTheory.vv_operand_def] >>
     irule exprSimPropsTheory.vv_at_memory_val_at >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (vv_operand vv) s` by
    (irule valueCopyBytesTheory.expr_val_at_bytestring_transport >> metis_tac[]) >>
  Cases_on `vv`
  >- gvs[ext_call_arg_value_def, vv_at_def, contextTheory.vv_operand_def] >>
  rename1 `LocatedValue tag p` >>
  `p.ptr_location = LocMemory` by
    metis_tac[compile_nonmemory_lowered_value_type] >>
  suspend "source"
QED

Resume extcall_snapshot_owned_retag[source]:
  `?val. raw = Value val` by
    (Cases_on `e`
     >~ [`eval_expr cx (Literal _ _) es = _`]
     >- metis_tac[exprSimPropsTheory.eval_expr_literal_value]
     >~ [`eval_expr cx (Builtin _ _ _) es = _`]
     >- metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value]
     >~ [`eval_expr cx (TypeBuiltin _ _ _ _) es = _`]
     >- metis_tac[exprSimConvertTheory.eval_expr_type_builtin_value]
     >~ [`eval_expr cx (Call _ _ _ _) es = _`]
     >- (rename1 `Call ann target args dr` >> Cases_on `target` >>
         gvs[lowered_value_type_def, vyperASTTheory.expr_type_def, expr_has_effect_thm]) >>
     gvs[lowered_value_type_def, vyperASTTheory.expr_type_def]) >>
  gvs[ext_call_arg_value_def, contextTheory.vv_operand_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_x_assum `expr_val_at ce cx (lowered_value_type ce e) _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, expr_val_at_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def]
QED

Finalise extcall_snapshot_owned_retag

Theorem extcall_request_snapshot_located_classified_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (sv,sm0) /\
         sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    metis_tac[] >>
  gvs[comp_bind_def] >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (shadow_vv,shadow_sm)` >>
  `shadow_vv = vv /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`cenv`, `expr_type e`, `e`, `T`] mp_tac
       (cj 1 gas_shadow_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[compile_snapshot_vv_def, comp_return_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  drule forced_expr_admissible_raw >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by simp[] >>
  `!fn inst s. frag_reachable ctx func s0 fn inst s ==>
     dalloca_no_wrap inst s` by
    (rpt strip_tac >> drule_all frag_reachable_members >>
     gvs[ctx_has_dalloca_def, dalloca_no_wrap_def, listTheory.EXISTS_MEM] >>
     metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> disch_then drule_all >>
  strip_tac >> suspend "read"
QED

Resume extcall_request_snapshot_located_classified_full[read]:
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
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  suspend "normal"
QED

Resume extcall_request_snapshot_located_classified_full[normal]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  Cases_on `read_result cx tv ee` >>
  rename1 `read_result cx tv ee = (read_res,read_state)` >>
  drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  Cases_on `read_res`
  >- (rename1 `read_result cx tv ee = (INL v,ee)` >> suspend "package") >>
  metis_tac[vv_post_failed_read]
QED

Resume extcall_request_snapshot_located_classified_full[package]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G1`,`ee`,`INL v`,`t`,`tn1`] >>
  simp[] >> conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` drule >>
  strip_tac >> simp[gas_origin_ptr_path_rules] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >>
     Cases_on `e = Call ty (IntCall fid) args drv` >> gvs[expr_has_effect_thm]) >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `(is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e))` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `vv_holds cenv cx (post_value_type cenv e) tv shadow_vv ee t` by
    metis_tac[vv_post_def] >>
  drule_all bodyIntCallJointPureSourceTheory.effect_free_eval_expr_frame >>
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `compile_expr _ _ e sa = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >>
     gvs[vv_post_def]) >>
  suspend "representation"
QED

Resume extcall_request_snapshot_located_classified_full[representation]:
  `vv_holds cenv cx (lowered_value_type cenv e) tv
     (ext_call_arg_value (lowered_value_type cenv e) shadow_vv) ee t /\
   ptr_vv_ok cx (lowered_value_type cenv e) tv
     (ext_call_arg_value (lowered_value_type cenv e) shadow_vv) ee G1 tn1 t` by
    (Cases_on `shadow_vv`
     >- (rename1 `StackValue tag op` >>
         Cases_on `is_word_type (expr_type e)`
         >- (`lowered_value_type cenv e = expr_type e` by
               metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word,
                 membership_element_word_boundary] >>
             gvs[ext_call_arg_value_def]) >>
         suspend "stack") >>
     rename1 `LocatedValue tag p` >>
     `~is_word_type (expr_type e)` by
       gvs[ext_call_arg_value_def, contextTheory.vv_type_def] >>
     irule extcall_snapshot_located_retag >> metis_tac[]) >>
  suspend "frame"
QED

Resume extcall_request_snapshot_located_classified_full[stack]:
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     qexistsl [`cx`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`ee`] >>
     simp[vyperStateTheory.bind_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?dv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dv /\
        value_has_type dv v` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- gvs[ext_call_arg_value_def] >>
  gvs[ext_call_arg_value_def, vv_holds_def, ptr_vv_ok_def] >>
  conj_tac
  >- (gvs[expr_val_rel_def] >>
      metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]) >>
  gvs[ptr_val_ok_def] >>
  metis_tac[bodyPtrIfExpMemoryTransportTheory.ptr_mem_ok_bytestring_transport]
QED

Resume extcall_request_snapshot_located_classified_full[frame]:
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
     (ext_call_arg_value (lowered_value_type cenv e) shadow_vv) t` by
    (Cases_on `shadow_vv` >> gvs[ext_call_arg_value_def, vv_store_bound_def]) >>
  `vv_storage_live H cx
     (ext_call_arg_value (lowered_value_type cenv e) shadow_vv) ee t` by
    (Cases_on `shadow_vv` >- simp[ext_call_arg_value_def] >>
     rename1 `LocatedValue tag p` >>
     Cases_on `p.ptr_location = LocMemory`
     >- simp[ext_call_arg_value_def] >>
     `lowered_value_type cenv e = expr_type e` by
       metis_tac[compile_nonmemory_lowered_value_type] >>
     `tag = expr_type e` by gvs[vv_holds_def] >>
     gvs[ext_call_arg_value_def, vv_post_def]) >>
  `!tag op. ext_call_arg_value (lowered_value_type cenv e) shadow_vv = StackValue tag op /\
     ~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t` by
    (Cases_on `shadow_vv` >> gvs[ext_call_arg_value_def]) >>
  `!tag p. ext_call_arg_value (lowered_value_type cenv e) shadow_vv = LocatedValue tag p /\
     p.ptr_location = LocMemory ==> ptr_buf_ok cenv e p.ptr_operand G1 t` by
    (Cases_on `shadow_vv` >> gvs[ext_call_arg_value_def]) >>
  suspend "ctor"
QED

Resume extcall_request_snapshot_located_classified_full[ctor]:
  `cenv.ce_is_ctor /\
   vv_location (ext_call_arg_value (lowered_value_type cenv e) shadow_vv) = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand (ext_call_arg_value (lowered_value_type cenv e) shadow_vv)) t =
       SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
       val_in_memory rt v (w2n w) mem)` by
    (Cases_on `shadow_vv`
     >- simp[ext_call_arg_value_def, contextTheory.vv_location_def] >>
     rename1 `LocatedValue raw_tag p` >>
     gvs[ext_call_arg_value_def, contextTheory.vv_location_def,
         contextTheory.vv_operand_def] >> strip_tac >>
     `lowered_value_type cenv e = expr_type e` by
       (irule compile_nonmemory_lowered_value_type >>
        qexistsl [`p`,`sa`,`sb`,`raw_tag`,`expr_type e`] >> simp[]) >>
     gvs[] >> metis_tac[]) >>
  `((?tag op0. ext_call_arg_value (lowered_value_type cenv e) shadow_vv = StackValue tag op0) \/
       (?p. ext_call_arg_value (lowered_value_type cenv e) shadow_vv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p sm0. ext_call_arg_value (lowered_value_type cenv e) shadow_vv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (ext_call_arg_value (lowered_value_type cenv e) shadow_vv,sm0) /\
         sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id))` by
    (Cases_on `shadow_vv`
     >- simp[ext_call_arg_value_def] >>
     rename1 `LocatedValue tag p` >>
     Cases_on `p.ptr_location = LocMemory`
     >- gvs[ext_call_arg_value_def, contextTheory.vv_type_def] >>
     `lowered_value_type cenv e = expr_type e` by
       metis_tac[compile_nonmemory_lowered_value_type] >>
     `tag = expr_type e` by gvs[vv_holds_def] >>
     gvs[ext_call_arg_value_def, contextTheory.vv_type_def] >>
     qexists_tac `sb` >> simp[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sb ee tv shadow_vv t` by
    metis_tac[vv_post_def] >>
  drule_at (Pat `eval_expr _ _ _ = _`) extcall_snapshot_owned_retag >>
  disch_then drule_all >> strip_tac >>
  gvs[vv_post_def] >>
  qexists_tac `tv` >> simp[] >>
  metis_tac[]
QED

Finalise extcall_request_snapshot_located_classified_full

(* The published owned interface remains the exact weakening. *)
Theorem extcall_request_snapshot_located_owned_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all extcall_request_snapshot_located_classified_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED



(* The original scalar interface remains the exact weakening. *)
Theorem extcall_request_snapshot_located_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all extcall_request_snapshot_located_owned_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >> qexists_tac `raw` >> simp[]
QED

