Theory exprSimAbiDecodeCompose
Ancestors
  exprSimAbiDecodeCallerSuffix exprSimAbiDecodeBodySuccess
  exprSimAbiDecodeEntryTyping exprSimHyps exprOpenFirstOperand
  exprSimSource exprSimDefs exprSimHypsDefs gasSummaryCompose gasSummary gasExemptCert
  gasOutcome gasNormalPrefix vyperState vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTyping vyperValue compileEnv loweringPosts
  exprSimMemDefs vyperStorageFootprint gasStorage fragGasMode fragGasPath
  exprSimAbiDecodeBodyEntry vyperTypeEvalSoundness vyperTypeSystem allocLimits
  vyperTypeCallGraph vyperTypeCallStackSoundness

(* The decode step reads the forced bytes and leaves the state alone. *)
Theorem abi_decode_value_state[local]:
  bind (lift_sum x) (\w. return (Value w)) st = (res, st') ==> st' = st
Proof
  Cases_on `x` >> simp[bind_def, lift_sum_def, return_def, raise_def]
QED

Theorem abi_decode_operand_pre_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty (e::es)) st ==>
  expr_body_pre_mods mods ce cx env e st
Proof
  simp[expr_body_pre_mods_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_thm,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.call_operands_effect_root_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem abi_decode_pre_mods_gas_obs:
  expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods ce cx env e es
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

(* The decode continuation after the forced operand, in the guarded
   horizon form: the operand's post holds at every valid horizon, and the
   decoder's post is moved from one horizon to all of them. *)
Theorem abi_decode_suffix_outcome:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func ce cx e es sa start s0 (ee with gas_obs := []) v data s /\
     s.vs_current_bb = start.cs_current_bb /\
     s.vs_inst_idx = LENGTH start.cs_current_insts) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]))
      (\w. return (Value w))) (ee with gas_obs := [],s)
    (\H res es1 t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es sa final s0
        es1 tv (LocatedValue ty (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts)
    (\H res es1 r. expr_exit res r)
Proof
  strip_tac >>
  `~s.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `?H0. valid_horizon cx st0 H0 ee.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `expr_body_pre_mods mods ce cx env e es` by
    metis_tac[abi_decode_operand_pre_mods] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule_all abi_decode_body_operand_evaluates >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_mods_def, expr_sim_inv_mods_def]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       metis_tac[abi_decode_inv_type_env, expr_body_pre_mods_def] >>
     fs[value_runtime_typed_def] >>
     Cases_on `v` >> gvs[value_has_type_def]) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule abi_decode_observed_scopes_dom >> simp[]) >>
  `expr_post H0 ctx func ce cx e es sa start s0 (ee with gas_obs := []) (BytesV bs) data s /\
   s.vs_current_bb = start.cs_current_bb /\
   s.vs_inst_idx = LENGTH start.cs_current_insts` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx (ee with gas_obs := []) s /\
     storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (rpt strip_tac >> res_tac >> fs[expr_post_def]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (data,start)` by
    metis_tac[] >>
  drule_all abi_decode_caller_suffix_summary >>
  rewrite_tac[gas_summary_at_def,
              ASSUME ``expr_type e = BaseT (BytesT (Dynamic n))``] >>
  strip_tac >>
  `es_end with gas_obs := [] = ee with gas_obs := []` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[gas_explicit_def] >> strip_tac >>
     drule abi_decode_value_state >> simp[]) >>
  `es_end.storage_trace = ee.storage_trace` by
    (pop_assum (mp_tac o Q.AP_TERM `\x. x.storage_trace`) >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl_tac [`res`, `es_end`, `r`] >>
  (conj_tac >| [first_assum ACCEPT_TAC, ALL_TAC])
  >- (disj1_tac >> qexists_tac `t` >> simp[] >>
      qpat_x_assum `(\res es1 t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
      gvs[] >> gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      mp_tac (Q.SPECL [`H0`, `H`, `ctx`, `func`, `ce`, `cx`,
        `TypeBuiltin ty (AbiDecode unwrap) ty [e]`, `es`, `sa`, `final`, `s0`,
        `ee with gas_obs := []`, `Value v`,
        `LocatedValue ty (mk_ptr out LocMemory)`, `t`, `s`]
        vv_post_fields_transport) >>
      impl_tac >- (gvs[] >> simp[vv_storage_live_def, contextTheory.mk_ptr_def]) >>
      simp[])
  >- (disj2_tac >> gvs[])
QED

(* The decode continuation cannot produce HaltException; retain this fact
   alongside its ordinary exit relation for finite-horizon consumers. *)
Theorem abi_decode_suffix_full_exit_outcome:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func ce cx e es sa start s0 (ee with gas_obs := []) v data s /\
     s.vs_current_bb = start.cs_current_bb /\
     s.vs_inst_idx = LENGTH start.cs_current_insts) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]))
      (\w. return (Value w))) (ee with gas_obs := [],s)
    (\H res es1 t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es sa final s0
        es1 tv (LocatedValue ty (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts)
    (\H res es1 r. expr_exit res r /\ halt_exit H cx es1 res r)
Proof
  strip_tac >> drule_all abi_decode_suffix_outcome >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks'`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- (rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`res`, `es_end`, `r`] >> gvs[])
      >> `res <> INR HaltException` by
        (qpat_x_assum `gas_marked_exec _ _ (bind (lift_sum _) _) _ _ _ _ _`
           (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
         strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
         Cases_on `evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]` >>
         simp[bind_def, lift_sum_def, return_def, raise_def] >>
         strip_tac >> gvs[]) >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> gvs[halt_exit_def] >>
      disj2_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
