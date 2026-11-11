(* The singleton encoder consumes the forced expression result.  Using
   lower_value here includes storage/code conversion as well as memory VVs. *)
Theory bodyAbiEncodeMemorySource
Ancestors
  abiBuiltinEncodeWord abiBuiltinDispatchCorrect externalReturnLiveWindowResources exprSimMemDefs
  exprSimUnwrapProps abiEncoderLiveSource loweringPosts exprSimProps
  exprLowering compileEnv context vyperAST venomState words exprOperandVar gasOutcome

Theorem compile_abi_encode_forced_source_trace:
  ~is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (src,ready) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty
    (AbiEncode F mid) ret_ty [e] origin = (vv,final) ==>
  ?out. lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) src
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) ready = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[lower_value_def, compile_type_builtin_dispatch_body_def,
      comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule as_ptr_val_result >> simp[]
QED

(* The live footprint, not the nominal type capacity, is protected from
   every later recorded allocation.  Empty footprints need no pointer bound. *)
Theorem abi_encode_source_live_resources:
  expr_post ctx func ce cx e es sa sb s0 ee v src s /\
  expr_store_bound cx (expr_type e) v src s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  fn_inst_ids_distinct func ==>
  ?at rv w. eval_operand src s = SOME w /\
    abi_encoder_window_input ei at rv (w2n w) (val_footprint tv v) s.vs_memory /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound (get_tenv cx) (expr_type e) /\
    (val_footprint tv v = 0 \/
     w2n w + val_footprint tv v <= s.vs_alloca_next) /\
    (!inst x b sz. MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
      not_local_ptr ce ee.scopes x /\ sb.cs_next_id <= inst.inst_id /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz))
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee s /\
   expr_val_at ce cx (expr_type e) sa sb ee v src s /\
   expr_val_rel cx (expr_type e) v src s` by fs[expr_post_def] >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  drule_all abi_encoder_live_source_window >> strip_tac >>
  qexistsl_tac [`at`, `rv`, `w`] >> asm_rewrite_tac[] >> conj_tac
  >- (mp_tac (Q.SPECL [`tv`, `v`] val_footprint_le_store_size) >>
      fs[expr_store_bound_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_0]) >>
  rpt strip_tac >> irule externalReturnSourceWindowTheory.expression_source_window_disjoint >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

(* Source preparation is a postcondition refinement of the recursive forced
   judgment.  ABI typing/plan facts are supplied at the actual source endpoint. *)
Theorem abi_encode_forced_source_outcome:
  expr_sim_mem ctx func ce cx (expr_type e) e es /\
  ~is_word_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (src,ready) /\
  compile_type_builtin_dispatch_body compile_expr ce vv_ty ty
    (AbiEncode F mid) ret_ty [e] sa = (vv,final) /\
  fn_has_code sa ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  (!v ee s. expr_post ctx func ce cx e es sa ready s0 ee v src s ==>
     value_has_type tv v /\ ?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av) ==>
  ?out. lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) src
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) ready = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory) /\
    (!x. src = Var x ==> not_fresh_at ready x) /\
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      (\res ee s. ?v at rv w av. res = INL v /\
        expr_post ctx func ce cx e es sa ready s0 ee v src s /\
        expr_store_bound cx (expr_type e) v src s /\
        s.vs_current_bb = ready.cs_current_bb /\
        s.vs_inst_idx = LENGTH ready.cs_current_insts /\
        alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
        vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
        eval_operand src s = SOME w /\
        abi_encoder_window_input ei at rv (w2n w) (val_footprint tv v) s.vs_memory /\
        enc at rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
        LENGTH (enc at rv) <= vyper_abi_size_bound (get_tenv cx) (expr_type e) /\
        (val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= s.vs_alloca_next) /\
        (!inst x b sz. MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
          not_local_ptr ce ee.scopes x /\ ready.cs_next_id <= inst.inst_id /\
          FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
          venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz)))
      (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all compile_abi_encode_forced_source_trace >> strip_tac >>
  qexists_tac `out` >> asm_rewrite_tac[] >> conj_tac
  >- (drule compiler_lower_value_var >>
      metis_tac[cj 1 compiler_compile_var]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE[expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `ready`, `src`, `s0`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> irule gas_outcome_post_mono >>
  qpat_assum `gas_outcome _ _ _ _ _ _ _` (fn th => irule_at Any th) >>
  simp_tac bool_ss [] >> rpt strip_tac >>
  `value_has_type tv v /\ ?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[] >>
  drule_all abi_encode_source_live_resources >> strip_tac >>
  qexistsl_tac [`v`, `at`, `rv`, `w`, `av`] >> asm_rewrite_tac[]
QED
