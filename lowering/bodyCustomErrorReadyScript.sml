(* Source typing and actual allocation resources for custom-error arguments. *)
Theory bodyCustomErrorReady
Ancestors
  bodyCustomErrorSource exprSimHypsDefs logArgumentTypeEval logDataPacking
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeABI
  vyperTypeSystem vyperTypeInvariants vyperValue vyperTyping
  stmtSimLogAllocate stmtSimCustomErrorStore abiCallerTupleLayout
  valueEncodingProps bodyCustomErrorWindowBounds abiTupleValueEncoding arithmetic words list finite_map

Theorem custom_error_args_type_evaluations:
  expr_sim_inv ce cx env es /\ well_typed_exprs env args ==>
  ?tvs. OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  drule_all checked_exprs_type_evaluations >> strip_tac >>
  qexists_tac `tvs` >> irule log_evaluate_types >>
  simp[LIST_REL_MAP1, combinTheory.o_DEF] >> gvs[]
QED

Theorem custom_error_args_source_typed:
  expr_sim_inv ce cx env es /\ well_typed_exprs env args /\
  call_evaluation_safe cx (int_calls_exprs args) /\
  type_memory_bytes ce (TupleT (MAP expr_type args)) < 2 ** 64 /\
  eval_exprs cx args es = (INL vs,ee) ==>
  ?tvs av.
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT (MAP expr_type args)) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    vyper_to_abi (get_tenv cx) (TupleT (MAP expr_type args))
      (ArrayV (TupleV vs)) = SOME av
Proof
  strip_tac >>
  `exprs_runtime_typed env args vs` by
    (fs[expr_sim_inv_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  fs[exprs_runtime_typed_def] >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs` by
    (irule log_evaluate_types >> simp[LIST_REL_MAP1, combinTheory.o_DEF] >> gvs[]) >>
  `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv)
      (MAP expr_type args) tvs` by
    (fs[LIST_REL_MAP1] >> irule LIST_REL_mono >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     gvs[combinTheory.o_DEF] >>
     drule_all custom_error_expr_inv_memory_size >> simp[]) >>
  drule abi_caller_memory_size_list >> strip_tac >>
  `type_slot_size (TupleTV tvs) <= dimword(:256)` by
    (gvs[compileEnvTheory.type_memory_bytes_def, type_memory_size_slots,
         type_slot_size_def, wordsTheory.dimword_def] >>
     rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> decide_tac) >>
  `evaluate_type (get_tenv cx) (TupleT (MAP expr_type args)) = SOME (TupleTV tvs)` by
    simp[evaluate_type_def, evaluate_types_OPT_MMAP] >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by
    fs[value_has_type_def, abi_values_have_types] >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >> gvs[]
QED

Theorem custom_error_buffer_immutable_frame:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,cap) /\
  off + type_memory_size_list tvs <= cap ==>
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs))
Proof
  rpt strip_tac >> drule_all log_buffer_clear_of_immutable >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem custom_error_raise_source_ready:
  body_inv tops ctx ce cx /\ custom_error_resolved [(NONE,tops)] err /\
  expr_sim_inv ce cx env es /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok ce (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_exprs (custom_error_exprs err)) /\
  eval_exprs cx (custom_error_exprs err) es = (INL vs,ee) ==>
  ?id positional kwargs params tvs av.
    err = CustomError id positional kwargs /\
    ce.ce_error_info (nsid_to_string id) = SOME params /\
    MAP expr_type (custom_error_exprs err) = MAP SND params /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP SND params) = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT (MAP SND params)) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    vyper_to_abi (get_tenv cx) (TupleT (MAP SND params))
      (ArrayV (TupleV vs)) = SOME av
Proof
  Cases_on `err` >> strip_tac >>
  drule_all custom_error_body_resolution >> strip_tac >>
  `well_typed_exprs env (custom_error_exprs (CustomError p l l0))` by
    gvs[type_stmt_def, well_typed_custom_error_def, AllCaseEqs()] >>
  `type_memory_bytes ce (TupleT (MAP expr_type (custom_error_exprs (CustomError p l l0)))) < 2 ** 64` by
    gvs[bodySimTheory.stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
        allocLimitsTheory.custom_error_alloc_ok_def] >>
  drule_all custom_error_args_source_typed >> strip_tac >>
  metis_tac[]
QED
