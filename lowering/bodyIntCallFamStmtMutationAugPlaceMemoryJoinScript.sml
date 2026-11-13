(* Counted loaded-memory-place RHS continuation. *)
Theory bodyIntCallFamStmtMutationAugPlaceMemoryJoin
Ancestors
  bodyIntCallFamStmtMutationAugPlaceSuffix augAssignPlaceSourceMemory
  bodyIntCallFamStmtMutationAugPlaceMemorySuffix
  augAssignPlaceSourcePrefix exprSimSliceCompose exprBopSimProps
  exprBopSimDefs exprSimHypsDefs exprSimSource stmtSimAugAssignPlaceMemory
  bodyIntCallJointContract compileEnv valueEncodingProps stmtSimAugAssignPlace stmtSimAugAssign

Theorem intcall_aug_place_memory_outcome:
  intcall_forced_producer fp e /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_program fp.jc_tops /\
  get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmt fp.jc_tops bindings (AugAssign ty bt bop e) /\
  supported_target_info fp.jc_tops bindings bt = SOME info /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AugAssign ty bt bop e)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env /\
  expr_sim_inv ce fp.jc_cx env es /\ ce.ce_alloca_locals /\
  ce_locals_declared ce env /\ expr_body_pre ce fp.jc_cx env e mid /\
  (!tail. eval_target_place fp.jc_cx bt (es with gas_obs := prefix ++ tail) =
    (INL (MemoryPlace id path),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt fp.jc_cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  read_place fp.jc_cx (MemoryPlace id path) mid = (INL old,mid) /\
  place_type_value fp.jc_cx (MemoryPlace id path) mid = (INL tv,mid) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv old /\
  type_bits ty MOD 8 = 0 /\ word_value_type ty /\ word_value_type (expr_type e) /\
  IS_SOME (evaluate_type (get_tenv fp.jc_cx) (expr_type e)) /\
  lower_value compile_expr ce ty e sl = (rhsop,s2) /\
  compile_binop bop cur rhsop ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  fn_has_code sl s2 fp.jc_func /\ fn_has_code s2 s3 fp.jc_func /\
  fn_has_code s3 sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!z. cur = Var z ==> not_fresh_at sl z) /\
  (!z. dst = Var z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
  eval_operand dst u = SOME w /\
  place_ptr_rel ce fp.jc_cx u (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  intcall_expr_res fp ce env mid sl u /\
  ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
  u.vs_inst_idx = LENGTH sl.cs_current_insts /\
  emit_void MSTORE [dst;result] s3 = ((),sf) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place fp.jc_cx (MemoryPlace id path)))) (mid,u)
    (\res ff t. res = INL () /\ intcall_joint_res fp ce env ff sf t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z v. not_fresh_at sl z /\ lookup_var z u = SOME v ==> lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      u.vs_alloca_next <= t.vs_alloca_next)
    (\res ff r. intcall_stmt_exit fp res ff r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok mid` by metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `intcall_forced_producer fp e` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >> disch_then drule_all >>
  disch_then (mp_then Any assume_tac aug_place_outcome_with_exec) >>
  irule aug_place_outcome_bind_value >>
  irule slice_gas_outcome_conseq >>
  goal_assum (drule_at (Pat `gas_outcome`)) >>
  conj_tac >- suspend "exception" >> suspend "normal"
QED

Resume intcall_aug_place_memory_outcome[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
      (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) = (INL v,raw with gas_obs := tail)` by
    gvs[gasSummaryTheory.gas_marked_exec_def] >>
  suspend "rhs_ready"
QED

Resume intcall_aug_place_memory_outcome[rhs_ready]:
  `bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings) =
     (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `eval_target_place fp.jc_cx bt
     (es with gas_obs := prefix ++ gas_explicit marks u.vs_gas_readings) =
     (INL (MemoryPlace id path),mid with gas_obs := gas_explicit marks u.vs_gas_readings)` by
    simp[] >>
  drule_all aug_place_rhs_memory_live >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env e
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings)` by simp[] >>
  drule_all aug_place_rhs_suffix_ready >> strip_tac >>
  suspend "source_callback"
QED

Resume intcall_aug_place_memory_outcome[source_callback]:
  `word_value old` by metis_tac[word_value_type_typed] >>
  drule_all aug_place_memory_reads_replay >> strip_tac >>
  drule_all aug_place_rhs_suffix_admissible >> strip_tac >>
  drule_all aug_place_memory_rhs_callback >>
  disch_then (qspecl_then [`fp.jc_func`,`fp.jc_ctx`] strip_assume_tac) >>
  suspend "backend_ready"
QED

Resume intcall_aug_place_memory_outcome[backend_ready]:
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  `eval_operand rhsop t = SOME (val_to_w256 v)` by
    (qpat_assum `expr_val_rel _ _ v rhsop t`
       (mp_then Any mp_tac expr_val_rel_word) >>
     simp[loweringPostsTheory.post_value_type_word]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func u (LENGTH marks) (OK t)` by
    gvs[gasSummaryTheory.gas_marked_exec_def] >>
  `eval_operand cur t = SOME (val_to_w256 old)` by
    (irule aug_place_saved_operand >>
     gvs[intcall_expr_cont_def,exprSimPropsTheory.typed_val_to_w256_word_value] >>
     metis_tac[]) >>
  `eval_operand dst t = SOME w` by
    (irule aug_place_saved_operand >> fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `place_ptr_rel ce fp.jc_cx t (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >>
     qexistsl [`u`,`sl`] >> fs[intcall_expr_cont_def,intcall_expr_res_def]) >>
  suspend "pure_suffix"
QED

Resume intcall_aug_place_memory_outcome[pure_suffix]:
  drule aug_place_typing >> strip_tac >>
  `bop_result fp.jc_cx ty bop [ty;expr_type e] old v (raw with gas_obs := []) =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop old v of INL x => INL x | INR err => INR (Error err)` by
    (irule stmtSimAugAssignTheory.bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  `binop_frag_words fp.jc_ctx fp.jc_func ce fp.jc_cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE) [ty;expr_type e] old v
     (val_to_w256 old) (val_to_w256 v) (raw with gas_obs := [])` by
    (qpat_x_assum `!func ctx. _` (qspecl_then [`fp.jc_func`,`fp.jc_ctx`] mp_tac) >>
     simp[binop_frag_def]) >>
  suspend "callbacks"
QED

Resume intcall_aug_place_memory_outcome[callbacks]:
  `!vv ff. bop_result fp.jc_cx ty bop [ty;expr_type e] old v
      (raw with gas_obs := []) = INL vv /\
      write_place fp.jc_cx (MemoryPlace id path) vv (raw with gas_obs := []) = (INL (),ff) ==>
      expr_sim_inv ce fp.jc_cx env ff` by
    (rpt strip_tac >>
     `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       tv bop old v = INL vv` by (gvs[AllCaseEqs()]) >>
     irule intcall_aug_place_source_replay_landing >>
     metis_tac[]) >>
  suspend "store_callback"
QED

Resume intcall_aug_place_memory_outcome[store_callback]:
  `!tt vv ff.
    gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK tt) /\
    intcall_expr_cont fp ce env (raw with gas_obs := []) s2 t
      (raw with gas_obs := []) s3 tt /\
    eval_operand result tt = SOME (val_to_w256 vv) /\ word_value vv /\
    value_has_type tv vv /\
    write_place fp.jc_cx (MemoryPlace id path) vv (raw with gas_obs := []) = (INL (),ff) /\
    expr_sim_inv ce fp.jc_cx env ff ==>
    ?r. gas_marked_path F fp.jc_ctx fp.jc_func tt 0 (OK r) /\
      intcall_joint_res fp ce env ff sf r /\
      ~r.vs_halted /\ r.vs_current_bb = sf.cs_current_bb /\
      r.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z. lookup_var z r = lookup_var z tt) /\
      r.vs_allocas = tt.vs_allocas /\ r.vs_alloca_next = tt.vs_alloca_next` by
    (rpt strip_tac >>
     `eval_operand result tt = SOME (typed_val_to_w256 tv vv)` by
       simp[exprSimPropsTheory.typed_val_to_w256_word_value] >>
     `local_ptrs_reserved ce s2` by
       fs[intcall_expr_cont_def,intcall_expr_res_def] >>
     `!z. dst = Var z ==> not_fresh_at s2 z` by metis_tac[] >>
     drule_all intcall_aug_memory_store_cont >> simp[]) >>
  suspend "compose_suffix"
QED

Resume intcall_aug_place_memory_outcome[compose_suffix]:
  `!z. cur = Var z ==> not_fresh_at s2 z` by metis_tac[] >>
  `intcall_expr_res fp ce env (raw with gas_obs := []) s2 t /\
    ~t.vs_halted /\ t.vs_current_bb = s2.cs_current_bb /\
    t.vs_inst_idx = LENGTH s2.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `!vv. bop_result fp.jc_cx ty bop [ty;expr_type e] old v (raw with gas_obs := []) = INL vv ==>
    value_has_type tv vv /\ ?ff.
      write_place fp.jc_cx (MemoryPlace id path) vv (raw with gas_obs := []) = (INL (),ff)` by metis_tac[] >>
  drule_all intcall_aug_memory_suffix_outcome >>
  disch_then assume_tac >>
  irule slice_gas_outcome_conseq >>
  goal_assum (drule_at (Pat `gas_outcome`)) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  fs[intcall_expr_cont_def] >> metis_tac[]
QED

Resume intcall_aug_place_memory_outcome[exception]:
  rpt gen_tac >> Cases_on `res` >>
  simp[exprSimDefsTheory.expr_exit_INL,intcall_stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Finalise intcall_aug_place_memory_outcome
