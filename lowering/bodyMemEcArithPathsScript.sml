(* Counted memory paths for the concrete EC scratch/precompile runs. *)
Theory bodyMemEcArithPaths
Ancestors
  bodyMemEcArithInstructionSafety bodyMemEcArithResultBounds exprSimECArith
  bodyMemBiMethodIdSuffix bodyMemBiSha256Compose exprSimVVFrame
  bodyMemEcArithContinuation exprLowering exprSimWordArgs vyperContext
  fragGasSeqAbort fragGasSeqMem exprLoweringProps compileEnv
  venomInstProps venomExecSemantics exprSimDefs loweringPosts fragExec loweringStateRelDefs

Theorem ec_counted_success_mem:
  (compile_ecadd_points p q sa = (op,sb) \/
   compile_ecmul_point p q sa = (op,sb)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  vv_post ctx func cenv cx e es sa sb s es' (Value v) vv t /\
  vv = LocatedValue (expr_type e) rp /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lowered_value_type cenv e = expr_type e ==>
  ?u n. gas_marked_path T ctx func s n (OK u) /\
    vv_post ctx func cenv cx e es sa sb s es' (Value v) vv u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es'
      (Value v) vv u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by metis_tac[ec_points_code_shape] >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all method_id_run_path_mem >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[sha256_run_inst_seq_alloca_next_mono] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       run_inst_seq_preserves_field)) >> goal_assum (drule_at Any) >>
     rpt strip_tac >> fs[listTheory.EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexists_tac `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))` >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  simp[vv_post_inst_idx] >>
  metis_tac[ec_result_vv_store_bound, vv_post_inst_idx]
QED

Theorem ec_counted_revert_mem:
  (compile_ecadd_points p q sa = (op,sb) \/
   compile_ecmul_point p q sa = (op,sb)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
  ?n rr. gas_marked_path T ctx func s n rr /\
    exit_result rr /\ expr_exit (INR (Error (RuntimeError msg))) rr
Proof
  strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by metis_tac[ec_points_code_shape] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     REFL_TAC) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (Q.SPEC `T` run_inst_seq_abort_gas_path) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[exit_result_def, expr_exit_def]
QED

Theorem ecmul_points_path_mem:
  compile_ecmul_point p scalar sa = (op,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!i. MEM i (emitted_insts sa sb) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME sw /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sa z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (BaseTV (UintT 256)) k /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (BaseT (UintT 256)) k scalar s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v p s /\
  w2n point + 64 < dimword (:256) /\ w2n point + 64 <= s.vs_alloca_next /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lowered_value_type cenv e = expr_type e /\
  ec_source_tail cx (expr_type e) ECMul
    [ArrayT (BaseT (UintT 256)) (Fixed 2); BaseT (UintT 256)] [v;k] es = (r,es') /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s ==>
  ?n rr. gas_marked_path T ctx func s n rr /\
    ((?t a. rr = OK t /\ r = INL a /\
        vv_post ctx func cenv cx e es sa sb s es' a
          (FST (as_ptr_val (expr_type e) LocMemory (op,sb))) t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' a
          (FST (as_ptr_val (expr_type e) LocMemory (op,sb))) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) \/
     (exit_result rr /\ expr_exit r rr))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all ecmul_insts_mem_ok >> simp[]) >>
  `es.outcomes = SOME s.vs_outcomes` by fs[stmt_state_rel_def, state_rel_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  drule_all (cj 1 ec_points_run) >> disch_tac >>
  drule_all (cj 1 ec_memory_semantics) >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `vfmExecution$ecmul coords scalarword` >>
  Cases_on `vfmExecution$ecmul coords scalarword`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      (irule ec_counted_revert_mem >> metis_tac[])) >>
  PairCases_on `x` >>
  Cases_on `s.vs_outcomes`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      (irule ec_counted_revert_mem >> metis_tac[])) >>
  rename1 `s.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ec_counted_success_mem >>
       simp[as_ptr_val_def] >> metis_tac[])) >>
  gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
  (irule ec_counted_revert_mem >> metis_tac[])
QED

Theorem ecadd_points_path_mem:
  compile_ecadd_points p q sa = (op,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!i. MEM i (emitted_insts sa sb) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  (!z. MEM (Var z) [p;q] ==> not_fresh_at sa z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 q s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v p s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v2 q s /\
  w2n point + 64 < dimword (:256) /\ w2n point2 + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next /\ w2n point2 + 64 <= s.vs_alloca_next /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lowered_value_type cenv e = expr_type e /\
  ec_source_tail cx (expr_type e) ECAdd
    [ArrayT (BaseT (UintT 256)) (Fixed 2); ArrayT (BaseT (UintT 256)) (Fixed 2)]
    [v;v2] es = (r,es') /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s ==>
  ?n rr. gas_marked_path T ctx func s n rr /\
    ((?t a. rr = OK t /\ r = INL a /\
        vv_post ctx func cenv cx e es sa sb s es' a
          (FST (as_ptr_val (expr_type e) LocMemory (op,sb))) t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' a
          (FST (as_ptr_val (expr_type e) LocMemory (op,sb))) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) \/
     (exit_result rr /\ expr_exit r rr))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all ecadd_insts_mem_ok >> simp[]) >>
  `es.outcomes = SOME s.vs_outcomes` by fs[stmt_state_rel_def, state_rel_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  drule_all (cj 2 ec_points_run) >> disch_tac >>
  qpat_assum `expr_val_rel _ _ v p s`
    (mp_then (Pat `expr_val_rel _ _ _ _ _`) mp_tac (cj 2 ec_memory_semantics)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `vfmExecution$ecadd coords coords2` >>
  Cases_on `vfmExecution$ecadd coords coords2`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      irule ec_counted_revert_mem >> metis_tac[]) >>
  PairCases_on `x` >>
  Cases_on `s.vs_outcomes`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      irule ec_counted_revert_mem >> metis_tac[]) >>
  rename1 `s.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
      drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ec_counted_success_mem >>
      simp[as_ptr_val_def] >> metis_tac[]) >>
  gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
  irule ec_counted_revert_mem >> metis_tac[]
QED
