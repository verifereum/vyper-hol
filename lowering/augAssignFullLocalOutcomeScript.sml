(* Local AugAssign continuation at the selected joint RHS endpoint.
   Compilation states match stmtSimAugAssign.augassign_local_code_parts:
   sa --MLOAD--> se --RHS--> sb --binop--> sc --MSTORE--> sf. *)
Theory augAssignFullLocalOutcome
Ancestors
  augAssignFullLocalStorePost augAssignFullOperator augAssignFullSource
  augAssignFullLocalNumeric augAssignFullLocalSuccessSource
  augAssignFullLocalSuccessFrame augAssignFullLocalWriteOutcome
  augAssignFullStateFrame augAssignFullHistory gasOutcomeFullCompose
  gasOutcomeFullRunning bodyFullMemoryFrames bodySimFull stmtSimAugAssign
  exprSimSource exprSimHypsDefs exprSimProps exprLoweringProps exprBopSimProps
  stmtSimAugAssignAttr exprSimExtract32Post loweringSlice vyperState
  fragExec exprSimDefs bodyFullGhostFrame loweringStateRelDefs stmtSimDeclStore stmtSimDefs
  bodyPtrBopScalarRun exprBopStraight augAssignPtrScalarCertificate augAssignPtrCompiler
  exprLowering stmtLowering compileEnv loweringPosts bodyPtrDefs
  freshWrites varsExt ptrDiscipline venomState finite_map list pred_set

Theorem augassign_local_rhs_operands_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ bop <> In /\ bop <> NotIn /\ cur = entry.value /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\ cs_extends se sb /\
  eval_operand lhs s = SOME (val_to_w256 cur) /\
  (!z. lhs = Var z ==> not_fresh_at se z) /\ (!l. lhs <> Label l) /\
  op_prov G lhs = NONE /\ op_taint tn lhs = {} /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    ptr_val_ok cx (post_value_type cenv e) v rhs G1 tn1 t /\
    ghost_kept_at lo cenv es se G tn s G1 tn1) ==>
  eval_operand lhs t = SOME (val_to_w256 entry.value) /\
  eval_operand rhs t = SOME (val_to_w256 v) /\
  op_prov G1 lhs = NONE /\ op_taint tn1 lhs = {} /\
  op_prov G1 rhs = NONE /\ op_taint tn1 rhs = {} /\
  (!z. lhs = Var z ==> not_fresh_at sb z) /\
  (!z. rhs = Var z ==> not_fresh_at sb z) /\
  (!l. lhs <> Label l /\ rhs <> Label l)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `well_typed_binop ty bop ty (expr_type e)` by
    (gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  `word_value_type (expr_type e)` by metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `op_prov G1 rhs = NONE /\ op_taint tn1 rhs = {}` by fs[ptr_val_ok_def] >>
  `op_prov G1 lhs = NONE /\ op_taint tn1 lhs = {}` by
    (fs[ghost_kept_at_def] >> Cases_on `lhs` >> fs[op_prov_def, op_taint_def]) >>
  `eval_operand lhs t = SOME (val_to_w256 entry.value)` by
    (fs[expr_post_def] >> Cases_on `lhs` >> fs[eval_operand_def] >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e
    es se sb s (mid with gas_obs := []) v rhs t` by
    simp[extract32_expr_post_end_gas_obs] >>
  drule_all augassign_attr_rhs_word_operand >> disch_tac >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem augassign_local_numeric_abort_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  word_value cur /\ ~t.vs_halted /\
  bop_result cx ty bop [ty;expr_type e] cur v mid = INR (Error (RuntimeError msg)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  (!D lo. allocas_from lo t /\ lo <= t.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (Abort Revert_abort (u with vs_inst_idx := j),Gf,tf)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur v)) (write_place cx (MemoryPlace id [])))
    (mid,t,G1,tn1)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv' sf u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `bop <> In /\ bop <> NotIn` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `!bs. cur <> BytesV bs` by (Cases_on `cur` >> gvs[word_value_def]) >>
  `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur v = INR (RuntimeError msg)` by
    (`bop_result cx ty bop [ty;expr_type e] cur v mid =
       case evaluate_binop
         (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
         ptv bop cur v of INL w => INL w | INR err => INR (Error err)` by
       (irule bop_result_augassign >> simp[]) >>
     gvs[AllCaseEqs()]) >>
  irule gas_outcome_full_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl [`Gf`, `mid`, `Abort Revert_abort (u with vs_inst_idx := j)`,
    `INR (Error (RuntimeError msg))`, `tf`] >>
  simp[bind_def, lift_sum_def, raise_def, exit_result_def,
    stmt_exit_ptr_def, expr_exit_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[ghost_inv_at_def]
QED

Theorem augassign_local_numeric_success_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\ cur = entry.value /\ ptv = entry.type /\
  (!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
    (INL (MemoryPlace id []),es with gas_obs := gs) /\
    read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL cur,es with gas_obs := gs) /\
    place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL ptv,es with gas_obs := gs)) /\
  emit_op MLOAD [Var p] sa = (lhs,se) /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\
  fn_has_code sb sc func /\ fn_has_code sc sf func /\
  cs_extends sa se /\ cs_extends se sb /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!z. not_fresh_at sa z ==> lookup_var z s = lookup_var z s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv es s /\
    MAP FDOM es.scopes = MAP FDOM es0.scopes) /\
  return_buf_frame d cenv se s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  expr_sim_inv cenv cx env mid /\ word_value cur /\
  bop_result cx ty bop [ty;expr_type e] cur v mid = INL w /\ word_value w /\
  value_has_type entry.type w /\ storage_trace_domain cx st0 mid.storage_trace /\
  ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ghost_kept_at lo cenv es se G tn s G1 tn1) /\
  run_inst_seq (emitted_insts sb sc) t = OK u /\
  eval_operand op u = SOME (val_to_w256 w) /\ u = t with vs_vars := u.vs_vars /\
  (!z. not_fresh_at sb z ==> lookup_var z u = lookup_var z t) /\
  (!D lo. allocas_from lo t /\ lo <= t.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts),Gu,tu)) /\
  (!z. not_fresh_at sb z ==> FLOOKUP Gu z = FLOOKUP G1 z /\
    op_taint tu (Var z) = op_taint tn1 (Var z)) /\
  tu.t_mem = tn1.t_mem /\ tu.t_stor = tn1.t_stor /\
  tu.t_trans = tn1.t_trans /\ tu.t_imm = tn1.t_imm /\
  op_prov Gu op = NONE /\ op_taint tu op = {} ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur v)) (write_place cx (MemoryPlace id [])))
    (mid,t,G1,tn1)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv' sf u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  drule_all augassign_local_success_source_full >> strip_tac >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `q = u with vs_inst_idx := LENGTH sc.cs_current_insts` by simp[Abbr `q`] >>
  mp_tac (SPEC_ALL augassign_local_success_store_inputs_full) >>
  (impl_tac >- (simp[Abbr `q`] >> metis_tac[])) >> strip_tac >>
  Cases_on `write_place cx (MemoryPlace id []) w (mid with gas_obs := [])` >>
  rename1 `_ = (wr,fin)` >>
  `!m. wr <> INR (Error (TypeError m))` by metis_tac[] >>
  `eval_operand op q = SOME (typed_val_to_w256 entry.type w)` by
    simp[typed_val_to_w256_word_value] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  `MAP FDOM mid.scopes = MAP FDOM es0.scopes` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid q /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gu tu q /\
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv mid q` by metis_tac[] >>
  simp[lift_sum_def, bind_return] >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  qexistsl_tac [`Gu`,`q`,`tu`] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      `allocas_from lo t /\ lo <= t.vs_alloca_next` by metis_tac[ghost_inv_at_def] >>
      first_x_assum irule >> simp[Abbr `q`]) >>
  qpat_x_assum `u = t with vs_vars := _` kall_tac >>
  qpat_x_assum `q = u with vs_inst_idx := _` kall_tac >>
  irule augassign_local_write_outcome_full >> simp[] >>
  rpt conj_tac
  >- (qexists_tac `es0` >> simp[] >> metis_tac[])
  >- (qexistsl_tac [`bop`,`e`,`ret_ty`,`ty`] >> simp[]) >>
  qexistsl_tac [`entry.type`,`op`,`sc`] >> simp[]
QED

Theorem augassign_local_entry_word_full:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\
  lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ word_value entry.value
Proof
  rpt strip_tac >>
  `FLOOKUP env.var_types id = SOME ty /\ word_value_type ty` by
    (fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs(),
        vyperTypeSystemTheory.well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[well_typed_binop_augassign_word]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def,
      vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type] >>
  metis_tac[word_value_type_typed]
QED

Theorem augassign_local_continuation_ready_full[local]:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\
  cur = entry.value /\ ptv = entry.type /\
  (!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
    (INL (MemoryPlace id []),es with gas_obs := gs) /\
    read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL cur,es with gas_obs := gs) /\
    place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL ptv,es with gas_obs := gs)) /\
  emit_op MLOAD [Var p] sa = (lhs,se) /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\
  fn_has_code se sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func /\
  cs_extends sa se /\ cs_extends se sb /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  eval_operand lhs s = SOME (val_to_w256 cur) /\
  (!z. lhs = Var z ==> not_fresh_at se z) /\
  (!l. lhs <> Label l) /\ op_prov G lhs = NONE /\ op_taint tn lhs = {} /\
  (!z. not_fresh_at sa z ==> lookup_var z s = lookup_var z s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv es s /\
    MAP FDOM es.scopes = MAP FDOM es0.scopes) /\
  return_buf_frame d cenv se s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  expr_sim_inv cenv cx env mid /\ FLOOKUP env.var_types id = SOME ty /\
  word_value_type ty /\ bop <> In /\ bop <> NotIn /\
  (!w. bop_result cx ty bop [ty;expr_type e] entry.value v mid = INL w ==>
    value_has_type entry.type w) /\
  ((?w. bop_result cx ty bop [ty;expr_type e] entry.value v mid = INL w /\
    word_value w /\
    !x y sa sb op ss.
      compile_binop bop x y ty NONE (if bop = Exp then expr_int_literal e else NONE) sa = (op,sb) /\
      fresh_vars_wrt sa ss /\
      eval_operand x ss = SOME (val_to_w256 entry.value) /\
      eval_operand y ss = SOME (val_to_w256 v) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
        eval_operand op ss' = SOME (val_to_w256 w)) \/
   (?msg. bop_result cx ty bop [ty;expr_type e] entry.value v mid = INR (Error (RuntimeError msg)) /\
    !x y sa sb op ss.
      compile_binop bop x y ty NONE (if bop = Exp then expr_int_literal e else NONE) sa = (op,sb) /\
      fresh_vars_wrt sa ss /\
      eval_operand x ss = SOME (val_to_w256 entry.value) /\
      eval_operand y ss = SOME (val_to_w256 v) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    expr_store_bound cx (expr_type e) v rhs t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v rhs G1 tn1 t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs G1 t) /\
    ghost_kept_at lo cenv es se G tn s G1 tn1) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur v)) (write_place cx (MemoryPlace id [])))
    (mid,t,G1,tn1)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv' sf u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `well_typed_binop ty bop ty (expr_type e)` by
    (gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    ptr_val_ok cx (post_value_type cenv e) v rhs G1 tn1 t /\
    ghost_kept_at lo cenv es se G tn s G1 tn1` by metis_tac[] >>
  drule_all augassign_local_rhs_operands_full >> strip_tac >>
  drule_all typed_binop_scalar_member_ptr >> disch_tac >>
  `straight_fresh (compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE))` by
    metis_tac[compile_binop_straight_fresh_ptr] >>
  `!z. lhs = Var z ==> not_fresh_at sb z` by
    metis_tac[not_fresh_at_mono] >>
  `!l. lhs <> Label l /\ rhs <> Label l` by metis_tac[] >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)
    compile_binop_clean_certificate_ptr >>
  disch_then (qspecl_then [`tn1`, `G1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all binop_numeric_origin_ptr_continuation >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
  drule_all augassign_local_entry_word_full >> strip_tac >>
  reverse strip_tac
  >- (irule augassign_local_numeric_abort_full >>
      simp[] >>
      conj_tac >- metis_tac[] >>
      metis_tac[]) >>
  `value_has_type entry.type v'` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ghost_kept_at lo cenv es se G tn s G1 tn1` by metis_tac[] >>
  irule augassign_local_numeric_success_full >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G`,`G'`,`e`,`entry`,`env`,`env'`,`es`,`es0`,`marks`,
    `op`,`ret_ty`,`rhs`,`s`,`sb`,`sc`,`tn`,`tn'`,`t'`,`v'`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED


Theorem augassign_local_continuation_full:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e) sa = (cenv,sf) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\
  cur = entry.value /\ ptv = entry.type /\
  (!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
    (INL (MemoryPlace id []),es with gas_obs := gs) /\
    read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL cur,es with gas_obs := gs) /\
    place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
      (INL ptv,es with gas_obs := gs)) /\
  emit_op MLOAD [Var p] sa = (lhs,se) /\
  lower_value compile_expr cenv ty e se = (rhs,sb) /\
  compile_binop bop lhs rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sb = (op,sc) /\
  emit_void MSTORE [Var p;op] sc = ((),sf) /\
  fn_has_code se sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func /\
  cs_extends sa se /\ cs_extends se sb /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  eval_operand lhs s = SOME (val_to_w256 cur) /\
  (!z. lhs = Var z ==> not_fresh_at se z) /\
  (!l. lhs <> Label l) /\ op_prov G lhs = NONE /\ op_taint tn lhs = {} /\
  (!z. not_fresh_at sa z ==> lookup_var z s = lookup_var z s0) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
    op_taint tn (Var z) = op_taint tn0 (Var z)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    alloca_frame cenv es0 sa s0 cenv es s /\
    MAP FDOM es.scopes = MAP FDOM es0.scopes) /\
  return_buf_frame d cenv se s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es se sb s mid v rhs t /\
    expr_store_bound cx (expr_type e) v rhs t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v rhs G1 tn1 t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs G1 t) /\
    ghost_kept_at lo cenv es se G tn s G1 tn1) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur v)) (write_place cx (MemoryPlace id [])))
    (mid,t,G1,tn1)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv' sf u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
        op_taint tf (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  drule_all augassign_local_numeric_ready_full >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule augassign_local_continuation_ready_full >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G`,`e`,`entry`,`env`,`env'`,`es`,`es0`,`marks`,`op`,
    `ret_ty`,`rhs`,`s`,`sb`,`sc`,`tn`] >> simp[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED
