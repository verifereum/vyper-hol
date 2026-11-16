(* Source-aware continuation at a loaded storage place. *)
Theory augAssignPlaceStorageContinuation
Ancestors
  augAssignPlaceLoadedContinuation augAssignPlaceSourcePrefix
  augAssignPlaceSourceMemory augAssignPlaceRhsContinuation
  exprSimProps exprSimSource exprSimHypsDefs exprSimLen
  stmtSimAugAssignPlaceStorage vyperState vyperStorageFootprint
  vyperStoragePlaceObserved vyperStorageTrace

Theorem aug_place_loaded_storage_suffix:
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e mid /\ expr_sim_mem ctx func cenv cx ty e mid /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL (StoragePlace tr slot tv),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  read_place cx (StoragePlace tr slot tv) mid = (INL old,mid) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
  type_bits ty MOD 8 = 0 /\ word_value_type ty /\
  word_value_type (expr_type e) /\ ~cx.txn.is_static /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (?offset tv0 path delta.
     MEM (StorageRoot tr offset tv0) mid.storage_trace /\
     storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta) /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;result] s3 = ((),sf) /\
  fn_has_code sl s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\
  local_ptrs_reserved cenv sl /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. cur = Var z ==> not_fresh_at sl z) /\
  (!z. dst = Var z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!l. cur <> Label l /\ dst <> Label l) /\
  eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
  eval_operand dst u = SOME slot /\
  place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
    (SOME (slot_loc tr)) (Type ty) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid u /\
       storage_well_formed_on cx mid (FST H)) /\
  alloca_history func u /\
  alloca_frame cenv es0 sa s0 cenv mid u /\ sa.cs_next_id <= sl.cs_next_id /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
  u.vs_inst_idx = LENGTH sl.cs_current_insts /\ ~block_is_terminated sf /\
  (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==> lookup_var z u = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (StoragePlace tr slot tv)))) (mid,u)
    (\H res ff v. res = INL () /\
      stmt_post H ctx func cx lctx cenv cenv sa sf es0 s0 res ff v /\
      alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next)
    (\H res ff r.
      (!tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r) /\
      halt_exit H cx ff res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?offset tv0 path delta. _` strip_assume_tac >>
  `!gs. read_place cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL old,mid with gas_obs := gs)` by simp[exprSimLenTheory.len_rp_obs] >>
  `!gs. place_type_value cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL tv,mid with gas_obs := gs)` by simp[place_type_value_def, return_def] >>
  drule_all aug_place_rhs_suffix_admissible >> strip_tac >>
  `word_value old` by metis_tac[word_value_type_typed] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rule_assum_tac (REWRITE_RULE [bind_assoc]) >>
  `emit_void (case slot_loc tr of LocStorage => SSTORE | LocTransient => TSTORE
                               | _ => MSTORE) [dst;result] s3 = ((),sf)` by
    (Cases_on `tr` >> fs[loweringPostsTheory.slot_loc_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       storage_place_observed H (StoragePlace tr slot tv)` by
    (gen_tac >> strip_tac >>
     irule aug_place_storage_rooted_observed >>
     goal_assum (drule_at (Pat `valid_horizon`)) >>
     qexistsl_tac [`delta`, `offset`, `path`, `tv0`] >> simp[]) >>
  mp_tac (Q.INST
    [`p` |-> `StoragePlace tr slot tv`, `ptv` |-> `tv`, `dtv` |-> `tv`,
     `es` |-> `mid`, `s0` |-> `u`, `s_entry` |-> `s0`, `s1` |-> `sl`,
     `x` |-> `cur`, `y` |-> `rhs`, `op` |-> `result`, `w` |-> `slot`,
     `loc` |-> `slot_loc tr`,
     `el` |-> `if bop = Exp then expr_int_literal e else NONE`]
    (Q.INST [`cur` |-> `old`] (SPEC_ALL aug_place_rhs_operator_write_mem))) >>
  impl_tac >- (
  simp[typed_val_to_w256_word_value, loweringPostsTheory.slot_loc_def] >>
  conj_tac >- (Cases_on `tr` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?xs. ee.storage_trace = mid.storage_trace ++ xs` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame] >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e) (read_result cx))`
       (fn frame =>
       qpat_assum `bind (eval_expr cx e) (read_result cx) (mid with gas_obs := _) =
                   (INL _,ee)`
         (fn eq => mp_tac (MATCH_MP vyperStorageTraceTheory.storage_trace_frame_prefix
                             (CONJ frame eq)))) >>
     simp[]) >>
  `MEM (StorageRoot tr offset tv0) ee.storage_trace` by simp[listTheory.MEM_APPEND] >>
  drule_all (SRULE [bind_assoc] aug_place_storage_rhs_callback) >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  qpat_assum `!v. bop_result _ _ _ _ _ _ _ = INL v ==> _`
    (qspec_then `v` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `ff` >>
  qpat_x_assum `slot = _` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `HH` >> strip_tac >>
  mp_tac (Q.INST [`H` |-> `HH`, `slot` |-> `n2w offset + n2w delta`]
    (SPEC_ALL aug_place_storage_store_wf)) >>
  impl_tac >- (simp[] >>
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  simp[]) >>
  simp[]
QED

(* A static storage suffix either exits in the operator or aborts at the store.
   No normal statement postcondition is needed in either case. *)
Theorem aug_place_static_operator_store_path:
  cx.txn.is_static /\ bop <> In /\ bop <> NotIn /\ word_value old /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] s3 = ((),sf) /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
    [ty;expr_type e] old rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] old rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!l. dst <> Label l) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv s2 /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H)) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  eval_operand x s = SOME (val_to_w256 old) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME slot ==>
  ?res r.
    (!tail. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop old rhs)) (write_place cx (StoragePlace tr slot tv))
      (ee with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
    gas_marked_path T ctx func s 0 r /\ exit_result r /\
    (!H tail. stmt_exit
      (RetQ (H : (bool # bytes32 # type_value) list # num list))
      (ee with gas_obs := tail) res r /\
      halt_exit H cx (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] old rhs ee =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop old rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule stmtSimAugAssignTheory.bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyBinopFamiliesMemoryTheory.binop_frag_val_mem_def,
                          bodyBinopFragMemoryTheory.binop_frag_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
  >- suspend "store"
  >> suspend "error"
QED

Resume aug_place_static_operator_store_path[store]:
  qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
  rename1 `eval_operand op t = SOME (val_to_w256 v)` >>
  `stmt_state_rel H0 ctx func cenv cx ee t` by metis_tac[] >>
  `t.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  `eval_operand dst t = SOME slot` by
    (irule exprBopSimPropsTheory.eval_operand_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`s2`, `s`] >> simp[]) >>
  drule_all storageStoreFrameTheory.storage_emit_static_path_memory >>
  disch_then (qspecl_then [`T`, `ctx`] assume_tac) >>
  `gas_marked_path T ctx func s 0
    (Abort ExHalt_abort (halt_state (set_returndata [] t)))` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
               `Abort ExHalt_abort (halt_state (set_returndata [] t))`] >>
  conj_tac >- (Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop old rhs` >>
    gvs[bind_def, lift_sum_def, return_def, raise_def,
        vyperPlaceFramesTheory.write_storage_place_eq]) >>
  simp[stmtSimDefsTheory.stmt_exit_def, exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def, fragExecTheory.exit_result_def]
QED

Resume aug_place_static_operator_store_path[error]:
  rpt (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop old rhs`
  >- gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `_ = INR err` >>
  qexistsl_tac [`INR (Error err)`, `r`] >>
  simp[bind_def, lift_sum_def, return_def, raise_def] >>
  rpt gen_tac >> simp[stmtSimDefsTheory.stmt_exit_def,
                       exprSimDefsTheory.halt_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
    stmtSimPropsTheory.expr_exit_INR_type] >> gvs[]
QED

Finalise aug_place_static_operator_store_path[local]

Theorem aug_place_loaded_storage_static_suffix:
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e mid /\ expr_sim_mem ctx func cenv cx ty e mid /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL (StoragePlace tr slot tv),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  read_place cx (StoragePlace tr slot tv) mid = (INL old,mid) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
  type_bits ty MOD 8 = 0 /\ word_value_type ty /\
  word_value_type (expr_type e) /\ cx.txn.is_static /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;result] s3 = ((),sf) /\
  fn_has_code sl s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\
  local_ptrs_reserved cenv sl /\ local_ptrs_reserved cenv s2 /\
  (!z. cur = Var z ==> not_fresh_at sl z) /\
  (!z. dst = Var z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!l. cur <> Label l /\ dst <> Label l) /\
  eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
  eval_operand dst u = SOME slot /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\
    storage_well_formed_on cx mid (FST H)) /\
  alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = sl.cs_current_bb /\
  u.vs_inst_idx = LENGTH sl.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (StoragePlace tr slot tv)))) (mid,u) Q
    (\H res ff r.
      (!tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r) /\
      halt_exit H cx ff res r)
Proof
  strip_tac >>
  `!gs. read_place cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL old,mid with gas_obs := gs)` by simp[exprSimLenTheory.len_rp_obs] >>
  `!gs. place_type_value cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL tv,mid with gas_obs := gs)` by simp[place_type_value_def, return_def] >>
  drule_all aug_place_rhs_suffix_admissible >> strip_tac >>
  `word_value old` by metis_tac[word_value_type_typed] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!z. rhs = Var z ==> not_fresh_at s2 z` by
    (gen_tac >> strip_tac >>
     irule exprOperandVarTheory.compile_lower_value_var >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`cenv`, `e`, `sl`, `ty`] >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sl`, `s2`, `rhs`, `u`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule stmtSimForcedTheory.forced_then_outcome >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> BETA_TAC >> conj_tac
      >- (simp[stmtSimDefsTheory.stmt_exit_def] >>
          ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
            stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
      gvs[exprSimDefsTheory.halt_exit_def]) >>
  conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts,
           vyperStorageTraceTheory.storage_trace_frame_write_place]) >>
  qexists_tac `\H v ee t. expr_post H ctx func cenv cx e mid sl s2 u ee v rhs t /\
    expr_store_bound cx (expr_type e) v rhs t /\
    t.vs_current_bb = s2.cs_current_bb /\
    t.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next` >>
  BETA_TAC >> conj_tac
  >- suspend "callback"
  >- first_assum ACCEPT_TAC
QED

Resume aug_place_loaded_storage_static_suffix[callback]:
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                    expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all aug_place_rhs_typed_memory_source >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  `eval_operand rhs t = SOME (val_to_w256 v)` by
    (drule_all exprSimWordArgsTheory.expr_post_word_operand >> simp[]) >>
  qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
  `eval_operand cur t = SOME (val_to_w256 old) /\
   eval_operand dst t = SOME slot` by
    (conj_tac >>
     (irule exprBopSimPropsTheory.eval_operand_frame >>
      conj_tac >- simp[] >> qexistsl_tac [`sl`, `u`] >>
      simp[typed_val_to_w256_word_value])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                       expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[loweringPostsTheory.expr_post_def] >> strip_tac >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (REWRITE_RULE [GSYM bind_assoc] aug_place_storage_binop_admissible) >>
  strip_tac >>
  `(!z. cur = Var z ==> not_fresh_at s2 z) /\
   (!z. dst = Var z ==> not_fresh_at s2 z)` by metis_tac[] >>
  `!l. dst <> Label l` by simp[] >>
  drule_all aug_place_static_operator_store_path >>
  disch_then (qspecl_then [`tv`, `RetQ`] strip_assume_tac) >>
  qexistsl_tac [`res`, `ee`, `r`] >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> simp[]
QED

Finalise aug_place_loaded_storage_static_suffix
