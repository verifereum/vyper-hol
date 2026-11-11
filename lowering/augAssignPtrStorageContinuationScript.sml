(* Target-independent clean storage continuation boundaries. *)
Theory augAssignPtrStorageContinuation
Ancestors
  augAssignPtrOperator augAssignPtrStorageStore augAssignPtrStorageSource
  augAssignPtrStorageCommon stmtSimAssignStorage stmtSimProps stmtSimDeclMem
  stmtSimAugAssign exprBopSimProps exprSimSource exprSimProps
  vyperStorageBackend vyperTypeBuiltins vyperTypeSystem vyperTypeValues
  vyperInterpreter vyperState vyperValueOperation vyperScopePreservation
  bodyPtrDefs loweringPosts exprLoweringProps accountsRelProps
  codegenRel compileEnv loweringStateRelDefs fragExec loweringSlice emitHelperProps emitHelper
  venomInst venomState venomExecSemantics ptrDiscipline
  fragGasPathPtr gasSummaryComposePtr wordArgsPtr

Theorem augassign_clean_storage_store_ptr:
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv frame_es origin G0 tn0 s0 G tn /\
  (!w st. storage_dead cx tr (update_storage slot w st) = storage_dead cx tr st) /\
  encode_value tv result = SOME [(0,typed_val_to_w256 tv result)] /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv result) /\
  op_taint tn dst = {} /\ op_taint tn op = {} ==>
  ?fin H tm t.
    write_storage_slot cx tr slot tv result es = (INL (),fin) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    stmt_state_rel ctx func cenv cx fin t /\ ghost_inv d cenv cx fin H tm t /\
    ghost_kept cenv frame_es origin G0 tn0 s0 H tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~block_is_terminated sb /\
    t.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static /\
   s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `?fin. write_storage_slot cx tr slot tv result es = (INL (),fin)` by
    simp[write_storage_slot_eq] >>
  `stmt_state_rel ctx func cenv cx fin
     (if tr then tstore slot (typed_val_to_w256 tv result) s
      else sstore slot (typed_val_to_w256 tv result) s)` by
    (drule_at (Pat `write_storage_slot _ _ _ _ _ _ = _`)
       (cj 2 stmt_state_rel_write_storage_word) >>
     disch_then drule_all >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (if tr then tstore slot (typed_val_to_w256 tv result) s
         else sstore slot (typed_val_to_w256 tv result) s)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, mk_inst_def] >>
     once_rewrite_tac[step_inst_base_def] >>
     Cases_on `tr` >> simp[exec_write2_def, eval_operands_def]) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts sa sb) s = OK last` >>
  `last.vs_allocas = s.vs_allocas /\ last.vs_fmp = s.vs_fmp /\
   last.vs_requests = s.vs_requests` by
    (Cases_on `tr` >> simp[Abbr `last`, sstore_def, tstore_def]) >>
  drule_all emit_storage_store_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  `fin.scopes = es.scopes` by metis_tac[write_storage_slot_scopes] >>
  suspend "post"
QED

Resume augassign_clean_storage_store_ptr[post]:
  `!k b. storage_dead cx tr
     (update_storage slot (typed_val_to_w256 tv result)
       (if tr then contract_transient s else contract_storage s)) k b =
     storage_dead cx tr
       (if tr then contract_transient s else contract_storage s) k b` by simp[] >>
  drule_at (Pat `s.vs_call_ctx.cc_address = _`) ghost_inv_storage_word_store >>
  disch_then drule_all >>
  disch_then (qspec_then `LENGTH sb.cs_current_insts` assume_tac) >>
  qabbrev_tac `store_tn =
    if tr then tn with t_trans := key_update tn.t_trans slot {}
    else tn with t_stor := key_update tn.t_stor slot {}` >>
  `ghost_inv d cenv cx fin G store_tn
      (last with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[Abbr `last`, Abbr `store_tn`] >>
  `ghost_kept cenv frame_es origin G0 tn0 s0 G store_tn` by
    (simp[Abbr `store_tn`] >> irule ghost_kept_storage_word_store >> simp[]) >>
  `~block_is_terminated sb` by
    (irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[is_terminator_def]) >>
  qexistsl [`fin`, `G`, `store_tn`, `last with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[Abbr `store_tn`] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  Cases_on `tr` >>
  gvs[Abbr `last`, sstore_def, tstore_def, lookup_var_def, stmt_state_rel_inst_idx]
QED

Finalise augassign_clean_storage_store_ptr

Theorem augassign_storage_clean_continuation_ptr:
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sa = (op,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  eval_operand cur s = SOME (val_to_w256 v) /\
  eval_operand rhs s = SOME (val_to_w256 v') /\ eval_operand dst s = SOME slot /\
  well_typed_binop ty bop ty (expr_type e) /\ type_bits ty MOD 8 = 0 /\
  (bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e = SOME n ==> v' = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. v' = IntV i /\ 0 <= i) /\
  word_value_type ty /\ word_value_type (expr_type e) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv' /\ value_has_type tv' v' /\
  bop <> In /\ bop <> NotIn /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] v v' es) /\
  (!l. cur <> Label l /\ rhs <> Label l /\ dst <> Label l) /\
  op_prov G cur = NONE /\ op_taint tn cur = {} /\
  op_prov G rhs = NONE /\ op_taint tn rhs = {} /\ op_taint tn dst = {} /\
  (!z. cur = Var z ==> not_fresh_at sa z) /\
  (!z. rhs = Var z ==> not_fresh_at sa z) /\
  (!z. dst = Var z ==> not_fresh_at sa z) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!w st. storage_dead cx tr (update_storage slot w st) = storage_dead cx tr st) ==>
  (?result fin H tm t.
    evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tv bop v v' = INL result /\
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        tv bop v v')) (write_storage_slot cx tr slot tv))
      (es,s,G,tn) [] (INL ()) fin H tm (OK t) /\
    stmt_state_rel ctx func cenv cx fin t /\ ghost_inv d cenv cx fin H tm t /\
    ghost_kept cenv es sa G tn s H tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~block_is_terminated sb /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w)) \/
  (?msg H tm t.
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        tv bop v v')) (write_storage_slot cx tr slot tv))
      (es,s,G,tn) [] (INR (Error (RuntimeError msg))) es H tm
      (Abort Revert_abort t))
Proof
  strip_tac >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  `!z. not_fresh_at sa z ==> not_fresh_at sa z` by simp[] >>
  `!l. cur <> Label l /\ rhs <> Label l` by simp[] >>
  drule augassign_clean_operator_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac)
  >- suspend "normal" >>
  suspend "abort"
QED

Resume augassign_storage_clean_continuation_ptr[normal]:
  rename1 `bop_result cx ty bop [ty;expr_type e] v v' es = INL result` >>
  `bop_result cx ty bop [ty;expr_type e] v v' es =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tv bop v v' of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     tv bop v v' = INL result` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)`
       mp_tac >> simp[CaseEq "sum"]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx es u` >>
  `eval_operand dst u = SOME slot` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `op_taint tm dst = {}` by
    (Cases_on `dst` >> fs[ghost_kept_def, op_taint_def]) >>
  `value_has_type tv result` by
    (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)
       well_typed_binop_success_type >>
     disch_then (fn th =>
       qpat_assum `well_typed_binop ty bop ty (expr_type e)`
         (mp_then (Pat `well_typed_binop _ _ _ _`) mp_tac th)) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `well_formed_type_value tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `encode_value tv result = SOME [(0,typed_val_to_w256 tv result)]` by
    (irule encode_value_word_typed >> simp[] >>
     qexistsl [`ty`, `get_tenv cx`] >> simp[]) >>
  `eval_operand op u = SOME (typed_val_to_w256 tv result)` by
    simp[typed_val_to_w256_word_value] >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`] >>
  drule_all augassign_clean_storage_store_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume augassign_storage_clean_continuation_ptr[compose]:
  `gas_path_ptr D 0 ctx func PG G tn s 0 H' tm' (OK t')` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tv bop v v')) (write_storage_slot cx tr slot tv) es = (INL (),fin)` by
    simp[lift_sum_def, bind_def, return_def] >>
  drule_all augassign_storage_continuation_exec_ptr >> strip_tac >>
  disj1_tac >> qexistsl [`result`, `fin`, `H'`, `tm'`, `t'`] >> simp[] >>
  simp[Abbr `u`]
QED

Resume augassign_storage_clean_continuation_ptr[abort]:
  `bop_result cx ty bop [ty;expr_type e] v v' es =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tv bop v v' of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tv bop v v' = INR (RuntimeError msg)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)`
       mp_tac >> simp[CaseEq "sum"]) >>
  `bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tv bop v v')) (write_storage_slot cx tr slot tv) es =
      (INR (Error (RuntimeError msg)),es)` by
    simp[lift_sum_def, bind_def, raise_def] >>
  drule_all augassign_storage_continuation_exec_ptr >> strip_tac >>
  disj2_tac >> goal_assum (drule_at Any)
QED

Finalise augassign_storage_clean_continuation_ptr
