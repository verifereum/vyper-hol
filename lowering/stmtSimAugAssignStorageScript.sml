(*
 * Counted simulation of self.x op= e for word storage/transient variables.
 * The compiler stages are slot load, RHS, binary operator and slot store.
 * Source certificates must use AugAssign itself, not a synthetic assignment:
 * equality of source runs does not transport syntactic exempt certificates.
 *)

Theory stmtSimAugAssignStorage
Ancestors
  gasContext exprSimDefs vyperExprNoControl fragGasPath exprBopSimDefs
  gasExemptCert gasSummary fragGasMode fragGasPathMem fragGasSeq fragGasFresh
  freshWrites venomExecSemantics venomInst venomState
  exprSimUnwrap exprSimProps accountsRelProps
  vyperStorageLayoutSafety vyperStorageBackend
  exprBopSimProps
  exprSimSource
  exprSimHypsDefs
  stmtSimDefs
  loweringPosts
  allocLimits list finite_map
  fragExec  exprSimHyps exprSimOps exprSimOperators exprSimLeaves
  exprSimTopLevelProps
   stmtSimAssign stmtSimAssignMem stmtSimAssignStorage
  stmtSimAugAssign
  exprLowering exprBopLowering exprLoweringProps stmtLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  vyperTypeCallGraph vyperAST
Libs
  monadsyntax

(* ===== The source ===== *)

(* A storage or transient variable's target place is a StoragePlace at its
   layout slot, at its declared type. *)
Theorem eval_target_place_toplevel:
  !cx src id es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_target_place cx (TopLevelNameTarget (src, id)) es =
      (INL (StoragePlace tr (n2w slot) tvt), es) /\
    place_type_value cx (StoragePlace tr (n2w slot) tvt) es = (INL tvt, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, get_place_def, place_type_value_def]
QED

Theorem read_storage_slot_gas_obs:
  read_storage_slot cx tr slot tv es = (res, ee) ==>
  read_storage_slot cx tr slot tv (es with gas_obs := gs) =
    (res, ee with gas_obs := gs)
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def, bind_def,
       get_accounts_def, get_transient_storage_def]
  >- (Cases_on `decode_value (lookup_transient_storage cx.txn.target es.tStorage)
        (w2n slot) tv` >>
      simp[lift_option_def, return_def, raise_def] >> strip_tac >> gvs[return_def, raise_def]) >>
  Cases_on `decode_value (lookup_account cx.txn.target es.accounts).storage
    (w2n slot) tv` >>
  simp[lift_option_def, return_def, raise_def] >> strip_tac >> gvs[return_def, raise_def]
QED


(* Pointwise action boundary, not a certificate transport rule. *)
Theorem eval_augassign_toplevel_forced:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tvt bop v0 v);
      write_storage_slot cx tr (n2w slot) tvt r od) es
Proof
  strip_tac >> drule_all eval_target_place_toplevel >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       write_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_toplevel_rhs_exception:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
    (INR ex, ee)
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[Once bind_def]
QED

Theorem augassign_toplevel_rhs_normal:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt) ee
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem augassign_toplevel_rhs_admissible:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_admissible (eval_stmt cx
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `read_storage_slot cx tr (n2w slot) tvt (es with gas_obs := gs) =
     (INL v0, es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs] >>
  `eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
     (es with gas_obs := gs) = (INR ex, ee)` by
    (irule augassign_toplevel_rhs_exception >> metis_tac[]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem augassign_toplevel_binop_admissible:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee)
Proof
  strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee) <=>
   expr_res_ok (case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     tvt bop v0 v of INL w => INL w | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tvt bop v0 v` >- simp[expr_res_ok_def] >>
  rename1 `_ = INR err` >>
  `read_storage_slot cx tr (n2w slot) tvt (es with gas_obs := gs) =
     (INL v0, es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs] >>
  `eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
     (es with gas_obs := gs) = (INR (Error err), ee)` by
    (drule_all augassign_toplevel_rhs_normal >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  `stmt_res_ok lctx (INR (Error err))` by metis_tac[gas_admissible_result] >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_storage_load_path:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out. op = Var out /\
    gas_marked_path F ctx func s0 0
      (OK ((update_var out (if tr then tload slot s0 else sload slot s0) s0)
        with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sa.cs_current_bb = sb.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  gvs[fn_has_code_def] >>
  qmatch_asmsub_abbrev_tac `sa.cs_current_insts ++ [inst]` >>
  qmatch_goalsub_abbrev_tac `OK (last with vs_inst_idx := _)` >>
  `run_inst_seq [inst] s0 = OK last` by
    (Cases_on `tr` >>
     simp[Abbr `inst`, Abbr `last`, run_inst_seq_def, step_inst_base_def,
          mk_inst_def, exec_read1_def, eval_operand_def]) >>
  qspecl_then [`[inst]`, `s0`, `last`] mp_tac tuple_run_inst_seq_gas_path >>
  Cases_on `tr` >>
  simp[gas_marked_path_def, Abbr `inst`, mk_inst_def, is_terminator_def] >>
  disch_then irule >> qexists_tac `bb` >> simp[] >>
  qpat_x_assum `_ ++ [_] <<= _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
  pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem declared_storage_holds_value:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) /\
  contract_storage_well_formed cx es /\ storage_layout_safe cx /\
  stmt_state_rel ctx func cenv cx es s ==>
  storage_holds cx tr ty (Value v) (n2w slot) es s
Proof
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >> metis_tac[]) >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >> metis_tac[]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) (n2w slot) tvt` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]) >>
  gvs[storage_holds_def, read_result_def, return_def]
QED

Theorem augassign_storage_load_frame:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) slot es s0 /\
  evaluate_type (get_tenv cx) ty = SOME tvt ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
    eval_operand op t = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >> drule_all augassign_storage_load_path >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s0 0 (OK t)` >>
  qexists_tac `t` >>
  `stmt_state_rel ctx func cenv cx es t` by
    (simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `sa.cs_current_bb = sb.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  drule_all storage_holds_load >> strip_tac >>
  simp[Abbr `t`, update_var_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem augassign_toplevel_place_exec:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  gas_marked_path memory ctx func s0 0 (OK t) ==>
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0) [] (INL (StoragePlace tr (n2w slot) tvt)) es (OK t)
Proof
  strip_tac >> simp[gas_marked_exec_def, gas_explicit_def] >>
  gen_tac >> irule (cj 1 eval_target_place_toplevel) >> metis_tac[]
QED

Theorem augassign_toplevel_rhs_exempt:
  read_storage_slot cx tr slot tvt es = (INL v0, es) /\
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0) [] (INL (StoragePlace tr slot tvt)) es (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx
     (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (return ()) =
   do p <- eval_target_place cx (TopLevelNameTarget (src,id));
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec memory (ctx,func) (read_place cx (StoragePlace tr slot tvt))
     (es with gas_obs := [],t) [] (INL v0)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         metis_tac[read_storage_slot_gas_obs]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* Typed storage operands, independently of storage changes made by the RHS. *)
Theorem augassign_storage_binop_ready:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  well_formed_type env.type_defs ty /\
  read_storage_slot cx tr slot tvt es = (INL v0, es) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  value_has_type tvt v0 /\ word_value v0 /\ expr_sim_inv cenv cx env ee /\
  (!w. bop_result cx ty bop [ty; expr_type e] v0 v est = INL w ==>
       value_has_type tvt w) /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty; expr_type e] v0 v est
Proof
  strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `well_formed_type_value tvt` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type tvt v0` by
    metis_tac[vyperTypeStatePreservationTheory.read_storage_slot_success_type] >>
  `word_value v0` by metis_tac[word_value_type_typed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  conj_tac
  >- (gen_tac >>
      `bop_result cx ty bop [ty; expr_type e] v0 v est =
       case evaluate_binop
         (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
         tvt bop v0 v of
           INL w => INL w | INR err => INR (Error err)` by
        (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
      pop_assum SUBST1_TAC >>
      simp[AllCaseEqs()] >> strip_tac >>
      irule vyperTypeBuiltinsTheory.well_typed_binop_success_type >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`ty`, `expr_type e`, `get_tenv cx`, `tvt`, `tyv`, `ty`] >> simp[]) >>
  irule exprSimBinopFragTheory.binop_frag_word_typed >> simp[] >> conj_tac
  >- (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
      Cases_on `expr_int_literal e` >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`expr_type e`, `get_tenv cx`, `tvt`, `tyv`] >> simp[]
QED

Theorem augassign_storage_store_post_path:
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot); op] st = ((), sf) /\
  fn_has_code st sf func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee s /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ type_slot_size tvt = 1 /\
  is_word_type ty /\ value_has_type tvt w /\
  eval_operand op s = SOME (typed_val_to_w256 tvt w) /\
  (!x wd. not_fresh_at sa x /\ lookup_var x s0 = SOME wd ==>
          lookup_var x s = SOME wd) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es0 sa s0 cenv ee s ==>
  ?fin last. write_storage_slot cx tr (n2w slot) tvt w ee = (INL (),fin) /\
    gas_marked_path F ctx func s 0 (OK last) /\
    stmt_post ctx func cx lctx cenv cenv sa sf es0 s0 (INL ()) fin last
Proof
  strip_tac >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `!u sto. storage_dead cx tr (update_storage (n2w slot) u sto) =
           storage_dead cx tr sto` by
    metis_tac[storage_dead_update_word_region] >>
  `encode_value tvt w = SOME [(0, typed_val_to_w256 tvt w)]` by
    metis_tac[encode_value_word_typed] >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt w ee` >>
  `~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  rename1 `_ = (res, fin)` >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  drule_all assign_storage_store_path >> strip_tac >>
  `fin.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `alloca_frame cenv es0 sa s0 cenv fin
     ((if tr then tstore (n2w slot) (typed_val_to_w256 tvt w) s
       else sstore (n2w slot) (typed_val_to_w256 tvt w) s)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule alloca_frame_same_state >> qexists_tac `s` >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, LET_THM] >>
     qpat_x_assum `alloca_frame _ _ _ _ _ ee s` mp_tac >>
     simp[alloca_frame_def]) >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `~block_is_terminated sf` by
    (drule exprOpenPrimitivesTheory.emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  first_x_assum (qspec_then `ctx` assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[stmt_post_def, stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  Cases_on `tr` >>
  gvs[sstore_def, tstore_def, lookup_var_def]
QED

Theorem augassign_toplevel_rhs_exception_exec:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_toplevel_rhs_exception >> simp[] >>
  qexists_tac `v0` >> metis_tac[read_storage_slot_gas_obs]
QED

Theorem augassign_toplevel_rhs_normal_exec:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `read_storage_slot cx tr (n2w slot) tvt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v0, es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` by
        metis_tac[read_storage_slot_gas_obs] >>
      drule_all augassign_toplevel_rhs_normal >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED
Theorem augassign_storage_continuation_exec:
  bind (lift_sum br) (write_storage_slot cx tr slot tvt) ee = (res,fin) /\
  gas_marked_path F ctx func u 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_storage_slot cx tr slot tvt))
    (ee,u) [] res fin r
Proof
  Cases_on `br` >>
  simp[gas_marked_exec_def, lift_sum_def, bind_def, return_def, raise_def] >>
  strip_tac >> simp[] >> gen_tac >>
  simp[write_storage_slot_gas_obs] >> gvs[]
QED


Theorem augassign_toplevel_code_parts:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `sa` assume_tac) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `tr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_op ld [Lit slot] sa` >>
  Cases_on `emit_op ld [Lit slot] sa` >> rename1 `_ = (cur_op, s1)` >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs_op, s2)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  rename1 `_ = (res_op, s3)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_void st [Lit slot; res_op] s3` >>
  Cases_on `emit_void st [Lit slot; res_op] s3` >> simp[oneTheory.one]
QED


(* ===== The statement ===== *)

(* self.x op= e on a word storage or transient variable x, for every
   outcome, given e's expr_sim_case (so e may make internal calls unless
   nocalls).  The statement's type ty is x's declared type, and the
   typing gives x that type (toplevel_vtypes). *)
Theorem compile_augassign_toplevel_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty src id bop e es
   ts tr id_str slot tvt vtyp.
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    FLOOKUP env.toplevel_vtypes (src, id) = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\ is_word_type vtyp /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx /\
   storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[expr_sim_inv_def, stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all augassign_toplevel_code_parts >> strip_tac >> gvs[] >>
  suspend "load_prefix"
QED

Resume compile_augassign_toplevel_case[load_prefix]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  drule_all declared_storage_holds_value >> strip_tac >>
  drule_all augassign_storage_load_frame >> strip_tac >>
  rename1 `read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es)` >>
  suspend "rhs_outcome"
QED

Resume compile_augassign_toplevel_case[rhs_outcome]:
  `expr_sim ctx func cenv cx ty e (es with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule augassign_toplevel_rhs_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by simp[] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs_op`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_toplevel_rhs_exempt >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule augassign_toplevel_place_exec >> metis_tac[]
QED

Resume compile_augassign_toplevel_case[rhs_summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_toplevel_rhs_exception_exec >>
      conj_tac >- metis_tac[] >>
      qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume compile_augassign_toplevel_case[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs_op u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v, ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all augassign_storage_binop_ready >>
  disch_then (qspecl_then [`func`, `ee with gas_obs := []`, `ctx`] strip_assume_tac) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee)` by
    (`expr_res_ok (bop_result cx ty bop [ty; expr_type e]
        v0 v (ee with gas_obs := []))` suffices_by simp[] >>
     irule augassign_toplevel_binop_admissible >> metis_tac[]) >>
  suspend "binop_ready"
QED

Resume compile_augassign_toplevel_case[binop_ready]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `eval_operand (Var out) t = SOME (val_to_w256 v0)` by
    simp[typed_val_to_w256_word_value] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 v0)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_def, binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `Var out`, `rhs_op`, `res_op`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_toplevel_case[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ es` kall_tac >>
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     tvt bop v0 v = INL result` by gvs[AllCaseEqs()] >>
  `value_has_type tvt result` by simp[] >>
  `type_slot_size tvt = 1` by
    metis_tac[word_type_slot_size] >>
  `eval_operand res_op s = SOME (typed_val_to_w256 tvt result)` by
    simp[typed_val_to_w256_word_value] >>
  `alloca_frame cenv (ee with gas_obs := []) s3 s cenv (ee with gas_obs := []) s` by
    (irule alloca_frame_same >> simp[]) >>
  `?fin last. write_storage_slot cx tr (n2w slot) tvt result
      (ee with gas_obs := []) = (INL (),fin) /\
    gas_marked_path F ctx func s 0 (OK last) /\
    stmt_post ctx func cx lctx cenv cenv s3 sb (ee with gas_obs := []) s (INL ()) fin last` by
    (irule augassign_storage_store_post_path >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`res_op`, `s3`] >> simp[]) >>
  suspend "store_post"
QED

Resume compile_augassign_toplevel_case[store_post]:
  `alloca_frame cenv (ee with gas_obs := []) s2 u cenv (ee with gas_obs := []) s` by
    (mp_tac (Q.INST [`es` |-> `ee with gas_obs := []`,
                     `es'` |-> `ee with gas_obs := []`,
                     `sa` |-> `s2`, `s0` |-> `u`]
               (SPEC_ALL alloca_frame_of_mem_frame)) >>
     impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv (es with gas_obs := []) t` by
    (mp_tac (Q.INST [`es'` |-> `es with gas_obs := []`, `s` |-> `t`]
               (SPEC_ALL alloca_frame_of_mem_frame)) >>
     impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
  `stmt_post ctx func cx lctx cenv cenv s2 sb (ee with gas_obs := []) u (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qexistsl_tac [`ee with gas_obs := []`, `s`, `s3`] >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `_ (es with gas_obs := gas_explicit _ _) = (INL v, _)`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >>
     simp[]) >>
  `stmt_post ctx func cx lctx cenv cenv s1 sb (es with gas_obs := []) t (INL ()) fin last` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ s1 s2 t _ _ _ u`
       (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            stmt_post_expr_entry_frame)) >>
     simp[]) >>
  `stmt_post ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qexistsl_tac [`es with gas_obs := []`, `t`, `s1`] >> simp[] >>
     rpt strip_tac >>
     qspecl_then [`if tr then TLOAD else SLOAD`, `[Lit (n2w slot)]`, `sa`]
       mp_tac ci_mono_emit_op >>
     simp[ci_mono_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `gas_marked_path F ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `fin = fin with gas_obs := []` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     once_rewrite_tac[write_storage_slot_gas_obs] >>
     simp[] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`INL ()`, `fin`, `OK last`] >> simp[] >>
  reverse conj_tac
  >- (disj1_tac >> metis_tac[]) >>
  irule augassign_toplevel_rhs_normal_exec >>
  qexistsl_tac [`ee`, `id_str`, `slot`, `t`, `tr`, `ts`, `tvt`, `ty`,
                `u`, `v`, `v0`] >> simp[] >>
  irule augassign_storage_continuation_exec >> simp[] >>
  simp[lift_sum_def, bind_def, return_def]
QED

Resume compile_augassign_toplevel_case[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v`
  >- (gvs[] >> fs[expr_exit_def, exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`, `ee with gas_obs := []`, `r`] >>
  conj_tac
  >- (irule augassign_toplevel_rhs_normal_exec >>
      qexistsl_tac [`ee`, `id_str`, `slot`, `t`, `tr`, `ts`, `tvt`, `ty`,
                    `u`, `v`, `v0`] >> simp[] >>
      irule augassign_storage_continuation_exec >>
      simp[lift_sum_def, bind_def, raise_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Finalise compile_augassign_toplevel_case

