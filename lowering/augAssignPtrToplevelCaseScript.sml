(* Scalar storage/transient augmented-assignment pointer pipeline. *)
Theory augAssignPtrToplevelCase
Ancestors augAssignPtrStorageCommon
  vyperScopePreservation venomExecSemantics venomInst venomState
  stmtSimAssignStorage vyperStorageBackend augAssignPtrStorageStore
  vyperTypeBuiltins augAssignPtrOperator vyperTypeSystem exprReasonOperand exprOperandVar exprSimHyps
  vyperTypeValues vyperTypeStatePreservation vyperTyping exprBopSimProps exprSimProps augAssignPtrRhsFrame ptrDiscipline
  vyperState vyperInterpreter gasSummary augAssignPtrSource augAssignPtrCompiler augAssignPtrTypedContinuation
  stmtSimAugAssignStorage augAssignPtrLoadClean augAssignPtrLoad
  bodyPtrPreds bodyPtrDefs exprSimHypsDefs exprSimSource
  loweringPosts compileEnv loweringStateRelDefs emitHelperProps exprLoweringProps
  accountsRelProps vyperStorageLayoutSafety vyperLookupStorage
  stmtSimDefs codegenRel stmtSimAugAssign exprSimTopLevelProps
  augAssignPtrStorageSource exprSimUnwrap fragExec loweringSlice gasContext stmtFragPtr fragGasPathPtr gasSummaryComposePtr exprSimDefs

Theorem compile_augassign_toplevel_case_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  well_formed_type env.type_defs ty /\ cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME vtyp /\ is_word_type vtyp /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
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
  `storage_var_info cx src id = SOME (tr,slot,tvt)` by
    simp[storage_var_info_def] >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >>
     irule declared_storage_region_ordinary >> simp[]) >>
  drule_all declared_storage_holds_value_ptr >> strip_tac >>
  `type_slot_size tvt = 1` by metis_tac[word_type_slot_size] >>
  `cs_extends sa s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `?out. cur_op = Var out` by metis_tac[emitted_insts_emit_op_local] >> gvs[] >>
  `0 < type_slot_size tvt` by simp[] >>
  drule_all augassign_storage_load_clean_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "rhs_entry"
QED

Resume compile_augassign_toplevel_case_ptr[rhs_entry]:
  `expr_body_pre cenv cx env e (es with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e (es with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok _ _`
      (mp_tac o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then (irule o cj 1 o CONJUNCT1) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (rw[gas_admissible_def] >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
       fs[expr_body_pre_def] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_res_ok) >> simp[]) >>
  `s1.cs_next_var = sa.cs_next_var + 1` by
    metis_tac[emitted_insts_emit_op_local] >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s1 x)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ret_pc_ok_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs_op`, `t`, `H`, `tm`] mp_tac) >>
  (impl_tac >- simp[stmtFragPtrTheory.ghost_inv_gas_obs]) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "rhs_summary" >>
  drule_all augassign_toplevel_place_exec_ptr >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all augassign_toplevel_rhs_exempt_ptr >> disch_tac >>
  simp[gas_outcome_ptr_def] >> metis_tac[]
QED

Resume compile_augassign_toplevel_case_ptr[rhs_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
  gvs[] >>
  drule_all augassign_toplevel_rhs_exception_exec_ptr >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume compile_augassign_toplevel_case_ptr[rhs_normal]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v',es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!gs. eval_target_place cx (TopLevelNameTarget (src,id))
          (es with gas_obs := gs) =
          (INL (StoragePlace tr (n2w slot) tvt),es with gas_obs := gs) /\
        read_place cx (StoragePlace tr (n2w slot) tvt)
          (es with gas_obs := gs) = (INL v,es with gas_obs := gs) /\
        place_type_value cx (StoragePlace tr (n2w slot) tvt)
          (es with gas_obs := gs) = (INL tvt,es with gas_obs := gs)` by
    (gen_tac >> drule_all eval_target_place_toplevel >>
     disch_then (qspec_then `es with gas_obs := gs` mp_tac) >>
     simp[read_place_def] >>
     metis_tac[read_storage_slot_gas_obs_ptr]) >>
  drule_all augassign_pure_prefix_binop_admissible >> disch_tac >>
  suspend "typed_operands"
QED

Resume compile_augassign_toplevel_case_ptr[typed_operands]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `well_formed_type_value tvt` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tvt v` by metis_tac[read_storage_slot_success_type] >>
  `word_value v` by metis_tac[word_value_type_typed] >>
  `eval_operand (Var out) t = SOME (val_to_w256 v)` by
    simp[typed_val_to_w256_word_value] >>
  `eval_operand rhs_op t' = SOME (val_to_w256 v')` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[word_value_type_word]) >>
  `eval_operand (Var out) t' = SOME (val_to_w256 v)` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`s1`, `t`] >>
     fs[expr_post_def]) >>
  `op_prov G (Var out) = NONE /\ op_taint tn (Var out) = {}` by
    (drule_all ghost_kept_old_operand >> fs[op_prov_def]) >>
  `op_prov G rhs_op = NONE /\ op_taint tn rhs_op = {}` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, word_value_type_word]) >>
  suspend "compiler_entry"
QED

Resume compile_augassign_toplevel_case_ptr[compiler_entry]:
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    fs[expr_sim_inv_def] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!l. rhs_op <> Label l` by
    (drule_all lower_compile_expr_not_label >> simp[]) >>
  drule_all typed_binop_scalar_member_ptr >> strip_tac >>
  `!l. Var out <> Label l /\ rhs_op <> Label l` by simp[] >>
  drule_all compile_binop_clean_certificate_ptr >> strip_tac >>
  `straight_fresh (compile_binop bop (Var out) rhs_op ty NONE
      (if bop = Exp then expr_int_literal e else NONE))` by
    (irule compile_binop_straight_fresh_ptr >> simp[]) >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t'` by
    fs[expr_post_def] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal]) >>
  `(!z. Var out = Var z ==> not_fresh_at s2 z) /\
   (!z. rhs_op = Var z ==> not_fresh_at s2 z)` by
    (simp[] >> metis_tac[compile_lower_value_var]) >>
  `(!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s1` >> simp[]) >>
  suspend "literal_premises"
QED

Resume compile_augassign_toplevel_case_ptr[literal_premises]:
  `?tv er. eval_expr cx e
       (es with gas_obs := gas_explicit marks t.vs_gas_readings) = (INL tv,er) /\
     read_result cx tv er = (INL v',es_end with gas_obs := [])` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. v' = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  `!n. expr_int_literal e = SOME n ==> v' = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = Exp ==>
     (IS_SOME (NONE:int option) \/
       ?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\ 0 <= n) /\
     (!n. (NONE:int option) = SOME n ==> v = IntV n) /\
     (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==>
           v' = IntV n))` by
    (strip_tac >> gvs[] >>
     fs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `!z. not_fresh_at s1 z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  suspend "operator_entry"
QED

Resume compile_augassign_toplevel_case_ptr[operator_entry]:
  `(bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
     (!n. expr_int_literal e = SOME n ==> v' = IntV n))` by
    (strip_tac >> gvs[] >>
     fs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  drule augassign_clean_operator_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)
  >- suspend "operator_normal" >>
  suspend "operator_abort"
QED

Resume compile_augassign_toplevel_case_ptr[operator_normal]:
  rename1 `bop_result cx ty bop [ty;expr_type e] v v' es_end = INL result` >>
  `bop_result cx ty bop [ty;expr_type e] v v' es_end =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v v' of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     tvt bop v v' = INL result` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  `value_has_type tvt result` by
    (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)
       well_typed_binop_success_type >>
     disch_then (fn th =>
       qpat_assum `well_typed_binop ty bop ty (expr_type e)`
         (mp_then (Pat `well_typed_binop _ _ _ _`) mp_tac th)) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `!w st. storage_dead cx tr (update_storage (n2w slot) w st) =
          storage_dead cx tr st` by
    (rpt gen_tac >> irule storage_dead_update_word_region >>
     qexistsl [`src`, `id`, `[]`, `tvt`] >> simp[]) >>
  `encode_value tvt result = SOME [(0,typed_val_to_w256 tvt result)]` by
    (irule encode_value_word_typed >> simp[] >>
     qexistsl [`ty`, `get_tenv cx`] >> simp[]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `?fin. write_storage_slot cx tr (n2w slot) tvt result
      (es_end with gas_obs := []) = (INL (),fin)` by
    simp[write_storage_slot_eq] >>
  suspend "store_entry"
QED

Resume compile_augassign_toplevel_case_ptr[store_entry]:
  qmatch_asmsub_abbrev_tac
    `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) u` >>
  `eval_operand res_op u = SOME (typed_val_to_w256 tvt result)` by
    simp[Abbr `u`, typed_val_to_w256_word_value] >>
  `stmt_state_rel ctx func cenv cx fin
     (if tr then tstore (n2w slot) (typed_val_to_w256 tvt result) u
      else sstore (n2w slot) (typed_val_to_w256 tvt result) u)` by
    (drule_at (Pat `write_storage_slot _ _ _ _ _ _ = _`)
       (cj 2 stmt_state_rel_write_storage_word) >>
     disch_then drule_all >> simp[]) >>
  `~u.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `run_inst_seq (emitted_insts s3 sb) u =
     OK (if tr then tstore (n2w slot) (typed_val_to_w256 tvt result) u
         else sstore (n2w slot) (typed_val_to_w256 tvt result) u)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, mk_inst_def] >>
     once_rewrite_tac[step_inst_base_def] >>
     Cases_on `tr` >> simp[exec_write2_def, eval_operands_def, eval_operand_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = s3.cs_current_bb /\
   u.vs_inst_idx = LENGTH s3.cs_current_insts` by simp[Abbr `u`] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts s3 sb) u = OK last` >>
  `last.vs_allocas = u.vs_allocas /\ last.vs_fmp = u.vs_fmp /\
   last.vs_requests = u.vs_requests` by
    (Cases_on `tr` >> simp[Abbr `last`, sstore_def, tstore_def]) >>
  `op_taint tm' (Lit (n2w slot)) = {} /\
   eval_operand (Lit (n2w slot)) u = SOME (n2w slot)` by
    simp[op_taint_def, eval_operand_def] >>
  drule_all emit_storage_store_path_ptr >>
  disch_then (qspecl_then [`PG`, `H'`, `cx_dead cx`] assume_tac) >>
  `fin.scopes = (es_end with gas_obs := []).scopes` by
    metis_tac[write_storage_slot_scopes] >>
  `u.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  suspend "store_ghost"
QED

Resume compile_augassign_toplevel_case_ptr[store_ghost]:
  `!k b. storage_dead cx tr
     (update_storage (n2w slot) (typed_val_to_w256 tvt result)
       (if tr then contract_transient u else contract_storage u)) k b =
     storage_dead cx tr
       (if tr then contract_transient u else contract_storage u) k b` by simp[] >>
  drule_at (Pat `u.vs_call_ctx.cc_address = _`)
    ghost_inv_storage_word_store >>
  disch_then drule_all >>
  disch_then (qspec_then `LENGTH sb.cs_current_insts` assume_tac) >>
  qabbrev_tac `store_tn =
    if tr then tm' with t_trans := key_update tm'.t_trans (n2w slot) {}
    else tm' with t_stor := key_update tm'.t_stor (n2w slot) {}` >>
  `ghost_inv d cenv cx fin H' store_tn
      (last with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[Abbr `last`, Abbr `store_tn`] >>
  `ghost_kept cenv (es with gas_obs := []) s1 H tm t H' store_tn` by
    (simp[Abbr `store_tn`] >>
     irule ghost_kept_storage_word_store >> simp[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t' 0 H' store_tn
      (OK (last with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  suspend "normal_compose"
QED

Resume compile_augassign_toplevel_case_ptr[normal_compose]:
  `bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v v')) (write_storage_slot cx tr (n2w slot) tvt)
      (es_end with gas_obs := []) = (INL (),fin)` by
    simp[lift_sum_def, bind_def, return_def] >>
  drule_all augassign_storage_continuation_exec_ptr >> strip_tac >>
  drule_all augassign_toplevel_rhs_normal_exec_ptr >>
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x /\ not_fresh_at s2 x` by
    (gen_tac >> disch_tac >> conj_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     fs[cs_extends_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x (last with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w` by
    (rpt strip_tac >>
     simp[Abbr `last`, sstore_def, tstore_def] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by simp[] >>
     `lookup_var x t = SOME w` by simp[] >>
     `lookup_var x t' = SOME w` by
       (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
          (mp_tac o cj 5 o REWRITE_RULE [expr_post_def]) >> simp[]) >>
     `lookup_var x u = SOME w` by
       (qpat_x_assum `!z w. not_fresh_at s2 z /\ _ ==> _` irule >> simp[]) >>
     Cases_on `tr` >> fs[lookup_var_def]) >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP H' x = FLOOKUP G0 x /\
       op_taint store_tn (Var x) = op_taint tn0 (Var x)` by
    metis_tac[ghost_kept_old_operand] >>
  suspend "normal_summary"
QED

Resume compile_augassign_toplevel_case_ptr[normal_summary]:
  `~block_is_terminated sb /\ sb.cs_current_bb = s3.cs_current_bb` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
     disch_then (fn th => rewrite_tac[GSYM th]) >>
     Cases_on `tr` >> Cases_on `s3.cs_current_insts` >>
     simp[block_is_terminated_def, rich_listTheory.LAST_APPEND, listTheory.LAST_CONS_cond, mk_inst_def,
          is_terminator_def]) >>
  `stmt_state_rel ctx func cenv cx fin
      (last with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    metis_tac[stmt_state_rel_inst_idx] >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj1_tac >>
  simp[] >>
  simp[stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl] >>
  conj_tac >- (Cases_on `tr` >> simp[Abbr `last`, sstore_def, tstore_def]) >>
  conj_tac >- (Cases_on `tr` >> simp[Abbr `last`, sstore_def, tstore_def]) >>
  fs[stmtFragPtrTheory.ghost_inv_gas_obs]
QED

Resume compile_augassign_toplevel_case_ptr[operator_abort]:
  `bop_result cx ty bop [ty; expr_type e] v v' es_end =
    (case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v v' of INL z => INL z | INR err => INR (Error err))` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v v' = INR (RuntimeError msg)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  `bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v v')) (write_storage_slot cx tr (n2w slot) tvt)
      (es_end with gas_obs := []) =
      (INR (Error (RuntimeError msg)),es_end with gas_obs := [])` by
    simp[lift_sum_def, bind_def, raise_def] >>
  drule_all augassign_storage_continuation_exec_ptr >> strip_tac >>
  drule_all augassign_toplevel_rhs_normal_exec_ptr >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       fragExecTheory.exit_result_def]
QED

Finalise compile_augassign_toplevel_case_ptr
