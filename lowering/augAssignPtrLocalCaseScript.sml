(* Local augmented-assignment counted pointer pipeline. *)
Theory augAssignPtrLocalCase
Ancestors
  augAssignPtrLocalLayout augAssignPtrLocalSource augAssignPtrLoadClean
  augAssignPtrLoad augAssignPtrStore stmtFragPtr venomState venomExecSemantics
  emitHelper list rich_list stmtSimProps
  augAssignPtrLocalCertificates stmtSimAssignStore augAssignPtrOperator exprReasonOperand exprOperandVar
  fragGasPath gasSummary gasCount gasContext vyperInterpreter vyperState vyperTypeSystem
  augAssignPtrTypedContinuation augAssignPtrStorePost augAssignPtrSource
  bodyPtrPreds bodyPtrDefs stmtSimAugAssign exprSimHyps exprSimProps
  exprSimHypsDefs exprSimSource vyperTypeStatePreservation exprLoweringProps
  loweringPosts compileEnv loweringStateRelDefs gasSummaryComposePtr fragGasPathPtr
  exprBopSimProps vyperAST augAssignPtrRhsFrame ptrDiscipline

Theorem compile_augassign_local_case_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  `word_value entry.value` by metis_tac[word_value_type_typed] >>
  drule_all augassign_local_layout_ptr >> strip_tac >> gvs[] >>
  `?out. cur_op = Var out` by metis_tac[emitted_insts_emit_op_local] >> gvs[] >>
  drule_all augassign_local_load_clean_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `expr_body_pre cenv cx env e (es with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e (es with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok _ _`
       (mp_tac o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then (irule o cj 1 o CONJUNCT1) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (simp[] >> irule augassign_rhs_admissible_ptr >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
    fs[expr_post_def] >>
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
  (impl_tac >- simp[]) >>
  disch_tac >> suspend "rhs_continuation"
QED

Resume compile_augassign_local_case_ptr[rhs_continuation]:
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "rhs_summary" >>
  suspend "rhs_exempt"
QED

Resume compile_augassign_local_case_ptr[rhs_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  suspend "rhs_exception"
QED

Resume compile_augassign_local_case_ptr[rhs_normal]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `!gs. eval_target_place cx (NameTarget id) (es with gas_obs := gs) =
          (INL (MemoryPlace id []),es with gas_obs := gs) /\
        read_place cx (MemoryPlace id []) (es with gas_obs := gs) =
          (INL entry.value,es with gas_obs := gs) /\
        place_type_value cx (MemoryPlace id []) (es with gas_obs := gs) =
          (INL entry.type,es with gas_obs := gs)` by
    (gen_tac >> irule eval_target_place_local >> simp[]) >>
  drule_all augassign_pure_prefix_binop_admissible >> disch_tac >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `eval_operand (Var out) t = SOME (val_to_w256 entry.value) /\
   eval_operand rhs_op t' = SOME (val_to_w256 v)` by
    (conj_tac >> irule expr_val_rel_word >>
     fs[expr_post_def] >> goal_assum (drule_at Any) >>
     simp[expr_type_def, word_value_type_word]) >>
  `eval_operand (Var out) t' = SOME (val_to_w256 entry.value)` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`s1`, `t`] >>
     fs[expr_post_def]) >>
  `op_prov G (Var out) = NONE /\ op_taint tn (Var out) = {}` by
    (drule_all ghost_kept_old_operand >>
     fs[op_prov_def]) >>
  `op_prov G rhs_op = NONE /\ op_taint tn rhs_op = {}` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, word_value_type_word]) >>
  suspend "operator_inputs"
QED

Resume compile_augassign_local_case_ptr[operator_inputs]:
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    fs[expr_sim_inv_def] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!l. Var out <> Label l /\ rhs_op <> Label l` by
    (simp[] >> drule_all lower_compile_expr_not_label >> simp[]) >>
  `well_formed_type env.type_defs ty` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    (conj_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >>
         fs[cs_extends_def]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `s1` >>
     fs[cs_extends_def]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t'` by
    fs[expr_post_def] >>
  `~t'.vs_halted` by
    metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal] >>
  `(!z. Var out = Var z ==> not_fresh_at s2 z) /\
   (!z. rhs_op = Var z ==> not_fresh_at s2 z)` by
    (simp[] >> metis_tac[compile_lower_value_var]) >>
  `(!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s1` >> fs[cs_extends_def]) >>
  suspend "literal_inputs"
QED

Resume compile_augassign_local_case_ptr[literal_inputs]:
  `?tv er. eval_expr cx e
       (es with gas_obs := gas_explicit marks t.vs_gas_readings) = (INL tv,er) /\
     read_result cx tv er = (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  `(bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
     (!n. expr_int_literal e = SOME n ==> v = IntV n))` by
    (strip_tac >> gvs[] >>
     `!n. expr_int_literal e = SOME n ==> v = IntV n` by
       metis_tac[eval_expr_int_literal_agrees] >>
     fs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `!z. not_fresh_at s1 z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule augassign_clean_operator_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)
  >- suspend "operator_normal" >>
  suspend "operator_abort"
QED

Resume compile_augassign_local_case_ptr[rhs_exception]:
  `?ex. res = INR ex` by
    (Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >> gvs[] >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INR ex) es_end G tn r` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_rhs_exception_exec_ptr >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume compile_augassign_local_case_ptr[rhs_exempt]:
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (eval_target_place cx (NameTarget id))
     (es,s0,G0,tn0) [] (INL (MemoryPlace id [])) es H tm (OK t)` by
    (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
     gen_tac >> irule (cj 1 eval_target_place_local) >> simp[]) >>
  drule_all augassign_rhs_exempt_ptr >> disch_tac >>
  simp[gas_outcome_ptr_def] >> metis_tac[]
QED

Resume compile_augassign_local_case_ptr[operator_abort]:
  `bop_result cx ty bop [ty;expr_type e] entry.value v es_end =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v = INR (RuntimeError msg)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INL v) es_end G tn (OK t')` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_error_continuation_exec_ptr >>
  disch_then (qspecl_then [`id`, `es_end with gas_obs := []`, `cx`] assume_tac) >>
  drule_all augassign_rhs_normal_exec_ptr >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       fragExecTheory.exit_result_def]
QED

Resume compile_augassign_local_case_ptr[operator_normal]:
  rename1 `bop_result cx ty bop [ty;expr_type e] entry.value v es_end = INL result` >>
  `bop_result cx ty bop [ty;expr_type e] entry.value v es_end =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v = INL result` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  Cases_on `write_place cx (MemoryPlace id []) result (es_end with gas_obs := [])` >>
  rename1 `write_place cx (MemoryPlace id []) result _ = (wr,fin)` >>
  `!m. wr <> INR (Error (TypeError m))` by
    (irule augassign_write_admissible_ptr >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all write_place_local >> strip_tac >> gvs[] >>
  suspend "store_entry"
QED

Resume compile_augassign_local_case_ptr[store_entry]:
  `lookup_scopes id es_end.scopes = SOME entry'` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) ty = SOME entry'.type /\
   value_has_type entry'.type entry'.value` by
    (drule_all expr_sim_inv_local >> strip_tac >> gvs[] >>
     metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type]) >>
  `word_value entry'.value` by metis_tac[word_value_type_typed] >>
  `stmt_state_rel ctx func cenv cx es_end t''` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  `ghost_inv d cenv cx es_end H' tm' t''` by fs[ghost_inv_gas_obs] >>
  drule_all ghost_inv_word_local_inputs >> strip_tac >>
  `local_ptrs_rel func cenv es_end.scopes t''` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `type_memory_size entry'.type = 32` by
    metis_tac[exprSimSourceTheory.word_value_type_memory_size] >>
  `32 <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  suspend "store_path"
QED

Resume compile_augassign_local_case_ptr[store_path]:
  qmatch_asmsub_abbrev_tac `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t' 0 H' tm' (OK u)` >>
  `~u.vs_halted /\ u.vs_current_bb = s3.cs_current_bb /\
   u.vs_inst_idx = LENGTH s3.cs_current_insts /\
   ptr_covers H' tm' p u 32 /\ lookup_var p u = SOME a /\
   eval_operand res_op u = SOME (val_to_w256 result)` by
    gvs[Abbr `u`, ptr_covers_def, op_taint_def, lookup_var_def] >>
  drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "store_post"
QED

Resume compile_augassign_local_case_ptr[store_post]:
  qmatch_asmsub_abbrev_tac `write_place cx (MemoryPlace id []) result _ = (INL (),fin)` >>
  `ghost_inv d cenv cx fin H' tnf sf` by
    (`local_ptrs_rel func cenv es_end.scopes u /\
      ghost_inv d cenv cx es_end H' tm' u` by
       (conj_tac
        >- (fs[stmt_state_rel_def, state_rel_def]) >>
        simp[Abbr `u`, ghost_inv_jump_to]) >>
     drule_all ghost_inv_write_local_word >>
     disch_then (qspecl_then [`LENGTH sb.cs_current_insts`, `s3.cs_next_id`] assume_tac) >>
     `fin = (es_end with scopes := pre ++
       (env' |+ (id,entry' with <|value := result; popped := []|>))::rest)
       with gas_obs := []` by
       simp[Abbr `fin`, vyperStateTheory.evaluation_state_component_equality] >>
     qpat_x_assum `fin = _` SUBST1_TAC >>
     qpat_x_assum `tnf = _` SUBST1_TAC >>
     qpat_x_assum `sf = _` SUBST1_TAC >>
     pure_rewrite_tac[ghost_inv_gas_obs] >> first_assum ACCEPT_TAC) >>
  suspend "ordinary_store_post"
QED

Resume compile_augassign_local_case_ptr[ordinary_store_post]:
  `val_wf entry'.type result` by
    metis_tac[loweringSliceTheory.word_value_wf] >>
  `val_in_memory entry'.type result (w2n a)
      (mstore (w2n a) (val_to_w256 result) u).vs_memory` by
    metis_tac[loweringSliceTheory.word_value_in_memory] >>
  suspend "ordinary_store_relation"
QED

Resume compile_augassign_local_case_ptr[ordinary_store_relation]:
  `stmt_state_rel ctx func cenv cx fin sf` by
    (`stmt_state_rel ctx func cenv cx
        (es_end with scopes := pre ++
          (env' |+ (id,entry' with <|value := result; popped := []|>))::rest)
        (mstore (w2n a) (val_to_w256 result) u)` by
       (irule stmt_state_rel_write_local_word >>
        goal_assum (drule_at Any) >> simp[Abbr `u`] >>
        goal_assum (drule_at Any) >> simp[]) >>
     `fin = (es_end with scopes := pre ++
       (env' |+ (id,entry' with <|value := result; popped := []|>))::rest)
       with gas_obs := []` by
       simp[Abbr `fin`, vyperStateTheory.evaluation_state_component_equality] >>
     `sf = (mstore (w2n a) (val_to_w256 result) u) with
       <|vs_gas_readings := (mstore (w2n a) (val_to_w256 result) u).vs_gas_readings;
         vs_inst_idx := LENGTH sb.cs_current_insts|>` by
       (qpat_x_assum `sf = _` (fn th => pure_rewrite_tac[th]) >>
        simp[NoAsms, venom_state_component_equality]) >>
     qpat_x_assum `fin = _` SUBST1_TAC >>
     qpat_x_assum `sf = _ with <|vs_gas_readings := _; vs_inst_idx := _|>` SUBST1_TAC >>
     irule msg_gas_state_frame >> asm_rewrite_tac[]) >>
  suspend "compose_store"
QED

Resume compile_augassign_local_case_ptr[compose_store]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t' 0 H' tnf (OK sf)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn t' _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule_all >> simp[]) >>
  drule_all augassign_store_continuation_exec_ptr >>
  disch_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INL v) es_end G tn (OK t')` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_rhs_normal_exec_ptr >> disch_tac >>
  suspend "local_frames"
QED

Resume compile_augassign_local_case_ptr[local_frames]:
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x /\ not_fresh_at s2 x` by
    (gen_tac >> disch_tac >> conj_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x sf = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `lookup_var x t' = SOME w` by metis_tac[expr_post_def] >>
     `lookup_var x u = SOME w` by metis_tac[] >>
     metis_tac[]) >>
  `ghost_kept cenv (es with gas_obs := []) s1 H tm t H' tnf` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     irule ghost_kept_mstore >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP H' x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_x_assum `ghost_kept cenv es sa _ _ _ _ _` mp_tac >>
     qpat_x_assum `ghost_kept _ _ s1 _ _ _ H' tnf` mp_tac >>
     simp[ghost_kept_def] >> metis_tac[]) >>
  suspend "normal_outcome"
QED

Resume compile_augassign_local_case_ptr[normal_outcome]:
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
     Cases_on `s3.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  qpat_x_assum `sf = _` kall_tac >>
  qpat_x_assum `tnf = _` kall_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >> goal_assum (drule_at Any) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_gas_obs]
QED

Finalise compile_augassign_local_case_ptr
