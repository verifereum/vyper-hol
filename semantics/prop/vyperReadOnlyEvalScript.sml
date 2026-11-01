(* Mutual evaluator frame for checked read-only syntax. *)
Theory vyperReadOnlyEval
Ancestors
  vyperReadOnlyBranches vyperReadOnlyCalls vyperReadOnlySyntax vyperReadOnlyTargets
  vyperMachineFrame vyperTypeContract vyperInterpreter vyperCallOutcomeFrame vyperState
  vyperAST sorting
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

Theorem evaluate_read_only:
  (!cx s. !mods. read_only_context mods cx /\ stmt_mutability_ok mods View s ==>
     state_rel_frame machine_frame (eval_stmt cx s)) /\
  (!cx ss. !mods. read_only_context mods cx /\ stmts_mutability_ok mods View ss ==>
     state_rel_frame machine_frame (eval_stmts cx ss)) /\
  (!cx it. !mods. read_only_context mods cx /\ iterator_mutability_ok mods View it ==>
     state_rel_frame machine_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. !mods. read_only_context mods cx /\ stmts_mutability_ok mods View body ==>
     state_rel_frame machine_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. !mods. read_only_context mods cx /\ expr_mutability_ok mods View e ==>
     state_rel_frame machine_frame (eval_expr cx e)) /\
  (!cx es. !mods. read_only_context mods cx /\ EVERY (expr_mutability_ok mods View) es ==>
     state_rel_frame machine_frame (eval_exprs cx es)) /\
  (!cx bt. !mods. read_only_context mods cx /\ target_mutability_ok mods View bt ==>
     state_rel_frame machine_frame (eval_base_place cx bt)) /\
  (!cx bt. !mods. read_only_context mods cx /\ target_mutability_ok mods View bt ==>
     state_rel_frame machine_frame (eval_target_place cx bt)) /\
  (!cx g v. !mods. read_only_context mods cx /\ atarget_mutability_ok mods View g ==>
     state_rel_frame machine_frame (assign_tuple_targets cx g v)) /\
  (!cx gs vs. !mods. read_only_context mods cx /\ EVERY (atarget_mutability_ok mods View) gs ==>
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs)) /\
  (!cx es. !mods. read_only_context mods cx /\ EVERY (expr_mutability_ok mods View) es ==>
     state_rel_frame machine_frame (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "return_some"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "raise_reason"
  >- suspend "raise_custom"
  >- suspend "assert_bare"
  >- suspend "assert_unreachable"
  >- suspend "assert_reason"
  >- suspend "assert_custom"
  >- suspend "log"
  >- suspend "annassign"
  >- suspend "append"
  >- suspend "assign"
  >- suspend "assign_tuple"
  >- suspend "augassign"
  >- suspend "if_stmt"
  >- suspend "for_stmt"
  >- suspend "expr_stmt"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "stmts_cons"
  >- suspend "iterator_array"
  >- suspend "iterator_range"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "for_cons"
  >- suspend "expr_name"
  >- suspend "expr_toplevel"
  >- suspend "expr_flag"
  >- suspend "expr_if"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "expr_struct"
  >- suspend "expr_subscript"
  >- suspend "expr_attribute"
  >- suspend "expr_builtin"
  >- suspend "expr_pop"
  >- suspend "expr_type_builtin"
  >- suspend "expr_send"
  >- suspend "expr_extcall"
  >- suspend "expr_intcall"
  >- suspend "expr_rawcall"
  >- suspend "expr_rawcalldata"
  >- suspend "expr_rawlog"
  >- suspend "expr_rawrevert"
  >- suspend "expr_selfdestruct"
  >- suspend "expr_create"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "exprs_cons"
  >- suspend "base_name"
  >- suspend "base_toplevel"
  >- suspend "base_attribute"
  >- suspend "base_subscript"
  >- suspend "target_place"
  >- suspend "target_base"
  >- suspend "target_tuple"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- suspend "targets_cons"
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >- simp[Once evaluate_def, machine_frame_primitives]
  >> suspend "expr_results_cons"
QED

Resume evaluate_read_only[return_some]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_read_only[log]:
  rpt strip_tac >> gvs[stmt_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only[expr_send]:
  rpt strip_tac >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only[expr_rawlog]:
  rpt strip_tac >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only[expr_selfdestruct]:
  rpt strip_tac >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only[expr_create]:
  rpt strip_tac >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only[raise_reason]:
  rpt strip_tac >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac >- suspend "raise_reason_value" >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_read_only[raise_reason_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only[assign]:
  rpt strip_tac >>
  gvs[Once stmt_mutability_ok_def, atarget_mutability_ok_def,
      write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_assign >> metis_tac[]
QED

Resume evaluate_read_only[append]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_append >> metis_tac[]
QED

Resume evaluate_read_only[augassign]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_augassign >> metis_tac[]
QED

Resume evaluate_read_only[expr_pop]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_expr_pop >> simp[] >> metis_tac[]
QED

Resume evaluate_read_only[for_cons]:
  rpt strip_tac >> irule machine_frame_for_cons >> metis_tac[]
QED

Resume evaluate_read_only[for_stmt]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_for >> conj_tac
  >- (rpt strip_tac >> Cases_on `x` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_read_only[base_name]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule machine_frame_sequence >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only[base_toplevel]:
  rpt strip_tac >> simp[Once evaluate_def, machine_frame_lookup_global]
QED

Resume evaluate_read_only[base_attribute]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_extend_place] >> metis_tac[]
QED

Resume evaluate_read_only[target_base]:
  rpt strip_tac >> gvs[Once atarget_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_assign_tuple_base >> metis_tac[]
QED

Resume evaluate_read_only[target_tuple]:
  rpt strip_tac >> gvs[Once atarget_mutability_ok_def] >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[machine_frame_primitives] >>
  rename1 `ArrayV a` >> Cases_on `a` >> simp[machine_frame_primitives] >> metis_tac[]
QED

Resume evaluate_read_only[targets_cons]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only[stmts_cons]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only[expr_name]:
  rpt strip_tac >> simp[Once evaluate_def] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives] >> gen_tac >>
  irule machine_frame_sequence >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only[expr_attribute]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "attribute_value" >> metis_tac[]
QED

Resume evaluate_read_only[attribute_value]:
  rpt strip_tac >> simp[machine_frame_select_result]
QED

Resume evaluate_read_only[expr_struct]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only[expr_rawrevert]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_sequence >> simp[machine_frame_primitives]) >>
  metis_tac[]
QED

Resume evaluate_read_only[expr_toplevel]:
  rpt strip_tac >> simp[Once evaluate_def, machine_frame_reads]
QED

Resume evaluate_read_only[expr_flag]:
  rpt strip_tac >> simp[Once evaluate_def, machine_frame_reads]
QED

Resume evaluate_read_only[assert_bare]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]) >>
  metis_tac[]
QED

Resume evaluate_read_only[assert_unreachable]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]) >>
  metis_tac[]
QED

Resume evaluate_read_only[expr_if]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >> conj_tac
      >- (irule machine_frame_switch_BoolV >> metis_tac[]) >>
      qx_gen_tac `res` >> simp[] >> Cases_on `res` >>
      simp[conditional_result_def, machine_frame_primitives] >>
      match_mp_tac machine_frame_bind >> simp[machine_frame_place_type_value] >>
      gen_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
      match_mp_tac machine_frame_bind >> simp[machine_frame_read_place]) >>
  metis_tac[]
QED

Resume evaluate_read_only[expr_stmt]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  metis_tac[]
QED

Resume evaluate_read_only[exprs_cons]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "exprs_materialise" >> metis_tac[]
QED

Resume evaluate_read_only[exprs_materialise]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only[expr_extcall]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  `EVERY (expr_mutability_ok mods View) (TAKE 1 es) /\
   EVERY (expr_mutability_ok mods View) (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   EVERY (expr_mutability_ok mods View) (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    simp[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "extcall_results" >> metis_tac[]
QED

Resume evaluate_read_only[extcall_results]:
  rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def] >> conj_tac
      >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
          simp[machine_frame_read_results] >> gen_tac >>
          simp[state_rel_frame_result] >> metis_tac[machine_frame_ext_call]) >> metis_tac[]) >>
  metis_tac[]
QED

Resume evaluate_read_only[iterator_array]:
  rpt strip_tac >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "iterator_array_value" >> metis_tac[]
QED

Resume evaluate_read_only[iterator_array_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only[annassign]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "annassign_value" >> metis_tac[]
QED

Resume evaluate_read_only[annassign_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result, machine_frame_new_variable]
QED

Resume evaluate_read_only[expr_type_builtin]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "type_builtin_value" >> metis_tac[]
QED

Resume evaluate_read_only[type_builtin_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only[base_subscript]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "base_subscript_expr" >> metis_tac[]
QED

Resume evaluate_read_only[base_subscript_expr]:
  rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
      simp[machine_frame_read_result, machine_frame_extend_place]) >> metis_tac[]
QED

Resume evaluate_read_only[raise_custom]:
  rpt strip_tac >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  irule machine_frame_stmt_custom_error >> rpt strip_tac >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY (expr_mutability_ok mods View) es` by metis_tac[PERM_EVERY] >>
  metis_tac[]
QED

Resume evaluate_read_only[if_stmt]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "if_scope" >> metis_tac[]
QED

Resume evaluate_read_only[if_scope]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  irule state_rel_frame_finally >> simp[machine_frame_def, machine_frame_primitives] >>
  irule machine_frame_switch_BoolV >> metis_tac[]
QED

Resume evaluate_read_only[iterator_range]:
  rpt strip_tac >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "range_first_value" >> metis_tac[]
QED

Resume evaluate_read_only[range_first_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "range_second_value" >> metis_tac[]
QED

Resume evaluate_read_only[range_second_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only[expr_rawcall]:
  rpt strip_tac >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "raw_operands" >> metis_tac[]
QED

Resume evaluate_read_only[raw_operands]:
  rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]
QED

Resume evaluate_read_only[expr_rawcalldata]:
  rpt strip_tac >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "rawcalldata_operands" >> metis_tac[]
QED

Resume evaluate_read_only[rawcalldata_operands]:
  rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]
QED

Resume evaluate_read_only[assert_reason]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "assert_reason_switch" >> metis_tac[]
QED

Resume evaluate_read_only[assert_reason_switch]:
  rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "assert_reason_value" >> metis_tac[]
QED

Resume evaluate_read_only[assert_reason_value]:
  rpt strip_tac >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives] >> rpt strip_tac)
QED

Resume evaluate_read_only[assert_custom]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "assert_custom_switch" >> metis_tac[]
QED

Resume evaluate_read_only[assert_custom_switch]:
  rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
  irule (SRULE [Once evaluate_def] machine_frame_stmt_custom_error) >>
  rpt strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
  `EVERY (expr_mutability_ok mods View) es` by metis_tac[PERM_EVERY] >>
  metis_tac[]
QED

Resume evaluate_read_only[expr_subscript]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "subscript_second_expr" >> metis_tac[]
QED
Resume evaluate_read_only[subscript_second_expr]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "subscript_tail" >> metis_tac[]
QED
Resume evaluate_read_only[subscript_tail]:
  rpt strip_tac >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_select_result]
QED

Resume evaluate_read_only[expr_builtin]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  Cases_on `bt = Len` >> simp[]
  >- suspend "builtin_len" >>
  Cases_on `bt = Env MsgGas` >> simp[]
  >- simp[machine_frame_next_gas_reading]
  >> suspend "builtin_other"
QED

Resume evaluate_read_only[builtin_len]:
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_reads, machine_frame_primitives]) >>
  Cases_on `es` >> gvs[type_check_def, assert_def, raise_def, vyperContextTheory.builtin_args_length_ok_def, SF ETA_ss] >> metis_tac[]
QED

Resume evaluate_read_only[builtin_other]:
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_reads, machine_frame_primitives]) >>
  gvs[SF ETA_ss] >> metis_tac[]
QED

Resume evaluate_read_only[expr_intcall]:
  rpt strip_tac >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  ntac 3 (irule state_rel_frame_bind_guarded >>
          simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  qmatch_asmsub_rename_tac `lift_option_type (lookup_callable_function _ _ _) _ _ = (INL tup,_)` >>
  PairCases_on `tup` >> simp[] >>
  rename1 `lookup_callable_function cx.in_deploy fn ts` >>
  rename1 `(INL (mut,nr,args,dflts,ret,body),_)` >>
  `get_module_code cx src_id_opt = SOME ts /\
   lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body)` by
    (Cases_on `get_module_code cx src_id_opt` >>
     Cases_on `lookup_callable_function cx.in_deploy fn ts` >>
     gvs[lift_option_type_def, lift_option_def, return_def, raise_def]) >>
  `~cx.in_deploy /\ ALOOKUP mods src_id_opt = SOME ts` by
    (gvs[read_only_context_def, vyperContextTheory.get_module_code_def]) >>
  SUBGOAL_THEN ``mut = View \/ mut = Pure`` assume_tac
  >- (ntac 3 (qpat_x_assum `!s. _` kall_tac) >>
      gvs[read_only_context_def, vyperContextTheory.get_module_code_def] >>
      Cases_on `mut` >> gvs[call_mutability_ok_def]) >>
  `EVERY (expr_mutability_ok mods View) dflts /\ stmts_mutability_ok mods View body` by
    (ntac 3 (qpat_x_assum `!s. _` kall_tac) >> metis_tac[read_only_context_callee]) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "intcall_after_args" >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3. _ ==> !mods. _ ==> state_rel_frame _ (eval_expr_results cx es)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  simp[arithmeticTheory.ADD_COMM] >> disch_then drule >>
  disch_then (qspec_then `mods` mp_tac) >> simp[]
QED

Resume evaluate_read_only[intcall_after_args]:
  rpt strip_tac >> BETA_TAC >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "intcall_after_defaults" >>
  irule state_rel_frame_finally >> simp[machine_frame_def, machine_frame_primitives] >>
  simp[ignore_bind_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3 s6 vs t4 s7 prev t5 s8 t6. _ ==> !mods. _ ==> state_rel_frame _ (eval_exprs _ _)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >> simp[arithmeticTheory.ADD_COMM] >>
  disch_then drule >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then `mods` mp_tac) >>
  simp[rich_listTheory.EVERY_DROP] >>
  qpat_x_assum `read_only_context mods cx` mp_tac >> simp[read_only_context_def]
QED

Resume evaluate_read_only[intcall_after_defaults]:
  rpt strip_tac >> BETA_TAC >>
  irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_results] >> rpt strip_tac >>
  ntac 2 (irule state_rel_frame_bind_guarded >>
          simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "intcall_after_lock" >>
  qpat_x_assum `mut = View \/ mut = Pure` strip_assume_tac >>
  simp[machine_frame_internal_lock]
QED

Resume evaluate_read_only[intcall_after_lock]:
  rpt strip_tac >> BETA_TAC >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_push_function] >>
  rpt strip_tac >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3 s6 results t4 s7 prev t5 s8 dv t6 sr vs tr s9 env t7 s10 rtv t8 s11 t9 s12 cx1 t10. _ ==> !mods. _ ==> state_rel_frame _ (eval_stmts _ _)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >> simp[arithmeticTheory.ADD_COMM] >>
  ntac 3 (disch_then drule) >> simp[ignore_bind_def] >>
  ntac 2 (disch_then drule) >> simp[] >>
  ntac 4 (disch_then drule) >>
  disch_then (qspec_then `mods` mp_tac) >>
  impl_tac
  >- (conj_tac >- (
        qpat_x_assum `push_function _ _ cx _ = _` mp_tac >>
        simp[push_function_def, return_def] >> strip_tac >> gvs[] >>
        qpat_x_assum `read_only_context mods cx` mp_tac >> simp[read_only_context_def]) >>
      simp[]) >>
  strip_tac >> ntac 3 (qpat_x_assum `!s. _` kall_tac) >>
  `~(nr /\ mut <> View /\ mut <> Pure)` by metis_tac[] >>
  simp[ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_primitives]) >>
  irule state_rel_frame_finally >> simp[machine_frame_def] >> conj_tac
  >- (irule state_rel_frame_try >> simp[machine_frame_def, machine_frame_handlers] >>
      irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]) >>
  irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_pop_function, machine_frame_primitives]
QED

Resume evaluate_read_only[assign_tuple]:
  rpt strip_tac >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_tuple_assign >> metis_tac[]
QED

Resume evaluate_read_only[target_place]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_get_place] >> metis_tac[]
QED

Resume evaluate_read_only[expr_results_cons]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac machine_frame_bind >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise evaluate_read_only

Theorem machine_frame_eval_stmts:
  read_only_context mods cx /\ stmts_mutability_ok mods View body ==>
  state_rel_frame machine_frame (eval_stmts cx body)
Proof
  metis_tac[ evaluate_read_only |> cj 2 ]
QED

