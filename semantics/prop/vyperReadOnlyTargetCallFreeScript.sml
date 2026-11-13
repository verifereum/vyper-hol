(* Read-only evaluation without a checked global context: internal calls
   are excluded syntactically. *)
Theory vyperReadOnlyTargetCallFree
Ancestors
  vyperReadOnlyBranches vyperReadOnlyCalls vyperReadOnlySyntax vyperReadOnlyTargets
  vyperMachineFrame vyperTypeContract vyperInterpreter vyperCallOutcomeFrame vyperState
  vyperAST sorting vyperTypeCallGraph exprOracleStorageInterfaces
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

val strip_calls = rpt strip_tac >>
  gvs[int_calls_expr_def, int_calls_stmt_def, int_calls_iterator_def,
      int_calls_atarget_def, int_calls_assert_reason_def,
      int_calls_raise_reason_def, int_calls_exprs_empty_every,
      int_calls_named_exprs_empty_every];

Theorem target_call_free_evaluate[local]:
  (!cx s. !mods. stmt_mutability_ok mods View s /\ int_calls_stmt s = [] ==>
     state_rel_frame machine_frame (eval_stmt cx s)) /\
  (!cx ss. !mods. stmts_mutability_ok mods View ss /\ int_calls_stmts ss = [] ==>
     state_rel_frame machine_frame (eval_stmts cx ss)) /\
  (!cx it. !mods. iterator_mutability_ok mods View it /\ int_calls_iterator it = [] ==>
     state_rel_frame machine_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. !mods. stmts_mutability_ok mods View body /\ int_calls_stmts body = [] ==>
     state_rel_frame machine_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. !mods. expr_mutability_ok mods View e /\ int_calls_expr e = [] ==>
     state_rel_frame machine_frame (eval_expr cx e)) /\
  (!cx es. !mods. EVERY (expr_mutability_ok mods View) es /\ int_calls_exprs es = [] ==>
     state_rel_frame machine_frame (eval_exprs cx es)) /\
  (!cx bt. !mods. target_mutability_ok mods View bt /\ int_calls_target bt = [] ==>
     state_rel_frame machine_frame (eval_base_place cx bt)) /\
  (!cx bt. !mods. target_mutability_ok mods View bt /\ int_calls_target bt = [] ==>
     state_rel_frame machine_frame (eval_target_place cx bt)) /\
  (!cx g v. !mods. atarget_mutability_ok mods View g /\ int_calls_atarget g = [] ==>
     state_rel_frame machine_frame (assign_tuple_targets cx g v)) /\
  (!cx gs vs. !mods. EVERY (atarget_mutability_ok mods View) gs /\ int_calls_atargets gs = [] ==>
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs)) /\
  (!cx es. !mods. EVERY (expr_mutability_ok mods View) es /\ int_calls_exprs es = [] ==>
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
  >- (strip_calls)
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

Resume target_call_free_evaluate[return_some]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
Resume target_call_free_evaluate[log]:
  strip_calls >> gvs[stmt_mutability_ok_def, call_mutability_ok_def]
QED
Resume target_call_free_evaluate[expr_send]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED
Resume target_call_free_evaluate[expr_rawlog]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED
Resume target_call_free_evaluate[expr_selfdestruct]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED
Resume target_call_free_evaluate[expr_create]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED
Resume target_call_free_evaluate[raise_reason]:
  strip_calls >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
      irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
Resume target_call_free_evaluate[assign]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, atarget_mutability_ok_def,
      write_mutability_ok_def, call_mutability_ok_def] >>
  simp[Once evaluate_def] >> match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[machine_frame_read_result] >> rpt strip_tac >> simp[] >>
  ho_match_mp_tac machine_frame_local_place_effect >>
  simp[machine_frame_write_memory_place] >> metis_tac[]
QED
Resume target_call_free_evaluate[append]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_append >> metis_tac[]
QED
Resume target_call_free_evaluate[augassign]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_augassign >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_pop]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_expr_pop >> simp[] >> metis_tac[]
QED
Resume target_call_free_evaluate[for_cons]:
  strip_calls >> irule machine_frame_for_cons >>
  conj_tac >> rpt strip_tac >> Cases_on `x` >> gvs[] >> metis_tac[]
QED
Resume target_call_free_evaluate[for_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_for >> conj_tac
  >- (rpt strip_tac >> Cases_on `x` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
Resume target_call_free_evaluate[base_name]:
  strip_calls >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule machine_frame_sequence >> simp[machine_frame_primitives]
QED
Resume target_call_free_evaluate[base_toplevel]:
  strip_calls >> simp[Once evaluate_def, machine_frame_lookup_global]
QED
Resume target_call_free_evaluate[base_attribute]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_extend_place] >> metis_tac[]
QED
Resume target_call_free_evaluate[target_base]:
  strip_calls >> gvs[Once atarget_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_assign_tuple_base >> metis_tac[]
QED
Resume target_call_free_evaluate[target_tuple]:
  strip_calls >> gvs[Once atarget_mutability_ok_def] >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[machine_frame_primitives] >>
  rename1 `ArrayV a` >> Cases_on `a` >> simp[machine_frame_primitives] >> metis_tac[]
QED
Resume target_call_free_evaluate[targets_cons]:
  strip_calls >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED
Resume target_call_free_evaluate[stmts_cons]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_name]:
  strip_calls >> simp[Once evaluate_def] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives] >> gen_tac >>
  irule machine_frame_sequence >> simp[machine_frame_primitives]
QED
Resume target_call_free_evaluate[expr_attribute]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[machine_frame_select_result]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_struct]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_rawrevert]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_sequence >>
      simp[machine_frame_primitives] >>
      irule machine_frame_bind >> simp[machine_frame_primitives]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_toplevel]:
  strip_calls >> simp[Once evaluate_def, machine_frame_reads]
QED
Resume target_call_free_evaluate[expr_flag]:
  strip_calls >> simp[Once evaluate_def, machine_frame_reads]
QED
Resume target_call_free_evaluate[assert_bare]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]) >> metis_tac[]
QED
Resume target_call_free_evaluate[assert_unreachable]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_if]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >> conj_tac
      >- (irule machine_frame_switch_BoolV >> metis_tac[]) >>
      simp[machine_frame_unchanged_reads]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >> metis_tac[]
QED
Resume target_call_free_evaluate[exprs_cons]:
  strip_calls >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
      irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_extcall]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  `EVERY (expr_mutability_ok mods View) (TAKE 1 es) /\
   EVERY (expr_mutability_ok mods View) (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   EVERY (expr_mutability_ok mods View) (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    simp[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  `EVERY (\e. int_calls_expr e = []) (TAKE 1 es) /\
   EVERY (\e. int_calls_expr e = []) (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   EVERY (\e. int_calls_expr e = []) (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    simp[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "extcall_results" >> metis_tac[]
QED
Resume target_call_free_evaluate[extcall_results]:
  rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def] >> conj_tac
      >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
          simp[machine_frame_read_results] >> gen_tac >>
          simp[state_rel_frame_result] >> metis_tac[machine_frame_ext_call]) >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[iterator_array]:
  strip_calls >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[machine_frame_array_iterator_results]) >> metis_tac[]
QED
Resume target_call_free_evaluate[annassign]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
    simp[machine_frame_def, machine_frame_read_result, machine_frame_new_variable]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_type_builtin]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
    simp[machine_frame_def, machine_frame_primitives]) >> metis_tac[]
QED
Resume target_call_free_evaluate[base_subscript]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def] >> conj_tac
      >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
          simp[machine_frame_read_result, machine_frame_extend_place]) >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[raise_custom]:
  strip_calls >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  irule machine_frame_stmt_custom_error >> rpt strip_tac >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY (expr_mutability_ok mods View) es` by metis_tac[PERM_EVERY] >>
  `EVERY (\e. int_calls_expr e = []) es` by metis_tac[PERM_EVERY] >>
  metis_tac[]
QED
Resume target_call_free_evaluate[if_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
      irule state_rel_frame_finally >> simp[machine_frame_def, machine_frame_primitives] >>
      irule machine_frame_switch_BoolV >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[iterator_range]:
  strip_calls >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
      irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
      >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
          simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
          irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]) >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_rawcall]:
  strip_calls >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
    rpt (irule state_rel_frame_bind_guarded >>
         simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
    simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_rawcalldata]:
  strip_calls >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
    rpt (irule state_rel_frame_bind_guarded >>
         simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
    simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]) >> metis_tac[]
QED
Resume target_call_free_evaluate[assert_reason]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
    irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
    >- (rpt strip_tac >> rpt (irule state_rel_frame_bind_guarded >>
        simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives] >> rpt strip_tac)) >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[assert_custom]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- (rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
    irule (SRULE [Once evaluate_def] machine_frame_stmt_custom_error) >>
    rpt strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
    `EVERY (expr_mutability_ok mods View) es` by metis_tac[PERM_EVERY] >>
  `EVERY (\e. int_calls_expr e = []) es` by metis_tac[PERM_EVERY] >>
  metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_subscript]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
      conj_tac >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
        simp[machine_frame_read_result, machine_frame_select_result]) >> metis_tac[]) >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_builtin]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  Cases_on `bt = Len` >> simp[]
  >- suspend "builtin_len" >>
  Cases_on `bt = Env MsgGas` >> simp[]
  >- simp[machine_frame_next_gas_reading] >> suspend "builtin_other"
QED
Resume target_call_free_evaluate[builtin_len]:
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_reads, machine_frame_primitives]) >>
  Cases_on `es` >> gvs[type_check_def, assert_def, raise_def, vyperContextTheory.builtin_args_length_ok_def, SF ETA_ss] >> metis_tac[]
QED
Resume target_call_free_evaluate[builtin_other]:
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >> simp[]
  >- (irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
      >- (rpt strip_tac >> simp[ignore_bind_def] >>
          match_mp_tac machine_frame_bind >> simp[machine_frame_primitives] >>
          match_mp_tac machine_frame_bind >> simp[machine_frame_primitives]) >>
      gvs[SF ETA_ss] >> metis_tac[]) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- rpt (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
          simp[machine_frame_def, machine_frame_reads, machine_frame_primitives,
               machine_frame_precompile_call_success]) >>
  gvs[SF ETA_ss] >> metis_tac[]
QED
Resume target_call_free_evaluate[assign_tuple]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_tuple_assign >> metis_tac[]
QED
Resume target_call_free_evaluate[target_place]:
  strip_calls >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_get_place] >> metis_tac[]
QED
Resume target_call_free_evaluate[expr_results_cons]:
  strip_calls >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac machine_frame_bind >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Finalise target_call_free_evaluate

Theorem target_call_free_stmts_frame:
  stmts_mutability_ok mods View body /\ int_calls_stmts body = [] ==>
  state_rel_frame machine_frame (eval_stmts cx body)
Proof
  metis_tac[target_call_free_evaluate |> cj 2]
QED
