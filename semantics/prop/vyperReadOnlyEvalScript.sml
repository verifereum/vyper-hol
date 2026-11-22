(* Mutual evaluator frame for checked read-only syntax. *)
Theory vyperReadOnlyEval
Ancestors
  vyperReadOnlyBranches vyperReadOnlyCalls vyperReadOnlySyntax vyperReadOnlyTargets
  vyperMachineFrame vyperTypeContract vyperInterpreter vyperCallOutcomeFrame vyperState
  vyperAST list sorting vyperTypeCallGraph
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

Theorem int_calls_exprs_FLAT_MAP:
  int_calls_exprs es = FLAT (MAP int_calls_expr es)
Proof
  Induct_on `es` >> simp[int_calls_expr_def]
QED

val every_int_calls_exprs = SIMP_CONV (srw_ss())
    [int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP]
    ``EVERY admissible (int_calls_exprs es)``;

val every_int_calls_named_exprs =
  PURE_REWRITE_RULE [vyperTypeEvalProofsTheory.int_calls_exprs_MAP_SND]
    (INST [``es : expr list`` |-> ``MAP SND (kes : (identifier # expr) list)``]
      every_int_calls_exprs);

val strip_call_requirements = rpt strip_tac >>
  gvs[int_calls_expr_def, int_calls_stmt_def, int_calls_iterator_def,
      int_calls_atarget_def, int_calls_assert_reason_def,
      int_calls_raise_reason_def, EVERY_APPEND, every_int_calls_exprs,
      every_int_calls_named_exprs];

val strip_calls = strip_call_requirements >>
  qpat_x_assum `!src fn ts. _ ==> ALOOKUP _ src = SOME ts /\ _` kall_tac;

val read_only_bind = match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- (simp[SF ETA_ss] >> metis_tac[]) >>
  rpt strip_tac >> BETA_TAC;

(* A caller can supply lookup agreement only for the internal call sites
   reached by its read-only syntax. Successful read-only callees must
   preserve the same restriction for their defaults and body. *)
Theorem evaluate_read_only_calls:
  !module_code in_deploy mods admissible.
  (!src fn ts. admissible (src,fn) /\ module_code src = SOME ts ==>
     ALOOKUP mods src = SOME ts /\
     lookup_callable_function in_deploy fn ts =
       lookup_callable_function F fn ts /\
     (!mut nr args dflts ret body.
        lookup_callable_function in_deploy fn ts =
          SOME (mut,nr,args,dflts,ret,body) /\
        (mut = View \/ mut = Pure) ==>
        EVERY (expr_mutability_ok mods View) dflts /\
        stmts_mutability_ok mods View body /\
        EVERY admissible (int_calls_exprs dflts) /\
        EVERY admissible (int_calls_stmts body))) ==>
  (!cx s. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     stmt_mutability_ok mods View s /\ EVERY admissible (int_calls_stmt s) ==>
     state_rel_frame machine_frame (eval_stmt cx s)) /\
  (!cx ss. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     stmts_mutability_ok mods View ss /\ EVERY admissible (int_calls_stmts ss) ==>
     state_rel_frame machine_frame (eval_stmts cx ss)) /\
  (!cx it. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     iterator_mutability_ok mods View it /\ EVERY admissible (int_calls_iterator it) ==>
     state_rel_frame machine_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     stmts_mutability_ok mods View body /\ EVERY admissible (int_calls_stmts body) ==>
     state_rel_frame machine_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     expr_mutability_ok mods View e /\ EVERY admissible (int_calls_expr e) ==>
     state_rel_frame machine_frame (eval_expr cx e)) /\
  (!cx es. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     EVERY (expr_mutability_ok mods View) es /\ EVERY admissible (int_calls_exprs es) ==>
     state_rel_frame machine_frame (eval_exprs cx es)) /\
  (!cx bt. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     target_mutability_ok mods View bt /\ EVERY admissible (int_calls_target bt) ==>
     state_rel_frame machine_frame (eval_base_place cx bt)) /\
  (!cx bt. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     target_mutability_ok mods View bt /\ EVERY admissible (int_calls_target bt) ==>
     state_rel_frame machine_frame (eval_target_place cx bt)) /\
  (!cx g v. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     atarget_mutability_ok mods View g /\ EVERY admissible (int_calls_atarget g) ==>
     state_rel_frame machine_frame (assign_tuple_targets cx g v)) /\
  (!cx gs vs. get_module_code cx = module_code /\ cx.in_deploy = in_deploy /\
     EVERY (atarget_mutability_ok mods View) gs /\ EVERY admissible (int_calls_atargets gs) ==>
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs))
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac
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
  >> simp[Once evaluate_def, machine_frame_primitives]
QED

Resume evaluate_read_only_calls[return_some]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives]
QED

Resume evaluate_read_only_calls[log]:
  strip_calls >> gvs[stmt_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only_calls[expr_send]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only_calls[expr_rawlog]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only_calls[expr_selfdestruct]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only_calls[expr_create]:
  strip_calls >> gvs[expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def]
QED

Resume evaluate_read_only_calls[raise_reason]:
  strip_calls >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only_calls[assign]:
  strip_calls >>
  gvs[Once stmt_mutability_ok_def, atarget_mutability_ok_def,
      write_mutability_ok_def, call_mutability_ok_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[machine_frame_trans] >>
  conj_tac >- simp[machine_frame_read_result] >> rpt strip_tac >> simp[] >>
  ho_match_mp_tac machine_frame_local_place_effect >>
  simp[machine_frame_write_memory_place] >> metis_tac[]
QED

Resume evaluate_read_only_calls[append]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_append >> metis_tac[]
QED

Resume evaluate_read_only_calls[augassign]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_stmt_augassign >> metis_tac[]
QED

Resume evaluate_read_only_calls[expr_pop]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_expr_pop >> simp[] >> metis_tac[]
QED

Resume evaluate_read_only_calls[for_cons]:
  strip_calls >> irule machine_frame_for_cons >> rpt conj_tac >>
  rpt strip_tac >> Cases_on `x` >> fs[] >> metis_tac[]
QED

Resume evaluate_read_only_calls[for_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_for >> conj_tac
  >- (rpt strip_tac >> Cases_on `x` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_read_only_calls[base_name]:
  strip_calls >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule machine_frame_sequence >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only_calls[base_toplevel]:
  strip_calls >> simp[Once evaluate_def, machine_frame_lookup_global]
QED

Resume evaluate_read_only_calls[base_attribute]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_extend_place] >> metis_tac[]
QED

Resume evaluate_read_only_calls[target_base]:
  strip_calls >> gvs[Once atarget_mutability_ok_def, write_mutability_ok_def, call_mutability_ok_def] >>
  irule machine_frame_assign_tuple_base >> metis_tac[]
QED

Resume evaluate_read_only_calls[target_tuple]:
  strip_calls >> gvs[Once atarget_mutability_ok_def] >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[machine_frame_primitives] >>
  rename1 `ArrayV a` >> Cases_on `a` >> simp[machine_frame_primitives] >> metis_tac[]
QED

Resume evaluate_read_only_calls[targets_cons]:
  strip_calls >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only_calls[stmts_cons]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only_calls[expr_name]:
  strip_calls >> simp[Once evaluate_def] >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives] >> gen_tac >>
  irule machine_frame_sequence >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only_calls[expr_attribute]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule machine_frame_bind >> simp[machine_frame_select_result]
QED

Resume evaluate_read_only_calls[expr_struct]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only_calls[expr_rawrevert]:
  strip_calls >> gvs[Once expr_mutability_ok_def, SF ETA_ss] >> simp[Once evaluate_def] >>
  irule machine_frame_bind >> simp[] >>
  rpt strip_tac >> irule machine_frame_sequence >>
  simp[machine_frame_primitives] >>
  irule machine_frame_bind >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only_calls[expr_toplevel]:
  strip_calls >> simp[Once evaluate_def, machine_frame_reads]
QED

Resume evaluate_read_only_calls[expr_flag]:
  strip_calls >> simp[Once evaluate_def, machine_frame_reads]
QED

Resume evaluate_read_only_calls[assert_bare]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule machine_frame_bind >> simp[] >>
  rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only_calls[assert_unreachable]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule machine_frame_bind >> simp[] >>
  rpt strip_tac >> irule machine_frame_switch_BoolV >> simp[machine_frame_primitives]
QED

Resume evaluate_read_only_calls[expr_if]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  read_only_bind >> rpt strip_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- (irule machine_frame_switch_BoolV >> metis_tac[]) >>
  simp[machine_frame_unchanged_reads]
QED

Resume evaluate_read_only_calls[expr_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  metis_tac[]
QED

Resume evaluate_read_only_calls[exprs_cons]:
  strip_calls >> gvs[] >> simp[Once evaluate_def] >>
  read_only_bind >> suspend "exprs_materialise"
QED

Resume evaluate_read_only_calls[exprs_materialise]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> metis_tac[]
QED

Resume evaluate_read_only_calls[expr_extcall]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  `EVERY (expr_mutability_ok mods View) (TAKE 1 es) /\
   EVERY (expr_mutability_ok mods View) (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   EVERY (expr_mutability_ok mods View) (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    simp[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  `EVERY (\e. EVERY admissible (int_calls_expr e)) (TAKE 1 es) /\
   EVERY (\e. EVERY admissible (int_calls_expr e))
     (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   EVERY (\e. EVERY admissible (int_calls_expr e))
     (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    simp[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  simp[Once evaluate_def] >> read_only_bind >> suspend "extcall_results"
QED

Resume evaluate_read_only_calls[extcall_results]:
  simp[] >> read_only_bind >>
  simp[] >> read_only_bind >>
  simp[state_rel_frame_result] >> metis_tac[machine_frame_ext_call]
QED

Resume evaluate_read_only_calls[iterator_array]:
  strip_calls >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  read_only_bind >> suspend "iterator_array_value"
QED

Resume evaluate_read_only_calls[iterator_array_value]:
  rpt strip_tac >> simp[machine_frame_array_iterator_results]
QED

Resume evaluate_read_only_calls[annassign]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "annassign_value" >> metis_tac[]
QED

Resume evaluate_read_only_calls[annassign_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result, machine_frame_new_variable]
QED

Resume evaluate_read_only_calls[expr_type_builtin]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "type_builtin_value" >> metis_tac[]
QED

Resume evaluate_read_only_calls[type_builtin_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only_calls[base_subscript]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  read_only_bind >> suspend "base_subscript_expr"
QED

Resume evaluate_read_only_calls[base_subscript_expr]:
  rpt strip_tac >> simp[] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac machine_frame_bind >>
      simp[machine_frame_read_result, machine_frame_extend_place]) >> metis_tac[]
QED

Resume evaluate_read_only_calls[raise_custom]:
  strip_calls >> gvs[stmt_mutability_ok_def, raise_reason_mutability_ok_def] >>
  irule machine_frame_stmt_custom_error >> rpt strip_tac >>
  drule order_custom_error_args_perm >> strip_tac >>
  `EVERY (expr_mutability_ok mods View) es /\
   EVERY (\e. EVERY admissible (int_calls_expr e)) es` by
    metis_tac[PERM_EVERY] >>
  metis_tac[]
QED

Resume evaluate_read_only_calls[if_stmt]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  read_only_bind >> suspend "if_scope"
QED

Resume evaluate_read_only_calls[if_scope]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  irule state_rel_frame_finally >> simp[machine_frame_def, machine_frame_primitives] >>
  irule machine_frame_switch_BoolV >> metis_tac[]
QED

Resume evaluate_read_only_calls[iterator_range]:
  strip_calls >> gvs[iterator_mutability_ok_def] >> simp[Once evaluate_def] >>
  read_only_bind >> suspend "range_first_value"
QED

Resume evaluate_read_only_calls[range_first_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  read_only_bind >> suspend "range_second_value"
QED

Resume evaluate_read_only_calls[range_second_value]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]
QED

Resume evaluate_read_only_calls[expr_rawcall]:
  strip_calls >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> read_only_bind >> suspend "raw_operands"
QED

Resume evaluate_read_only_calls[raw_operands]:
  rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]
QED

Resume evaluate_read_only_calls[expr_rawcalldata]:
  strip_calls >> Cases_on `flags.rcf_is_static` >>
  gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, call_mutability_ok_def, SF ETA_ss] >>
  simp[Once evaluate_def] >> read_only_bind >> suspend "rawcalldata_operands"
QED

Resume evaluate_read_only_calls[rawcalldata_operands]:
  rpt strip_tac >> BETA_TAC >> simp[ignore_bind_def] >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  simp[state_rel_frame_result] >> metis_tac[machine_frame_raw_call]
QED

Resume evaluate_read_only_calls[assert_reason]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> read_only_bind >> suspend "assert_reason_switch"
QED

Resume evaluate_read_only_calls[assert_reason_switch]:
  rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
  read_only_bind >> suspend "assert_reason_value"
QED

Resume evaluate_read_only_calls[assert_reason_value]:
  rpt strip_tac >>
  rpt (irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_read_result, machine_frame_primitives] >> rpt strip_tac)
QED

Resume evaluate_read_only_calls[assert_custom]:
  strip_calls >> gvs[Once stmt_mutability_ok_def, assert_reason_mutability_ok_def] >>
  simp[Once evaluate_def] >> read_only_bind >> suspend "assert_custom_switch"
QED

Resume evaluate_read_only_calls[assert_custom_switch]:
  rpt strip_tac >> BETA_TAC >> irule machine_frame_switch_BoolV >> simp[] >>
  irule (SRULE [Once evaluate_def] machine_frame_stmt_custom_error) >>
  rpt strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
  `EVERY (expr_mutability_ok mods View) es /\
   EVERY (\e. EVERY admissible (int_calls_expr e)) es` by
    metis_tac[PERM_EVERY] >>
  metis_tac[]
QED

Resume evaluate_read_only_calls[expr_subscript]:
  strip_calls >> gvs[Once expr_mutability_ok_def] >> simp[Once evaluate_def] >>
  read_only_bind >> suspend "subscript_second_expr"
QED
Resume evaluate_read_only_calls[subscript_second_expr]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "subscript_index" >>
  Cases_on `subscript_reads_base cx e e'` >> simp[machine_frame_primitives] >>
  irule machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_primitives]
QED
Resume evaluate_read_only_calls[subscript_index]:
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "subscript_tail" >> metis_tac[]
QED
Resume evaluate_read_only_calls[subscript_tail]:
  rpt strip_tac >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_select_result]
QED

Resume evaluate_read_only_calls[expr_builtin]:
  strip_calls >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  Cases_on `bt = Len` >> simp[]
  >- suspend "builtin_len" >>
  Cases_on `bt = Env MsgGas` >> simp[]
  >- simp[machine_frame_next_gas_reading]
  >> suspend "builtin_other"
QED

Resume evaluate_read_only_calls[builtin_len]:
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_reads, machine_frame_primitives]) >>
  Cases_on `es` >> gvs[type_check_def, assert_def, raise_def, vyperContextTheory.builtin_args_length_ok_def, SF ETA_ss] >> metis_tac[]
QED

Resume evaluate_read_only_calls[builtin_other]:
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- (Cases_on `is_self_codesize bt es` >>
      rpt (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
           simp[machine_frame_def, machine_frame_reads, machine_frame_primitives,
                machine_frame_precompile_call_success])) >>
  gvs[SF ETA_ss] >> Cases_on `code_slice_source bt es` >> simp[]
  >- metis_tac[] >>
  rename1 `_ = SOME p` >> PairCases_on `p` >> simp[] >>
  `EVERY (expr_mutability_ok mods View) (TL es) /\
   expr_mutability_ok mods View p1 /\
   EVERY (\e. EVERY admissible (int_calls_expr e)) (TL es) /\
   EVERY admissible (int_calls_expr p1)` by
    (qpat_x_assum `code_slice_source _ _ = SOME _` mp_tac >>
     qpat_x_assum `EVERY (expr_mutability_ok _ _) es` mp_tac >>
     qpat_x_assum `EVERY (\e. EVERY _ _) es` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[code_slice_source_SOME] >> gvs[expr_mutability_ok_def, int_calls_expr_def]) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
       simp[machine_frame_def, machine_frame_reads, machine_frame_primitives,
            machine_frame_precompile_call_success])
QED

Resume evaluate_read_only_calls[expr_intcall]:
  strip_call_requirements >> gvs[Once expr_mutability_ok_def, call_target_mutability_ok_def, SF ETA_ss] >>
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
  `ALOOKUP mods src_id_opt = SOME ts /\
   lookup_callable_function cx.in_deploy fn ts = lookup_callable_function F fn ts` by
    (qpat_assum `!src fn ts. _`
       (qspecl_then [`src_id_opt`, `fn`, `ts`] mp_tac) >> simp[]) >>
  SUBGOAL_THEN ``mut = View \/ mut = Pure`` assume_tac
  >- (qpat_x_assum `option_CASE (ALOOKUP mods src_id_opt) _ _` mp_tac >>
     `lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body)` by
       metis_tac[] >>
     Cases_on `mut` >> simp[call_mutability_ok_def]) >>
  `EVERY (expr_mutability_ok mods View) dflts /\ stmts_mutability_ok mods View body /\
   EVERY (\e. EVERY admissible (int_calls_expr e)) dflts /\
   EVERY admissible (int_calls_stmts body)` by
    (qpat_assum `!src fn ts. _`
       (qspecl_then [`src_id_opt`, `fn`, `ts`] mp_tac) >>
     simp[every_int_calls_exprs] >>
     disch_then (qspecl_then [`mut`, `nr`, `args`, `dflts`, `ret`, `body`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "intcall_after_args" >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3. _ ==> state_rel_frame _ (eval_exprs cx es)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  simp[arithmeticTheory.ADD_COMM] >> disch_then drule >>
  simp[]
QED

Resume evaluate_read_only_calls[intcall_after_args]:
  rpt strip_tac >> BETA_TAC >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac >- suspend "intcall_after_defaults" >>
  irule state_rel_frame_finally >> simp[machine_frame_def, machine_frame_primitives] >>
  simp[ignore_bind_def] >> irule state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3 s6 vs t4 s7 prev t5 s8 t6. _ ==> _ ==> state_rel_frame _ (eval_exprs _ _)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >> simp[arithmeticTheory.ADD_COMM] >>
  disch_then drule >> disch_then drule >> disch_then drule >> disch_then drule >>
  simp[every_int_calls_exprs, rich_listTheory.EVERY_DROP, FUN_EQ_THM,
       vyperTypeEvalProofsTheory.get_module_code_stk_irrelevant]
QED

Resume evaluate_read_only_calls[intcall_after_defaults]:
  rpt strip_tac >> BETA_TAC >>
  ntac 2 (irule state_rel_frame_bind_guarded >>
          simp[machine_frame_def, machine_frame_primitives] >> rpt strip_tac) >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >> conj_tac
  >- suspend "intcall_after_lock" >>
  qpat_x_assum `mut = View \/ mut = Pure` strip_assume_tac >>
  simp[machine_frame_internal_lock,
       REWRITE_RULE [ignore_bind_def] machine_frame_internal_lock]
QED

Resume evaluate_read_only_calls[intcall_after_lock]:
  rpt strip_tac >> BETA_TAC >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_push_function] >>
  rpt strip_tac >>
  qpat_assum `!s t s3 ts t1 s4 tup t2 s5 t3 s6 vs t4 s7 prev t5 s8 dv t6 s9 env t7 s10 rtv t8 s11 t9 s12 cx1 t10. _ ==> _ ==> state_rel_frame _ (eval_stmts _ _)`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >> simp[arithmeticTheory.ADD_COMM] >>
  ntac 3 (disch_then drule) >> simp[ignore_bind_def] >>
  ntac 2 (disch_then drule) >> simp[] >>
  ntac 3 (disch_then drule) >>
  impl_tac
  >- (qpat_x_assum `push_function _ _ cx _ = _` mp_tac >>
      simp[push_function_def, return_def] >> strip_tac >>
      qpat_x_assum `cx with stk updated_by _ = _` (fn th => REWRITE_TAC [GSYM th]) >>
      simp[FUN_EQ_THM, vyperTypeEvalProofsTheory.get_module_code_stk_irrelevant]) >>
  strip_tac >>
  `~(nr /\ mut <> View /\ mut <> Pure)` by metis_tac[] >>
  simp[ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> irule state_rel_frame_bind_guarded >>
      simp[machine_frame_def, machine_frame_primitives]) >>
  simp[finally_unless_halt_return] >>
  irule state_rel_frame_finally >> simp[machine_frame_def] >> conj_tac
  >- (irule state_rel_frame_try >> simp[machine_frame_def, machine_frame_handlers] >>
      irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_primitives]) >>
  simp[machine_frame_pop_function]
QED

Resume evaluate_read_only_calls[assign_tuple]:
  strip_calls >> gvs[Once stmt_mutability_ok_def] >>
  irule machine_frame_stmt_tuple_assign >> metis_tac[]
QED

Resume evaluate_read_only_calls[target_place]:
  strip_calls >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_get_place] >> metis_tac[]
QED

Finalise evaluate_read_only_calls

Theorem read_only_context_calls[local]:
  read_only_context mods cx ==>
  !src fn ts. get_module_code cx src = SOME ts ==>
    ALOOKUP mods src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = lookup_callable_function F fn ts /\
    (!mut nr args dflts ret body.
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
       (mut = View \/ mut = Pure) ==>
       EVERY (expr_mutability_ok mods View) dflts /\
       stmts_mutability_ok mods View body)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >- gvs[read_only_context_def, vyperContextTheory.get_module_code_def] >>
  conj_tac >- gvs[read_only_context_def] >>
  metis_tac[read_only_context_callee]
QED

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
     state_rel_frame machine_frame (assign_tuple_target_list cx gs vs))
Proof
  rpt conj_tac >> rpt strip_tac >>
  (mp_tac (Q.SPECL [`get_module_code cx`, `cx.in_deploy`, `mods`, `K T`]
    evaluate_read_only_calls) >>
   impl_tac >- (drule read_only_context_calls >> simp[EVERY_MEM] >> metis_tac[]) >>
   strip_tac >> first_assum irule >> simp[EVERY_MEM])
QED

Theorem machine_frame_eval_stmts:
  read_only_context mods cx /\ stmts_mutability_ok mods View body ==>
  state_rel_frame machine_frame (eval_stmts cx body)
Proof
  metis_tac[ evaluate_read_only |> cj 2 ]
QED

