(* Source-only ordinary evaluation clauses. No oracle typing assumptions. *)
Theory loweringBudgetSourceEvalOrdinary
Ancestors
  evalNoHalt sourceCallCount vyperInterpreter vyperState vyperContext
  vyperMisc vyperValue vyperValueOperation vyperCallOutcome vyperCallOutcomeProps
  supportedExprTraverse supportedStmtTraverse supportedDecls supportedProgram
  vyperTypeCallGraph list pair
Libs BasicProvers evalWalkLib

val _ = Parse.hide "body";

(* These ML terms are the eleven predicates of eval_no_halt_every, with only
   its distinguished exception changed. They introduce no logical constants. *)
val calls_ok = ``\cx cs. EVERY (\c. FST c = NONE /\ ?tops.
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  IS_SOME (supported_function_decl tops c Internal)) cs``;
val err = ``Error (RuntimeError "create outcome accounts")``;
val p_stmt = ``\cx s. ~supported_stmt_expr_exists expr_evm_run_root s /\
  ^calls_ok cx (int_calls_stmt s) ==>
  !st st'. eval_stmt cx s st = (INR ^err,st') ==> F``;
val p_stmts = ``\cx ss. ~supported_stmts_expr_exists expr_evm_run_root ss /\
  ^calls_ok cx (int_calls_stmts ss) ==>
  !st st'. eval_stmts cx ss st = (INR ^err,st') ==> F``;
val p_iter = ``\cx it. ~supported_iterator_exists expr_evm_run_root it /\
  ^calls_ok cx (int_calls_iterator it) ==>
  !st st'. eval_iterator cx it st = (INR ^err,st') ==> F``;
val p_for = ``\cx tv nm ss vs. ~supported_stmts_expr_exists expr_evm_run_root ss /\
  ^calls_ok cx (int_calls_stmts ss) ==>
  !st st'. eval_for cx tv nm ss vs st = (INR ^err,st') ==> F``;
val p_expr = ``\cx e. ~supported_expr_exists expr_evm_run_root e /\
  ^calls_ok cx (int_calls_expr e) ==>
  !st st'. eval_expr cx e st = (INR ^err,st') ==> F``;
val p_exprs = ``\cx es. EVERY (\e.
  ~supported_expr_exists expr_evm_run_root e /\
  ^calls_ok cx (int_calls_expr e)) es ==>
  !st st'. eval_exprs cx es st = (INR ^err,st') ==> F``;
val p_base = ``\cx t. ~supported_target_exists expr_evm_run_root t /\
  ^calls_ok cx (int_calls_target t) ==>
  !st st'. eval_base_place cx t st = (INR ^err,st') ==> F``;
val p_target = ``\cx t. ~supported_target_exists expr_evm_run_root t /\
  ^calls_ok cx (int_calls_target t) ==>
  !st st'. eval_target_place cx t st = (INR ^err,st') ==> F``;
val p_tuple = ``\cx g v. ~supported_assignment_exists expr_evm_run_root g /\
  ^calls_ok cx (int_calls_atarget g) ==>
  !st st'. assign_tuple_targets cx g v st = (INR ^err,st') ==> F``;
val p_tuples = ``\cx gs vs. ~supported_assignments_exists expr_evm_run_root gs /\
  ^calls_ok cx (int_calls_atargets gs) ==>
  !st st'. assign_tuple_target_list cx gs vs st = (INR ^err,st') ==> F``;
val p_results = ``\cx es. EVERY (\e.
  ~supported_expr_exists expr_evm_run_root e /\
  ^calls_ok cx (int_calls_expr e)) es ==>
  !st st'. eval_expr_results cx es st = (INR ^err,st') ==> F``;
val predicates = [p_stmt,p_stmts,p_iter,p_for,p_expr,p_exprs,p_base,p_target,
                  p_tuple,p_tuples,p_results];
val specialized_ind = BETA_RULE (ISPECL predicates evaluate_ind);
val clauses = strip_conj (fst (dest_imp (concl specialized_ind)));
(* The Call constant occurs only in the nine Call-constructor clauses:
   partition by syntax rather than by fragile induction-clause positions. *)
fun call_clause tm = can (find_term (same_const ``vyperAST$Call``)) tm;
val _ = app (fn (n,c) => if call_clause c then
          print ("CALL clause " ^ Int.toString n ^ "\n") else ())
  (ListPair.zip (List.tabulate (length clauses, fn n => n+1), clauses));
val ordinary_clauses = List.filter (not o call_clause) clauses;
val ordinary_goal = list_mk_conj ordinary_clauses;
fun final_premise tm =
  if is_forall tm then final_premise (#2 (dest_forall tm))
  else let val (a,b) = dest_imp tm
       in if same_const b F then a else final_premise b end;
val _ = app (fn (n,c) => print (Int.toString n ^ ": " ^
  term_to_string (rator (#1 (dest_eq (final_premise c)))) ^ "\n"))
  (ListPair.zip (List.tabulate (length ordinary_clauses, fn n => n+1),
                 ordinary_clauses));

(* Inline primitive reduction, shared by the clauses without publishing a
   second family of sourceCallCount's private exclusion lemmas. *)
val read_defs = [oneline read_result_def, oneline read_place_def,
  eval_result_CASE_rator, place_CASE_rator, read_storage_slot_def,
  vyperStorageBackendTheory.get_storage_backend_eq, get_immutables_def,
  get_address_immutables_def, get_scopes_def, lift_option_def,
  lift_option_type_def, lift_sum_def, return_def, raise_def,
  bind_def, ignore_bind_def, option_CASE_rator, sum_CASE_rator,
  prod_CASE_rator, AllCaseEqs()];
val syn_defs = [supported_stmt_expr_exists_def, supported_expr_exists_def,
  supported_assignment_exists_def, supported_iterator_exists_def,
  supported_assert_exists_def, supported_raise_exists_def,
  expr_evm_run_root_def, int_calls_stmt_def, int_calls_expr_def,
  int_calls_atarget_def, int_calls_iterator_def, int_calls_assert_reason_def,
  int_calls_raise_reason_def, EVERY_APPEND];
val read_error_tac =
  qpat_x_assum `read_result _ _ _ = (INR _,_)`
    (fn th => POP_ASSUM_LIST (K (assume_tac th))) >>
  gvs read_defs >>
  imp_res_tac read_memory_path_error_shape >>
  imp_res_tac evaluate_subscripts_error_shape >> gvs[];

(* One suspension per original clause: avoid matching a recursive IH instead
   of the constructor's conclusion (Builtin has eval_exprs [addr] in its IH). *)
fun isolate_clauses [nm] = suspend nm
  | isolate_clauses (nm::nms) =
      conj_tac >- suspend nm >> isolate_clauses nms
  | isolate_clauses [] = NO_TAC;

Theorem source_no_create_error_ordinary_cases:
  ^ordinary_goal
Proof
  isolate_clauses
    ["base","base","base","base","return_some","base","base",
     "raise_reason","raise_custom","assert_bare","assert_unreachable",
     "assert_reason","assert_custom","log","annassign","append",
     "assign_base","assign_tuple","augassign","if","for","expr_stmt",
     "base","stmts_cons","array","range","for_nil","for_cons",
     "name","topname","flag","ifexp","literal","struct","subscript",
     "attribute","builtin","pop","typebuiltin","base","exprs_cons",
     "name_target","top_target","attribute_target","subscript_target",
     "target_place","tuple_base","tuple_tuple","base","tuple_cons",
     "tuple_extra_values","tuple_extra_targets","base","results_cons"]
QED

Resume source_no_create_error_ordinary_cases[return_some]:
  rpt gen_tac >> rpt strip_tac >>
  pop_assum mp_tac >>
  simp[Once evaluate_def, return_def, raise_def, ignore_bind_def, bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs syn_defs >>
  all_tac >>~- ([`read_result _ _ _ = (INR _,_)`], read_error_tac) >>
  FAIL_TAC "return remaining"
QED

Resume source_no_create_error_ordinary_cases[base]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  gvs[Once evaluate_def, return_def, raise_def]
QED

Resume source_no_create_error_ordinary_cases[expr_stmt]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs syn_defs >>
  gvs[type_check_def, assert_def, AllCaseEqs()]
QED

Resume source_no_create_error_ordinary_cases[raise_reason]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs syn_defs >>
  all_tac >>~- ([`read_result _ _ _ = (INR _,_)`], read_error_tac) >>
  gvs[lift_option_type_def, return_def, raise_def, option_CASE_rator,
      AllCaseEqs()]
QED

Resume source_no_create_error_ordinary_cases[literal]:
  rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Resume source_no_create_error_ordinary_cases[name]:
  rpt strip_tac >> gvs[Once evaluate_def, get_scopes_def, lift_option_type_def,
    bind_def, ignore_bind_def, type_check_def, assert_def,
    return_def, raise_def, option_CASE_rator, AllCaseEqs()]
QED

Resume source_no_create_error_ordinary_cases[stmts_cons]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs syn_defs >> metis_tac[]
QED

Resume source_no_create_error_ordinary_cases[for_nil]:
  rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

Resume source_no_create_error_ordinary_cases[results_cons]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[EVERY_DEF] >> metis_tac[]
QED

Resume source_no_create_error_ordinary_cases[exprs_cons]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[EVERY_DEF] >>
  all_tac >>~- ([`read_result _ _ _ = (INR _,_)`], read_error_tac) >>
  metis_tac[]
QED

Resume source_no_create_error_ordinary_cases[struct]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs syn_defs >> FAIL_TAC "struct syntax"
QED

Resume source_no_create_error_ordinary_cases[target_place]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs syn_defs >> FAIL_TAC "target place"
QED

Resume source_no_create_error_ordinary_cases[raise_custom]:
  FAIL_TAC "raise_custom"
QED
Resume source_no_create_error_ordinary_cases[assert_bare]: FAIL_TAC "assert_bare" QED
Resume source_no_create_error_ordinary_cases[assert_unreachable]: FAIL_TAC "assert_unreachable" QED
Resume source_no_create_error_ordinary_cases[assert_reason]: FAIL_TAC "assert_reason" QED
Resume source_no_create_error_ordinary_cases[assert_custom]: FAIL_TAC "assert_custom" QED
Resume source_no_create_error_ordinary_cases[log]: FAIL_TAC "log" QED
Resume source_no_create_error_ordinary_cases[annassign]: FAIL_TAC "annassign" QED
Resume source_no_create_error_ordinary_cases[append]: FAIL_TAC "append" QED
Resume source_no_create_error_ordinary_cases[assign_base]: FAIL_TAC "assign_base" QED
Resume source_no_create_error_ordinary_cases[assign_tuple]: FAIL_TAC "assign_tuple" QED
Resume source_no_create_error_ordinary_cases[augassign]: FAIL_TAC "augassign" QED
Resume source_no_create_error_ordinary_cases[if]: FAIL_TAC "if" QED
Resume source_no_create_error_ordinary_cases[for]: FAIL_TAC "for" QED
Resume source_no_create_error_ordinary_cases[array]: FAIL_TAC "array" QED
Resume source_no_create_error_ordinary_cases[range]: FAIL_TAC "range" QED
Resume source_no_create_error_ordinary_cases[for_cons]: FAIL_TAC "for_cons" QED
Resume source_no_create_error_ordinary_cases[topname]: FAIL_TAC "topname" QED
Resume source_no_create_error_ordinary_cases[flag]: FAIL_TAC "flag" QED
Resume source_no_create_error_ordinary_cases[ifexp]: FAIL_TAC "ifexp" QED
Resume source_no_create_error_ordinary_cases[subscript]: FAIL_TAC "subscript" QED
Resume source_no_create_error_ordinary_cases[attribute]: FAIL_TAC "attribute" QED
Resume source_no_create_error_ordinary_cases[builtin]: FAIL_TAC "builtin" QED
Resume source_no_create_error_ordinary_cases[pop]: FAIL_TAC "pop" QED
Resume source_no_create_error_ordinary_cases[typebuiltin]: FAIL_TAC "typebuiltin" QED
Resume source_no_create_error_ordinary_cases[name_target]: FAIL_TAC "name_target" QED
Resume source_no_create_error_ordinary_cases[top_target]: FAIL_TAC "top_target" QED
Resume source_no_create_error_ordinary_cases[attribute_target]: FAIL_TAC "attribute_target" QED
Resume source_no_create_error_ordinary_cases[subscript_target]: FAIL_TAC "subscript_target" QED
Resume source_no_create_error_ordinary_cases[tuple_base]: FAIL_TAC "tuple_base" QED
Resume source_no_create_error_ordinary_cases[tuple_tuple]: FAIL_TAC "tuple_tuple" QED
Resume source_no_create_error_ordinary_cases[tuple_cons]: FAIL_TAC "tuple_cons" QED
Resume source_no_create_error_ordinary_cases[tuple_extra_values]: FAIL_TAC "tuple_extra_values" QED
Resume source_no_create_error_ordinary_cases[tuple_extra_targets]: FAIL_TAC "tuple_extra_targets" QED

Finalise source_no_create_error_ordinary_cases
