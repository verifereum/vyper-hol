(* Supported internal calls as transformers of the caller argument frame. *)
Theory targetPureWalkInternalFrame
Ancestors
  targetPureWalkCallees vyperReadOnlyTargetCallFree vyperMachineFrame
  vyperCallOutcomeFrame vyperReadOnlyCalls vyperInterpreter vyperState
  vyperEvalFrame exprLowering compileVyper vyperTypeContract
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

(* Transfer the existing primitive interface to the weaker, log-free frame. *)
val machine_leaf = irule state_rel_frame_machine >>
  conj_tac >- simp[machine_frame_def];

Theorem walk_bind[local]:
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) f /\
  (!v. state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) (g v)) ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (vyperState$bind f g)
Proof
  strip_tac >> match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> simp[]
QED

Theorem target_walk_internal_frame:
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
     function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) ==>
  !ty name actuals fallback.
    supported_program (cx_tops cx) /\
    IS_SOME (supported_function_decl (cx_tops cx) (NONE,name) Internal) /\
    ~call_can_mutate cenv (IntCall (NONE,name)) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr_results cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall (NONE,name)) actuals fallback))
Proof
  rpt strip_tac >>
  Cases_on `lookup_callable_function cx.in_deploy name (cx_tops cx)`
  >- (once_rewrite_tac[evaluate_def] >>
      simp[ignore_bind_def, lift_option_type_def,
           lift_option_def, bind_def, type_check_def, assert_def,
           return_def, raise_def, state_rel_frame_def, machine_frame_def] >>
      Cases_on `MEM (NONE,name) cx.stk` >> simp[]) >>
  PairCases_on `x` >>
  rename1 `lookup_callable_function cx.in_deploy name (cx_tops cx) =
           SOME (mut,nr,args,dflts,ret,body)` >>
  drule_all target_walk_callee_syntax >> strip_tac >> gvs[] >> (
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac walk_bind >>
  conj_tac >- (machine_leaf >> simp[machine_frame_primitives]) >>
  gen_tac >>
  simp[Once lift_option_type_def, lift_option_def, bind_return] >>
  simp[Once lift_option_type_def, lift_option_def, bind_return] >>
  match_mp_tac walk_bind >>
  conj_tac >- (machine_leaf >> simp[machine_frame_primitives]) >>
  gen_tac >> suspend "after_lookup")
QED
Resume target_walk_internal_frame[after_lookup]:
  markerLib.RESUME_TAC >> rpt strip_tac >> BETA_TAC >> (
  match_mp_tac walk_bind >> conj_tac >- (first_assum ACCEPT_TAC) >>
  gen_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- (machine_leaf >> simp[machine_frame_primitives]) >>
  gen_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac walk_bind >>
  conj_tac >- (machine_leaf >>
    match_mp_tac state_rel_frame_finally >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_primitives] >>
    match_mp_tac machine_frame_bind >> simp[machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_read_results] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- (Cases_on `nr` >> simp[machine_frame_primitives] >>
    Cases_on `cx.nonreentrant_slot` >> simp[machine_frame_primitives] >>
    match_mp_tac machine_frame_bind >>
    simp[machine_frame_view_lock, machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- simp[machine_frame_push_function] >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  conj_tac >- (match_mp_tac state_rel_frame_finally_unless_halt >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_primitives] >>
    match_mp_tac state_rel_frame_finally >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_pop_function] >>
    match_mp_tac state_rel_frame_try >>
    conj_tac >- metis_tac[machine_frame_trans] >>
    simp[machine_frame_handlers] >>
    match_mp_tac machine_frame_bind >>
    simp[machine_frame_primitives] >>
    metis_tac[target_call_free_stmts_frame]) >>
  gen_tac >> BETA_TAC >> match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives])
QED
Finalise target_walk_internal_frame
