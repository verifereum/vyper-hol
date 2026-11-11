Theory targetInternalCallStorageFrame
Ancestors
  targetCallLockFrame vyperTypeEvalSoundness vyperEvalFrame vyperMachineFrame vyperCallOutcomeFrame
  vyperInterpreter vyperState vyperStorageBackend pair list
Libs evalWalkLib monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Triviality lock_frame:
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) ==>
  state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
    lookup_storage w (get_storage cx s tr)) (lock_if_nr cx nr view) /\
  state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
    lookup_storage w (get_storage cx s tr)) (unlock_if_nr cx nr view)
Proof
  pure_rewrite_tac[state_rel_frame_result] >> BETA_TAC >> disch_tac >>
  conj_tac
  >- (rpt strip_tac >> irule lock_if_nr_get_storage_frame >>
      metis_tac[]) >>
  rpt strip_tac >> irule unlock_if_nr_get_storage_frame >>
  metis_tac[]
QED

val CALL_FRAME_STEP = evalWalkLib.STEP {
  net = evalWalkLib.walk_net
    (map SPEC_ALL [state_rel_frame_bind_guarded, state_rel_frame_try,
                   state_rel_frame_finally, cj 1 lock_frame, cj 2 lock_frame]) [],
  at = RAND_CONV,
  unfolds = [ignore_bind_def],
  intros = [CHANGED_TAC (simp_tac bool_ss [FST, SND]),
    CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac,
    conj_tac, CONV_TAC (RAND_CONV ETA_CONV)],
  fallbacks = [
    FIRST_PROVE [irule state_rel_frame_machine >>
      simp[machine_frame_def, get_storage_def,
        machine_frame_primitives, machine_frame_handlers,
        machine_frame_push_function, machine_frame_pop_function]],
    evalWalkLib.IH_TAC {stop = K false,
      normalise = SIMP_RULE (srw_ss()) [FST, SND]}]};

Theorem internal_call_storage_frame:
  ~cx.in_deploy /\
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) /\
  state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
    lookup_storage w (get_storage cx s tr)) (eval_expr_results cx es) /\
  (!ts mut nr args dflts ret stmts.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) ==>
    state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
      lookup_storage w (get_storage cx s tr))
      (eval_exprs (cx with stk updated_by CONS (src,fn))
        (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts))) /\
  (!results. state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
    lookup_storage w (get_storage cx s tr)) (read_results cx results)) /\
  (!ts mut nr args dflts ret stmts.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) ==>
    state_rel_frame (\s t. lookup_storage w (get_storage cx t tr) =
      lookup_storage w (get_storage cx s tr))
      (eval_stmts (cx with stk updated_by CONS (src,fn)) stmts)) ==>
  !st res st'. eval_expr cx (Call ty (IntCall (src,fn)) es ann) st = (res,st') ==>
    lookup_storage w (get_storage cx st' tr) = lookup_storage w (get_storage cx st tr)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!s t u. (lookup_storage w (get_storage cx t tr) = lookup_storage w (get_storage cx s tr)) /\
    (lookup_storage w (get_storage cx u tr) = lookup_storage w (get_storage cx t tr)) ==>
    lookup_storage w (get_storage cx u tr) = lookup_storage w (get_storage cx s tr)` by simp[] >>
  `!s t. machine_frame s t ==> lookup_storage w (get_storage cx t tr) =
    lookup_storage w (get_storage cx s tr)` by
    (Cases_on `tr` >> gvs[machine_frame_def, get_storage_def]) >>
  qsuff_tac `state_rel_frame
    (\s t. lookup_storage w (get_storage cx t tr) =
      lookup_storage w (get_storage cx s tr))
    (eval_expr cx (Call ty (IntCall (src,fn)) es ann))`
  >- simp[state_rel_frame_result] >>
  simp_tac bool_ss [Once evaluate_def] >>
  CALL_FRAME_STEP >> CALL_FRAME_STEP
  >- simp[]
  >- (irule state_rel_frame_machine >>
      simp[machine_frame_primitives]) >>
  CALL_FRAME_STEP >> CALL_FRAME_STEP >> CALL_FRAME_STEP >>
  rpt gen_tac >> disch_tac >>
  CALL_FRAME_STEP
  >- simp[]
  >- (irule state_rel_frame_machine >> simp[machine_frame_primitives]) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `lift_option_type (get_module_code _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [lift_option_type_INL_eq]) >>
  BETA_TAC >>
  CALL_FRAME_STEP
  >- simp[]
  >- (irule state_rel_frame_machine >> simp[machine_frame_primitives]) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [lift_option_type_INL_eq]) >>
  rename1 `lookup_callable_function _ fn ts = SOME tup` >>
  PairCases_on `tup` >>
  qpat_assum `~cx.in_deploy`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQF_INTRO th])) >>
  simp_tac bool_ss [LET_THM, FST, SND] >>
  qpat_assum `!ts mut nr args dflts ret stmts.
    _ ==> state_rel_frame _ (eval_exprs _ _)` drule_all >> strip_tac >>
  qpat_assum `!ts mut nr args dflts ret stmts.
    _ ==> state_rel_frame _ (eval_stmts _ _)` drule_all >> strip_tac >>
  rpt CALL_FRAME_STEP >>
  qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [push_function_def, vyperStateTheory.return_def, PAIR_EQ, sumTheory.INL_11] >>
  strip_tac >> gvs[]
QED
