(* Read-only external entry wrapper, before pending-deletion finalization. *)
Theory vyperReadOnlyExternal
Ancestors
  vyperReadOnlyEval vyperTypeSelectedEntry vyperReadOnlyBranches
  vyperMachineFrame vyperCallOutcomeFrame vyperState vyperInterpreter vyperAST
  vyperReadOnlySyntax vyperContext
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

Theorem machine_frame_external_body:
  state_rel_frame machine_frame (eval_stmts cx body) /\
  (mut = View \/ mut = Pure) ==>
  state_rel_frame machine_frame
    (do
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot T
        else return ());
       send_call_value mut cx;
       eval_stmts cx body
     od)
Proof
  strip_tac >> simp[ignore_bind_def] >>
  irule state_rel_frame_bind_guarded >> simp[machine_frame_def, machine_frame_internal_lock] >>
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[machine_frame_def] >>
  irule machine_frame_nonpayable_value >> Cases_on `mut` >> gvs[]
QED

Theorem call_external_function_read_only:
  ~cx.in_deploy /\
  state_rel_frame machine_frame (eval_stmts cx body) /\
  (mut = View \/ mut = Pure) /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INL v, am', rqs) ==>
  am' = am
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  `state_rel_frame machine_frame
    (do (if nr then
           case cx.nonreentrant_slot of
           | NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock cx.txn.target slot T
         else return ());
        send_call_value mut cx; eval_stmts cx body od)` by
    (irule machine_frame_external_body >> simp[]) >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts)` >>
  simp[] >> rename1 `SOME dvs` >>
  Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ dvs)` >>
  simp[] >> rename1 `SOME env` >>
  qmatch_goalsub_abbrev_tac `action (initial_state am [env] with <|outcomes := orc; requests := []|>)` >>
  qpat_x_assum `state_rel_frame machine_frame action`
    (qspec_then `initial_state am [env] with <|outcomes := orc; requests := []|>` mp_tac o
     REWRITE_RULE [state_rel_frame_def]) >>
  Cases_on `action (initial_state am [env] with <|outcomes := orc; requests := []|>)` >>
  simp[] >> strip_tac >> rename1 `machine_frame _ st` >>
  `abstract_machine_from_state am.sources am.exports am.layouts st = am` by
    (irule machine_frame_reconstruct >>
     gvs[machine_frame_def, initial_state_def]) >>
  Cases_on `q` >- simp[return_def] >>
  rename1 `action _ = (INR ex,st)` >> Cases_on `ex` >> simp[return_def] >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >> simp[] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  qmatch_goalsub_abbrev_tac `safe_cast tv rv` >> Cases_on `safe_cast tv rv` >> simp[]
QED

Theorem selected_entry_external_function_frame:
  check_contract F am.layouts tx.target mods = SOME art /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  (mut = View \/ mut = Pure) /\
  call_external_function orc am
    (initial_evaluation_context am.sources am.layouts tx
      (find_function_module am tx.target tx.function_name))
    nr mut ts mods args dflts vals body ret = (INL v, am', rqs) ==>
  am' = am
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  irule call_external_function_read_only >>
  goal_assum (drule_at Any) >> simp[initial_evaluation_context_def] >>
  irule machine_frame_eval_stmts >> qexists `mods` >> conj_tac
  >- (simp[read_only_context_def, initial_evaluation_context_def] >>
      gvs[selected_entry_def] >> metis_tac[]) >>
  irule selected_entry_read_only >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
