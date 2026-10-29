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

Theorem machine_frame_external_defaults:
  read_only_context mods cx /\ EVERY (expr_mutability_ok mods View) es ==>
  state_rel_frame machine_frame (eval_external_defaults cx es)
Proof
  strip_tac >> simp[eval_external_defaults_def] >>
  irule machine_frame_bind >> simp[machine_frame_primitives] >>
  gen_tac >> irule state_rel_frame_finally >>
  simp[machine_frame_def, machine_frame_primitives] >>
  simp[ignore_bind_def] >> irule machine_frame_bind >>
  simp[machine_frame_primitives] >>
  irule (cj 6 evaluate_read_only) >> qexists `mods` >> simp[]
QED

Theorem machine_frame_external_action:
  state_rel_frame machine_frame (eval_external_defaults cx es) /\
  state_rel_frame machine_frame (eval_stmts cx body) /\
  (mut = View \/ mut = Pure) ==>
  state_rel_frame machine_frame
    (do send_call_value mut cx;
        dvs <- eval_external_defaults cx es;
        case bind_arguments tenv args (vals ++ dvs) of
        | NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME env => do
            set_scopes [env];
            (if nr then
               case cx.nonreentrant_slot of
               | NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock cx.txn.target slot T
             else return ());
            eval_stmts cx body
          od
     od)
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >> simp[ignore_bind_def] >>
  match_mp_tac machine_frame_bind >> conj_tac
  >- (irule machine_frame_nonpayable_value >> Cases_on `mut` >> gvs[]) >>
  simp[] >> match_mp_tac machine_frame_bind >> conj_tac >- simp[] >>
  qx_gen_tac `dvs` >>
  Cases_on `bind_arguments tenv args (vals ++ dvs)` >>
  simp[machine_frame_primitives] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_primitives] >>
  match_mp_tac machine_frame_bind >>
  simp[machine_frame_internal_lock]
QED

Theorem call_external_function_read_only:
  ~cx.in_deploy /\
  state_rel_frame machine_frame
    (eval_external_defaults cx
      (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts)) /\
  state_rel_frame machine_frame (eval_stmts cx body) /\
  (mut = View \/ mut = Pure) /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INL v, am', rqs) ==>
  am' = am
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def] >>
  IF_CASES_TAC >- simp[] >>
  `LENGTH dflts - (LENGTH args - LENGTH vals) =
   LENGTH dflts + LENGTH vals - LENGTH args` by decide_tac >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `action (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  `state_rel_frame machine_frame action` by
    (simp[Abbr `action`] >> irule machine_frame_external_action >> simp[]) >>
  qpat_x_assum `state_rel_frame machine_frame action`
    (qspec_then `initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>` mp_tac o
     REWRITE_RULE [state_rel_frame_def]) >>
  Cases_on `action (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `read_only_context mods
    (initial_evaluation_context am.sources am.layouts tx
      (find_function_module am tx.target tx.function_name))` by
    (simp[read_only_context_def, initial_evaluation_context_def] >>
     gvs[selected_entry_def] >> metis_tac[]) >>
  `EVERY (expr_mutability_ok mods View) dflts` by
    (drule_all selected_entry_defaults_read_only >> simp[]) >>
  `stmts_mutability_ok mods View body` by
    (irule selected_entry_read_only >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `state_rel_frame machine_frame
    (eval_external_defaults
      (initial_evaluation_context am.sources am.layouts tx
        (find_function_module am tx.target tx.function_name))
      (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts))` by
    (irule machine_frame_external_defaults >> qexists `mods` >>
     simp[rich_listTheory.EVERY_DROP]) >>
  `state_rel_frame machine_frame
    (eval_stmts (initial_evaluation_context am.sources am.layouts tx
      (find_function_module am tx.target tx.function_name)) body)` by
    (irule machine_frame_eval_stmts >> qexists `mods` >> simp[]) >>
  irule call_external_function_read_only >>
  qpat_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (fn th => irule_at Any th) >>
  simp[initial_evaluation_context_def]
QED
