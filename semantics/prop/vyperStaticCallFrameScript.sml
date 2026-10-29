(* Concrete static EVM calls preserve the Vyper machine projection. *)
Theory vyperStaticCallFrame
Ancestors
  vyperInterpreter vfmContext vfmExecution vfmStaticCalls vfmDecreasesGas vfmRunCall

Theorem evm_transfer_zero[simp]:
  vfmExecution$transfer_value caller callee 0 accounts = accounts
Proof
  simp[vfmExecutionTheory.transfer_value_def]
QED

Theorem static_call_initial_rollback:
  (make_ext_call_state caller callee code data NONE gas accounts transient txp).rollback.accounts = accounts /\
  (make_ext_call_state caller callee code data NONE gas accounts transient txp).rollback.tStorage = transient /\
  (make_ext_call_state caller callee code data NONE gas accounts transient txp).rollback.toDelete = []
Proof
  simp[make_ext_call_state_def]
QED

Theorem static_run_call_preserves:
  run_call es = SOME (INR result,final_state) /\
  es.contexts = [(ctxt,rb)] /\ ctxt.msgParams.static /\
  (!a. ctxt.msgParams.outputTo <> Code a) ==>
  final_state.rollback.accounts = es.rollback.accounts /\
  final_state.rollback.tStorage = es.rollback.tStorage /\
  final_state.rollback.toDelete = es.rollback.toDelete /\
  (case final_state.contexts of
     [] => T
   | [(ctxt',rb')] => ctxt'.logs = ctxt.logs
   | _ => T)
Proof
  strip_tac >> drule run_call_inr_imp_run >> strip_tac >>
  drule run_static_preserves >> simp[]
QED

Theorem static_call_setup:
  ?ctxt rb.
    (make_ext_call_state caller callee code data NONE gas accounts transient txp).contexts = [(ctxt,rb)] /\
    ctxt.msgParams.static /\ (!a. ctxt.msgParams.outputTo <> Code a) /\
    ctxt.logs = []
Proof
  simp[make_ext_call_state_def, initial_context_def,
       initial_msg_params_def, empty_return_destination_def]
QED

Theorem extract_static_call_result:
  es.contexts = [(ctxt,rb)] /\ ctxt.msgParams.static /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\ ctxt.logs = [] /\
  es.rollback.accounts = accounts /\ es.rollback.tStorage = transient /\
  run_call es = SOME outcome /\
  extract_call_result accounts transient outcome =
    SOME (ok,ret,accounts',transient',logs',deletions) ==>
  accounts' = accounts /\ transient' = transient /\ logs' = [] /\
  deletions = (if ok then es.rollback.toDelete else [])
Proof
  Cases_on `outcome` >> rename1 `(result,final_state)` >>
  simp[extract_call_result_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule static_run_call_preserves >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem extract_precompile_call_result:
  es.contexts = [(ctxt,rb)] /\ ctxt.logs = [] /\
  es.rollback.accounts = accounts /\ es.rollback.tStorage = transient /\
  dispatch_precompiles addr es = outcome /\
  extract_call_result accounts transient outcome =
    SOME (ok,ret,accounts',transient',logs',deletions) ==>
  accounts' = accounts /\ transient' = transient /\ logs' = [] /\
  deletions = (if ok then es.rollback.toDelete else [])
Proof
  Cases_on `outcome` >> rename1 `(result,final_state)` >> strip_tac >>
  qspec_then `addr` mp_tac
    (GEN_ALL (INST_TYPE [alpha |-> ``:unit``] cp_dispatch_precompiles)) >>
  pure_rewrite_tac[cp_def] >>
  disch_then (qspec_then `es` mp_tac) >> simp[] >>
  disch_then (qspec_then `FST (dispatch_precompiles addr es)` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[extract_call_result_def, AllCaseEqs()]
QED

Theorem run_ext_call_static_frame:
  run_ext_call caller callee data NONE gas accounts transient txp =
    SOME (ok,ret,accounts',transient',logs',deletions) ==>
  accounts' = accounts /\ transient' = transient /\ logs' = [] /\ deletions = []
Proof
  simp[run_ext_call_def, AllCaseEqs()] >> strip_tac >>
  qabbrev_tac `es = make_ext_call_state caller callee
    (lookup_account callee accounts).code data NONE gas accounts transient txp` >>
  `es.rollback.accounts = accounts /\ es.rollback.tStorage = transient /\
   es.rollback.toDelete = []`
    by simp[Abbr `es`, static_call_initial_rollback] >>
  `?ctxt rb. es.contexts = [(ctxt,rb)] /\ ctxt.msgParams.static /\
     (!a. ctxt.msgParams.outputTo <> Code a) /\ ctxt.logs = []`
    by simp[Abbr `es`, static_call_setup] >>
  gvs[] >>
  metis_tac[extract_precompile_call_result, extract_static_call_result]
QED
