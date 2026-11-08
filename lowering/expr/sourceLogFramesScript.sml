(* TOP-LEVEL: concrete log appends preserve the source/native state relation.
   Source evaluation first completes the arguments, then appends the encoded
   event. The final composition applies to effectful argument evaluations too. *)
Theory sourceLogFrames
Ancestors
  sourceMemoryFrames sourceValueFrames allocationGrowth typedCopyStateFrame
  abiStateFrame abiFieldOperands compileEnv valueEncoding
  vyperInterpreter vyperState vyperTypeInvariants vyperContext vyperEvent
  fragBlockPath venomExecSemantics venomState list words

Theorem logs_rel_eq:
  !cenv addr es ss. logs_rel cenv addr es ss <=> es.logs = ss.vs_logs
Proof
  rpt gen_tac >> `log_entry_equiv cenv addr = $=` by simp[FUN_EQ_THM, log_entry_equiv_def] >>
  simp[logs_rel_def] >> eq_tac >> strip_tac >> gvs[]
QED

Theorem vars_rel_log_update[simp]:
  !cenv scopes ss logs.
    vars_rel cenv scopes (ss with vs_logs := logs) = vars_rel cenv scopes ss
Proof
  simp[vars_rel_def]
QED

Theorem local_ptrs_rel_log_update[simp]:
  !func cenv scopes ss logs.
    local_ptrs_rel func cenv scopes (ss with vs_logs := logs) = local_ptrs_rel func cenv scopes ss
Proof
  simp[local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def]
QED

Theorem eval_operand_log_update[simp]:
  !arg ss logs. eval_operand arg (ss with vs_logs := logs) = eval_operand arg ss
Proof
  Cases_on `arg` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem state_rel_simple_logs_append:
  !cenv cx es ss events. state_rel_simple cenv cx es ss ==>
    state_rel_simple cenv cx (es with logs := es.logs ++ events) (ss with vs_logs := ss.vs_logs ++ events)
Proof
  simp[state_rel_simple_def, logs_rel_eq, storage_rel_def, transient_rel_def, immutables_rel_simple_def,
    contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> simp[]
QED

Theorem state_rel_simple_log_frame:
  !cenv cx es before after events.
    state_rel_simple cenv cx es before /\ vars_rel cenv es.scopes after /\
    abi_state_frame before (after with vs_logs := before.vs_logs) /\
    after.vs_logs = before.vs_logs ++ events ==>
    state_rel_simple cenv cx (es with logs := es.logs ++ events) after
Proof
  rpt gen_tac >> strip_tac >>
  `state_rel_simple cenv cx es (after with vs_logs := before.vs_logs)` by
    (mp_tac (Q.SPECL [`cenv`, `cx`, `es`, `before`, `after with vs_logs := before.vs_logs`]
       state_rel_simple_external_vars_frame) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]) >>
  `after with vs_logs := before.vs_logs ++ events = after` by simp[venom_state_component_equality] >>
  mp_tac (Q.SPECL [`cenv`, `cx`, `es`, `after with vs_logs := before.vs_logs`, `events`]
    state_rel_simple_logs_append) >> simp[]
QED

Theorem source_relations_log_memory_frame:
  !func cenv cx es before after events bound.
    state_rel_simple cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    copy_state_frame before (after with vs_logs := before.vs_logs) /\
    after.vs_memory = before.vs_memory /\ after.vs_logs = before.vs_logs ++ events /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg. abi_operand_before bound arg ==> eval_operand arg after = eval_operand arg before) ==>
    state_rel_simple cenv cx (es with logs := es.logs ++ events) after /\
    local_ptrs_rel func cenv (es with logs := es.logs ++ events).scopes after
Proof
  rpt gen_tac >> strip_tac >> drule_all copy_state_frame_external >> DISCH_TAC >>
  drule_all allocation_growth_copy_frame >> DISCH_TAC >>
  mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `before`, `after with vs_logs := before.vs_logs`, `bound`]
    source_relations_memory_frame) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> strip_tac >>
  `after with vs_logs := before.vs_logs ++ events = after` by simp[venom_state_component_equality] >>
  conj_tac >- (mp_tac (Q.SPECL [`cenv`, `cx`, `es`, `after with vs_logs := before.vs_logs`, `events`]
    state_rel_simple_logs_append) >> simp[]) >>
  fs[]
QED

Theorem state_rel_simple_call_address:
  !cenv cx es ss. state_rel_simple cenv cx es ss ==> ss.vs_call_ctx.cc_address = cx.txn.target
Proof
  simp[state_rel_simple_def, call_ctx_rel_def] >> rpt strip_tac >> simp[]
QED

Theorem source_log_context:
  !env cenv cx es ss. env_consistent env cx es /\ state_rel_simple cenv cx es ss ==>
    env.type_defs = get_tenv cx /\ ss.vs_call_ctx.cc_address = cx.txn.target
Proof
  rpt gen_tac >> strip_tac >> drule_all state_rel_simple_call_address >> DISCH_TAC >>
  fs[env_consistent_def, env_context_consistent_def]
QED

Theorem eval_log_arguments:
  !cx event_id exprs es values es1 ev.
    ~cx.txn.is_static /\
    eval_exprs cx exprs es = (INL values,es1) /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev ==>
    eval_stmt cx (Log event_id exprs) es = (INL (),es1 with logs := es1.logs ++ [ev])
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, lift_option_def, push_log_def,
       return_def]
QED

Theorem eval_log_arguments_exception:
  !cx event_id exprs es exn es1. eval_exprs cx exprs es = (INR exn,es1) ==>
    eval_stmt cx (Log event_id exprs) es = (INR exn,es1)
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem log_statement_execution:
  !cx cenv ctx func event_id exprs es es1 values ev before middle after.
    ~cx.txn.is_static /\
    eval_exprs cx exprs es = (INL values,es1) /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
    fragment_path ctx func before middle /\ fragment_path ctx func middle after /\
    state_rel_simple cenv cx es1 middle /\ vars_rel cenv es1.scopes after /\
    abi_state_frame middle (after with vs_logs := middle.vs_logs) /\
    after.vs_logs = middle.vs_logs ++ [ev] ==>
    eval_stmt cx (Log event_id exprs) es = (INL (),es1 with logs := es1.logs ++ [ev]) /\
    fragment_path ctx func before after /\ state_rel_simple cenv cx (es1 with logs := es1.logs ++ [ev]) after
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (drule_all eval_log_arguments >> simp[])
  >- (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  drule_all state_rel_simple_log_frame >> simp[]
QED
