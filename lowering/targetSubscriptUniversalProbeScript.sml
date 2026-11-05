Theory targetSubscriptUniversalProbe
Ancestors
  targetSubscriptProbe words vyperStorage vyperStorageBackend vyperState
  vyperInterpreter vyperContext vyperValue vfmState
  venomExecSemantics venomState venomInst calleeTransport
Libs
  pairLib

Theorem clear_call_symbolic:
  !es.
    eval_expr probe_clear_source_context
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE) es =
    (INL (Value (IntV 0)),
     set_storage probe_clear_source_context es F
       (update_storage 0w 0w (get_storage probe_clear_source_context es F)))
Proof
  gen_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``get_storage_backend``,
    ``set_storage_backend``, ``lookup_storage``]) >>
  simp[get_storage_backend_eq, get_storage_scopes] >>
  simp[set_storage_backend_eq, handle_function_def, return_def,
       set_storage_def, evaluation_state_component_equality] >>
  simp[get_storage_def] >> EVAL_TAC
QED

Theorem clear_root_symbolic[local]:
  !es. eval_base_place probe_clear_source_context
    (TopLevelNameTarget (NONE,"outer")) es =
    (INL (PlaceR (StoragePlace F 0w
      (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
        (Dynamic 1)) (Dynamic 1)))), es)
Proof
  gen_tac >> EVAL_TAC >>
  simp[dimword_def, type_slot_size_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem clear_base_symbolic:
  !es.
    eval_base_place probe_clear_source_context probe_clear_source_bt es =
    if lookup_storage 0w (get_storage probe_clear_source_context es F) = 0w
    then (INR (Error (RuntimeError "array dynamic length oob")), es)
    else
      let es' = set_storage probe_clear_source_context es F
        (update_storage 0w 0w (get_storage probe_clear_source_context es F)) in
      if lookup_storage 1w (get_storage probe_clear_source_context es F) = 0w
      then (INR (Error (RuntimeError "array dynamic length oob")), es')
      else (INL (PlaceR (StoragePlace F 2w
        (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))), es')
Proof
  gen_tac >> simp[probe_clear_source_bt_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, clear_root_symbolic] >>
  simp[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def,
       return_def, bind_def, read_result_def] >>
  simp[targetSubscriptSimTheory.extend_place_storage_array_index,
       wordsTheory.w2n_eq_0, clear_call_symbolic,
       read_result_def, return_def] >>
  Cases_on `lookup_storage 0w (get_storage probe_clear_source_context es F) = 0w` >>
  gvs[GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0] >>
  simp[targetSubscriptSimTheory.extend_place_storage_array_index,
       GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0,
       get_storage_after_set] >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM,
       wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `get_storage probe_clear_source_context es F 1w = 0w` >> simp[]
QED

Theorem clear_machine_setup:
  !ss. ?cs. setup_callee probe_descendant_function [] ss = SOME cs
Proof
  simp[setup_callee_def, probe_descendant_function_def, mk_raw_function_def]
QED

Theorem clear_machine_invoke_raw:
  !fuel k ss id out cs.
    setup_callee probe_descendant_function [] ss = SOME cs ==>
    step_inst (SUC fuel) (probe_descendant_ctx k)
      (mk_inst id INVOKE [Label "internal 0 shrink()_runtime"] [out]) ss =
    OK (update_var out 0w
      (merge_callee_state ss
        ((sstore 2w 0w (sstore 0w 0w (cs with vs_inst_idx := 0)))
          with vs_inst_idx := 2)))
Proof
  rpt strip_tac >> irule probe_descendant_invoke >>
  simp[probe_descendant_ctx_lookups]
QED

Theorem clear_machine_merge:
  !ss cs.
    setup_callee probe_descendant_function [] ss = SOME cs ==>
    merge_callee_state ss
      ((sstore 2w 0w (sstore 0w 0w (cs with vs_inst_idx := 0)))
        with vs_inst_idx := 2) =
    sstore 2w 0w (sstore 0w 0w ss)
Proof
  rpt strip_tac >>
  gvs[setup_callee_def, probe_descendant_function_def, mk_raw_function_def] >>
  simp[merge_callee_state_def, sstore_def, venom_state_component_equality]
QED

Theorem clear_machine_invoke:
  !fuel k ss id out.
    step_inst (SUC fuel) (probe_descendant_ctx k)
      (mk_inst id INVOKE [Label "internal 0 shrink()_runtime"] [out]) ss =
    OK (update_var out 0w (sstore 2w 0w (sstore 0w 0w ss)))
Proof
  rpt gen_tac >>
  qspec_then `ss` strip_assume_tac clear_machine_setup >>
  drule clear_machine_invoke_raw >>
  drule clear_machine_merge >> simp[]
QED

Theorem clear_machine_frames:
  !ss out.
    let t = update_var out 0w (sstore 2w 0w (sstore 0w 0w ss)) in
    (!v. lookup_var v t = if v = out then SOME 0w else lookup_var v ss) /\
    t.vs_allocas = ss.vs_allocas /\
    t.vs_alloca_next = ss.vs_alloca_next /\
    t.vs_memory = ss.vs_memory /\
    t.vs_transient = ss.vs_transient /\
    t.vs_call_ctx = ss.vs_call_ctx /\
    t.vs_tx_ctx = ss.vs_tx_ctx /\
    t.vs_block_ctx = ss.vs_block_ctx /\
    t.vs_current_bb = ss.vs_current_bb /\
    t.vs_prev_bb = ss.vs_prev_bb /\
    t.vs_inst_idx = ss.vs_inst_idx /\
    t.vs_fmp = ss.vs_fmp /\
    t.vs_call_entry_fmp = ss.vs_call_entry_fmp /\
    t.vs_return_pc_token = ss.vs_return_pc_token /\
    contract_storage t = contract_storage (sstore 2w 0w (sstore 0w 0w ss))
Proof
  simp[update_var_def, lookup_var_def, sstore_def, contract_storage_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED
