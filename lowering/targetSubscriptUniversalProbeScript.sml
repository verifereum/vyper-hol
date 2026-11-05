Theory targetSubscriptUniversalProbe
Ancestors
  targetSubscriptProbe words vyperStorage vyperStorageBackend vyperState
  vyperInterpreter vyperContext vyperValue vfmState
  venomExecSemantics venomState venomInst calleeTransport
  exprSimLeaves exprSimHyps vyperTypeCallGraph compileEnv exprLoweringProps
  venomMemDefs
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

Theorem clear_literal_cases:
  !k.
    expr_sim_case F (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context
      (Literal (BaseT (UintT 256)) (IntL 0)) /\
    expr_vv_case F (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context
      (Literal (BaseT (UintT 256)) (IntL 0))
Proof
  gen_tac >>
  mp_tac compile_literal_case_sim >>
  rewrite_tac[expr_ok_case] >>
  simp[expr_sim_case_def, expr_vv_case_def, int_calls_expr_def] >>
  metis_tac[]
QED

Theorem clear_base_compile_symbolic:
  !sa.
    let vn = \n. "%" ++ num_to_dec_string (sa.cs_next_var + n);
        op = \n. Var (vn n);
        ins = \n opc args outs. mk_inst (sa.cs_next_id + n) opc args (MAP vn outs)
    in
    compile_get_target_ptr compile_expr probe_deep_cenv probe_clear_source_bt sa =
    ((op 19, SOME LocStorage,
      SOME (ValPT (ArrayT (BaseT (UintT 256)) (Dynamic 1)))),
     sa with <| cs_next_var := sa.cs_next_var + 20;
                cs_next_id := sa.cs_next_id + 23;
                cs_current_insts := sa.cs_current_insts ++
       [ins 0 SLOAD [Lit 0w] [0];
        ins 1 LT [Lit 0w; op 0] [1];
        ins 2 ISZERO [op 1] [2];
        ins 3 OR [Lit 0w; op 2] [3];
        ins 4 ISZERO [op 3] [4];
        ins 5 ASSERT [op 4] [];
        ins 6 ADD [Lit 0w; Lit 1w] [5];
        ins 7 MUL [Lit 0w; Lit 3w] [6];
        ins 8 ADD [op 5; op 6] [7];
        ins 9 ALLOCA [Lit 32w] [8];
        ins 10 INVOKE [Label "internal 0 shrink()_runtime"] [9];
        ins 11 ADD [op 8; Lit 0w] [10];
        ins 12 MSTORE [op 10; op 9] [];
        ins 13 MLOAD [op 8] [11];
        ins 14 SLOAD [op 7] [12];
        ins 15 LT [op 11; op 12] [13];
        ins 16 ISZERO [op 13] [14];
        ins 17 OR [Lit 0w; op 14] [15];
        ins 18 ISZERO [op 15] [16];
        ins 19 ASSERT [op 16] [];
        ins 20 ADD [op 7; Lit 1w] [17];
        ins 21 MUL [op 11; Lit 2w] [18];
        ins 22 ADD [op 17; op 18] [19]] |>)
Proof
  gen_tac >>
  `num_to_dec_string 0 = "0"` by EVAL_TAC >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``num_to_dec_string``]) >>
  simp[arithmeticTheory.ADD_ASSOC] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

Theorem clear_base_compile_shape[local]:
  !sa r sb.
    compile_get_target_ptr compile_expr probe_deep_cenv probe_clear_source_bt sa = (r,sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
    ?tail. LENGTH tail = 22 /\
      sb.cs_current_insts = sa.cs_current_insts ++
        mk_inst sa.cs_next_id SLOAD [Lit 0w]
          ["%" ++ num_to_dec_string sa.cs_next_var] :: tail
Proof
  rpt gen_tac >>
  qspec_then `sa` mp_tac clear_base_compile_symbolic >>
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (fn th => rewrite_tac[th]) >>
  rpt strip_tac >> gvs[] >> simp[mk_inst_def]
QED

Theorem clear_caller_root_position[local]:
  !n.
    n < LENGTH (HD probe_descendant_outer_caller.fn_blocks).bb_instructions /\
    (EL n (HD probe_descendant_outer_caller.fn_blocks).bb_instructions).inst_opcode = SLOAD /\
    (EL n (HD probe_descendant_outer_caller.fn_blocks).bb_instructions).inst_operands = [Lit 0w] ==>
    n = 0
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``EL``]) >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >>
  CONV_TAC (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV EVAL)) >> simp[]
QED

Theorem clear_caller_lookup[local]:
  !label bb.
    lookup_block label probe_descendant_outer_caller.fn_blocks = SOME bb ==>
    label = "entry" /\ bb = HD probe_descendant_outer_caller.fn_blocks
Proof
  simp[probe_descendant_outer_caller_def, mk_raw_function_def,
       lookup_block_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[]
QED

Theorem clear_base_code_position[local]:
  !sa r sb.
    compile_get_target_ptr compile_expr probe_deep_cenv probe_clear_source_bt sa = (r,sb) /\
    fn_has_code sa sb probe_descendant_outer_caller ==>
    sa.cs_current_bb = "entry" /\ sa.cs_current_insts = []
Proof
  rpt strip_tac >>
  drule clear_base_compile_shape >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
  drule clear_caller_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `LENGTH sa.cs_current_insts <
    LENGTH (HD probe_descendant_outer_caller.fn_blocks).bb_instructions` by
    (qpat_x_assum `(HD _).bb_instructions = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `EL (LENGTH sa.cs_current_insts)
      (HD probe_descendant_outer_caller.fn_blocks).bb_instructions =
    mk_inst sa.cs_next_id SLOAD [Lit 0w]
      ["%" ++ num_to_dec_string sa.cs_next_var]` by
    (qpat_x_assum `(HD _).bb_instructions = _` (fn th => rewrite_tac[th]) >>
     simp[listTheory.EL_APPEND_EQN]) >>
  qspec_then `LENGTH sa.cs_current_insts` mp_tac clear_caller_root_position >>
  simp[mk_inst_def]
QED

Theorem clear_base_code_inversion:
  !sa r sb.
    compile_get_target_ptr compile_expr probe_deep_cenv probe_clear_source_bt sa = (r,sb) /\
    fn_has_code sa sb probe_descendant_outer_caller ==>
    sa.cs_current_bb = "entry" /\ sa.cs_current_insts = [] /\
    sa.cs_next_id = 0 /\ sa.cs_next_var = 0
Proof
  rpt strip_tac >>
  drule_all clear_base_code_position >> strip_tac >>
  drule clear_base_compile_shape >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  pure_rewrite_tac[fragExecTheory.fn_has_code_def] >> strip_tac >>
  drule clear_caller_lookup >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  gvs[] >>
  `HD (HD probe_descendant_outer_caller.fn_blocks).bb_instructions =
     mk_inst sa.cs_next_id SLOAD [Lit 0w]
       ["%" ++ num_to_dec_string sa.cs_next_var]` by
    (qpat_x_assum `_ = (HD _).bb_instructions` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  pop_assum mp_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``num_to_dec_string``]) >>
  simp[]
QED

(* Entry header observations: the child header is live only before clearing. *)
Theorem clear_entry_root_header:
  !k es ss.
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context es ss ==>
    sload 0w ss =
      lookup_storage 0w (get_storage probe_clear_source_context es F)
Proof
  rpt strip_tac >>
  drule targetSubscriptSimTheory.stmt_state_rel_storage_live_head >>
  disch_then (qspecl_then [`F`, `0w`,
    `ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
      (Dynamic 1)) (Dynamic 1)`] mp_tac) >>
  simp[type_slot_size_def] >> disch_then irule >>
  irule accountsRelPropsTheory.declared_storage_region_read_live >>
  qexistsl_tac [`NONE`, `"outer"`, `[]`] >>
  simp[probe_clear_source_declared_region]
QED

Theorem clear_entry_child_not_dead[local]:
  !st b.
    lookup_storage 0w st <> 0w ==>
    ~storage_dead probe_clear_source_context F st 1 b
Proof
  rpt strip_tac >>
  gvs[storage_dead_def, probe_clear_source_declared_region,
      type_slot_size_def, dead_bytes_def, w2n_eq_0] >>
  decide_tac
QED

Theorem clear_entry_child_header:
  !k es ss.
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context es ss /\
    lookup_storage 0w (get_storage probe_clear_source_context es F) <> 0w ==>
    sload 1w ss =
      lookup_storage 1w (get_storage probe_clear_source_context es F)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree
    (storage_dead probe_clear_source_context F
      (get_storage probe_clear_source_context es F))
    (get_storage probe_clear_source_context es F) (contract_storage ss)` by
    gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
        get_storage_def, lookup_account_def] >>
  simp[sload_def] >> sym_tac >>
  irule accountsRelPropsTheory.word_to_bytes_EL_eq >> rpt strip_tac >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def] >>
  disch_then irule >> simp[clear_entry_child_not_dead]
QED

Theorem clear_root_accounts[local]:
  !cx es ss.
    accounts_rel cx es ss /\ ss.vs_call_ctx.cc_address = cx.txn.target ==>
    accounts_rel cx
      (set_storage cx es F (update_storage 0w 0w (get_storage cx es F)))
      (sstore 0w 0w ss)
Proof
  rpt strip_tac >> irule accountsRelPropsTheory.accounts_rel_sstore >>
  simp[] >> qexists_tac `es` >>
  simp[set_storage_backend_eq, get_storage_def, lookup_account_def] >>
  rpt strip_tac >>
  irule accountsRelPropsTheory.storage_dead_update_zero >> simp[]
QED

Theorem clear_root_stmt[local]:
  !k es ss.
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context es ss ==>
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context
      (set_storage probe_clear_source_context es F
        (update_storage 0w 0w (get_storage probe_clear_source_context es F)))
      (sstore 0w 0w ss)
Proof
  rpt strip_tac >>
  `ss.vs_call_ctx.cc_address = probe_clear_source_context.txn.target` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `accounts_rel probe_clear_source_context
    (set_storage probe_clear_source_context es F
      (update_storage 0w 0w (get_storage probe_clear_source_context es F)))
    (sstore 0w 0w ss)` by
    (irule clear_root_accounts >>
     gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  drule accountsRelPropsTheory.accounts_rel_storage_transient >>
  simp[sstore_def] >> strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def, sstore_def,
      local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
      immutables_rel_def, logs_rel_def, alloca_inv_def, alloca_room_def,
      pending_alloca_size_def, immutable_alloca_sep_def, set_storage_def,
      allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem clear_stmt_transport:
  !k es ss.
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context es ss ==>
    stmt_state_rel (probe_descendant_ctx k) probe_descendant_outer_caller
      probe_deep_cenv probe_clear_source_context
      (set_storage probe_clear_source_context es F
        (update_storage 0w 0w (get_storage probe_clear_source_context es F)))
      (sstore 2w 0w (sstore 0w 0w ss))
Proof
  rpt strip_tac >>
  drule clear_root_stmt >> strip_tac >>
  `ss.vs_call_ctx.cc_address = probe_clear_source_context.txn.target` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  irule targetSubscriptSimTheory.stmt_state_rel_sstore_dead_right >>
  simp[sstore_def, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> rpt strip_tac >>
  irule probe_clear_source_dead_descendant >>
  simp[set_storage_def, lookup_account_def,
       lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem clear_root_prefix:
  !ss. run_inst_seq
    (TAKE 9 (HD probe_descendant_outer_caller.fn_blocks).bb_instructions) ss =
    if sload 0w ss = 0w then
      Abort Revert_abort
        (revert_state (set_returndata []
          (update_var "%4" 0w (update_var "%3" 1w
            (update_var "%2" 1w (update_var "%1" 0w
              (update_var "%0" 0w ss)))))))
    else
      OK (update_var "%7" 1w (update_var "%6" 0w
        (update_var "%5" 1w (update_var "%4" 1w
          (update_var "%3" 0w (update_var "%2" 0w
            (update_var "%1" 1w (update_var "%0" (sload 0w ss) ss))))))))
Proof
  gen_tac >> Cases_on `sload 0w ss = 0w` >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``step_inst_base``, ``sload``,
    ``update_var``, ``revert_state``, ``set_returndata``]) >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomStateTheory.eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var, bool_to_word_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var, bool_to_word_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var, bool_to_word_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var] >>
  simp[wordsTheory.WORD_OR_CLAUSES] >>
  simp[GSYM arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0,
       bool_to_word_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def] >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var] >>
  simp[wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES]
QED
