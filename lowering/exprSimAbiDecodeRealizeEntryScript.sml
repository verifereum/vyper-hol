Theory exprSimAbiDecodeRealizeEntry
Ancestors
  exprSimAbiDecodeRealizeFunctionBoundary exprSimAbiDecodeRealizeTarget
  compileEnv exprLoweringProps venomState vyperState vyperContext
  vyperTypeInitialState vyperInterpreter exprSimAbiDecodeRealizeSource
  exprSimAbiDecodeRealizeFunction fcgDefs venomInst venomMemDefs relation list

Definition abi_decode_realize_entry_ce_def:
  abi_decode_realize_entry_ce (ce:compile_env) =
    (abi_decode_realize_ce ce) with
      <|ce_vars := FEMPTY; ce_module_vars := FEMPTY;
        ce_is_ctor := F; ce_imm_alloca := NONE|>
End

Definition abi_decode_realize_entry_state_def:
  abi_decode_realize_entry_state entry = (init_venom_state entry) with
    <|vs_block_ctx := empty_block_context with bc_number := 1w;
      vs_prev_hashes := [0w]|>
End

Theorem abi_decode_realize_entry_call_ctx:
  call_ctx_rel abi_decode_realize_txn
    (abi_decode_realize_entry_state entry).vs_call_ctx
    (abi_decode_realize_entry_state entry).vs_tx_ctx
    (abi_decode_realize_entry_state entry).vs_block_ctx
Proof
  simp[call_ctx_rel_def, abi_decode_realize_entry_state_def,
       init_venom_state_def, empty_call_context_def, empty_tx_context_def,
       empty_block_context_def, abi_decode_realize_txn_def,
       empty_call_txn_def, tx_env_ok_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem abi_decode_realize_entry_state_rel:
  state_rel func (abi_decode_realize_entry_ce ce)
    (abi_decode_realize_live_cx k) abi_decode_realize_state
    (abi_decode_realize_entry_state entry)
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def,
       storage_rel_def, transient_rel_def, accounts_rel_def,
       accounts_agree_def, transient_agree_def, storage_agree_def,
       immutables_rel_def, logs_rel_def, storage_vars_rel_def, transient_vars_rel_def,
       vyperContextTheory.get_module_code_def,
       abi_decode_realize_tops_def, vyperStateTheory.find_var_decl_by_name_def,
       call_ctx_rel_def, empty_tx_context_def, empty_block_context_def,
       tx_env_ok_def,
       abi_decode_realize_entry_ce_def, abi_decode_realize_ce_def,
       abi_decode_realize_state_def, initial_state_def, initial_machine_state_def,
       abi_decode_realize_entry_state_def, init_venom_state_def,
       abi_decode_realize_live_cx_def, abi_decode_realize_cx_def,
       empty_evaluation_context_def, abi_decode_realize_txn_def,
       empty_call_txn_def, empty_call_context_def,
       vfmStateTheory.lookup_account_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def]
QED

Theorem abi_decode_realize_entry_no_edge:
  ~fn_directly_calls (abi_decode_realize_context ce k entry) a b
Proof
  simp[fn_directly_calls_def, abi_decode_realize_context_def,
       mk_venom_context_def, venomInstTheory.lookup_function_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  drule abi_decode_realize_function_no_dynamic_or_invoke >> simp[]
QED

Theorem abi_decode_realize_entry_no_reach:
  ~TC (fn_directly_calls (abi_decode_realize_context ce k entry)) a b
Proof
  simp[Once TC_CASES1, abi_decode_realize_entry_no_edge]
QED

Theorem abi_decode_realize_entry_stmt:
  stmt_state_rel (abi_decode_realize_context (abi_decode_realize_entry_ce ce) k entry)
    (abi_decode_realize_function (abi_decode_realize_entry_ce ce) k entry)
    (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx k)
    abi_decode_realize_state (abi_decode_realize_entry_state entry)
Proof
  simp[stmt_state_rel_def, abi_decode_realize_entry_state_rel,
       alloca_room_def, fmp_room_def, abi_decode_realize_function_lookup,
       abi_decode_realize_entry_no_reach, abi_decode_realize_function_pending_empty,
       abi_decode_realize_entry_state_def, init_venom_state_def,
       alloca_inv_def, immutable_alloca_sep_def, immutable_base_zero_def,
       abi_decode_realize_entry_ce_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256,
       allocas_non_overlapping_def, alloca_next_valid_def, EVERY_MEM] >>
  rpt strip_tac >> drule abi_decode_realize_function_no_dynamic_or_invoke >> simp[]
QED

Theorem abi_decode_realize_entry_package:
  ?vv sb s0.
    compile_expr (abi_decode_realize_entry_ce ce)
      (expr_type (abi_decode_realize_expr k)) (abi_decode_realize_expr k)
      (initial_compile_state entry) = (vv,sb) /\
    fn_has_code (initial_compile_state entry) sb
      (abi_decode_realize_function (abi_decode_realize_entry_ce ce) k entry) /\
    fn_inst_ids_distinct
      (abi_decode_realize_function (abi_decode_realize_entry_ce ce) k entry) /\
    local_ptrs_reserved (abi_decode_realize_entry_ce ce) (initial_compile_state entry) /\
    gas_admissible (eval_expr (abi_decode_realize_live_cx k) (abi_decode_realize_expr k))
      expr_vv_res_ok abi_decode_realize_state /\
    stmt_state_rel
      (abi_decode_realize_context (abi_decode_realize_entry_ce ce) k entry)
      (abi_decode_realize_function (abi_decode_realize_entry_ce ce) k entry)
      (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx k)
      abi_decode_realize_state s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = (initial_compile_state entry).cs_current_bb /\
    s0.vs_inst_idx = LENGTH (initial_compile_state entry).cs_current_insts
Proof
  qexistsl_tac [`FST (compile_expr (abi_decode_realize_entry_ce ce)
    (expr_type (abi_decode_realize_expr k)) (abi_decode_realize_expr k)
    (initial_compile_state entry))`,
    `abi_decode_realize_final (abi_decode_realize_entry_ce ce) k entry`,
    `abi_decode_realize_entry_state entry`] >>
  simp[abi_decode_realize_final_def, abi_decode_realize_function_has_code,
       abi_decode_realize_function_ids, abi_decode_realize_live_admissible,
       abi_decode_realize_entry_stmt, local_ptrs_reserved_def,
       abi_decode_realize_entry_ce_def, abi_decode_realize_entry_state_def,
       init_venom_state_def, vyperCompilerTheory.initial_compile_state_def]
QED
