Theory bodyPtrPopFullFrameRuntime
Ancestors
  bodyPtrPopFullFrameProbe compileEnv exprLoweringProps vyperContext
  bodyPtrPopFullFrameSource accountsRelProps venomState vyperState vyperStorageBackend
  compileVyper vyperValue

(* Positive domain probe for the repaired control transaction; no runtime
   relation witness or target execution is asserted here. *)
Theorem pop_full_frame_transaction_domain:
  tx_env_ok pop_full_frame_cx.txn
Proof
  EVAL_TAC
QED

(* Name the concrete machine frame so relation certificates can use projections
   without expanding the whole supported compilation context. *)
Definition pop_full_frame_ss_def:
  pop_full_frame_ss =
    (init_venom_state "internal 0 take()_runtime") with
      <| vs_accounts := pop_full_frame_es.accounts;
         vs_transient := pop_full_frame_es.tStorage;
         vs_block_ctx := empty_block_context with bc_number := 1w;
         vs_inst_idx := 2;
         vs_vars := FEMPTY |+ ("%5",0w) |+ ("%6",0w);
         vs_allocas := FEMPTY |+ (9,(0,32));
         vs_alloca_next := 32 |>
End

Theorem pop_full_frame_call_context:
  call_ctx_rel pop_full_frame_cx.txn pop_full_frame_ss.vs_call_ctx
    pop_full_frame_ss.vs_tx_ctx pop_full_frame_ss.vs_block_ctx
Proof
  EVAL_TAC >> gen_tac >> Cases_on `n = 0` >> simp[]
QED

Theorem pop_full_frame_accounts_rel:
  accounts_rel pop_full_frame_cx pop_full_frame_es pop_full_frame_ss
Proof
  simp[accounts_rel_def, pop_full_frame_ss_def]
QED

Theorem pop_full_frame_storage_rel:
  storage_rel pop_full_frame_cx pop_full_frame_cx.txn.target
    pop_full_frame_es pop_full_frame_ss
Proof
  simp[storage_rel_def, pop_full_frame_ss_def, contract_storage_def,
       init_venom_state_def, empty_call_context_def, pop_full_frame_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

Theorem pop_full_frame_transient_rel:
  transient_rel pop_full_frame_cx pop_full_frame_cx.txn.target
    pop_full_frame_es pop_full_frame_ss
Proof
  simp[transient_rel_def, pop_full_frame_ss_def, contract_transient_def,
       init_venom_state_def, empty_call_context_def, pop_full_frame_cx_def,
       empty_evaluation_context_def, empty_call_txn_def]
QED

Theorem pop_full_frame_local_ptrs_rel:
  local_ptrs_rel pop_full_frame_fn pop_full_frame_body_env
    pop_full_frame_es.scopes pop_full_frame_ss
Proof
  simp[local_ptrs_rel_def, pop_full_frame_vars, local_region_def]
QED

Theorem pop_full_frame_immutables_rel:
  immutables_rel pop_full_frame_body_env pop_full_frame_cx.txn.target
    pop_full_frame_body_env.ce_module pop_full_frame_body_env.ce_is_ctor
    pop_full_frame_es pop_full_frame_ss
Proof
  simp[immutables_rel_def, pop_full_frame_es_def, set_storage_def,
       vyperStateTheory.empty_state_def]
QED

Theorem pop_full_frame_logs_rel:
  logs_rel pop_full_frame_body_env pop_full_frame_cx.txn.target
    pop_full_frame_es pop_full_frame_ss
Proof
  EVAL_TAC
QED

Theorem pop_full_frame_module_vars:
  pop_full_frame_body_env.ce_module_vars =
    FEMPTY |+ ((NONE,"a"), StorageLoc 0w)
Proof
  simp[pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_def, allocate_args_def,
       allocate_internal_special_vars_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> EVAL_TAC
QED

Theorem pop_full_frame_storage_vars_rel:
  storage_vars_rel pop_full_frame_body_env pop_full_frame_cx
Proof
  simp[storage_vars_rel_def, pop_full_frame_module_vars,
       pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_def, allocate_args_def,
       allocate_internal_special_vars_def] >>
  rpt (pairarg_tac >> simp[]) >>
  EVAL_TAC >> rpt strip_tac >>
  Cases_on `name = "a"` >> gvs[find_var_decl_by_name_def] >> EVAL_TAC
QED

Theorem pop_full_frame_transient_vars_rel:
  transient_vars_rel pop_full_frame_body_env pop_full_frame_cx
Proof
  simp[transient_vars_rel_def, pop_full_frame_module_vars,
       pop_full_frame_body_env_def, pop_full_frame_cenv_def,
       build_compile_env_def, allocate_args_def,
       allocate_internal_special_vars_def] >>
  rpt (pairarg_tac >> simp[]) >>
  EVAL_TAC >> rpt strip_tac >>
  Cases_on `name = "a"` >> gvs[find_var_decl_by_name_def, var_decl_transient_def]
QED

Theorem pop_full_frame_state_rel:
  state_rel pop_full_frame_fn pop_full_frame_body_env pop_full_frame_cx
    pop_full_frame_es pop_full_frame_ss
Proof
  simp[state_rel_def, pop_full_frame_local_ptrs_rel,
       pop_full_frame_storage_rel, pop_full_frame_storage_vars_rel,
       pop_full_frame_transient_rel, pop_full_frame_transient_vars_rel,
       pop_full_frame_accounts_rel, pop_full_frame_immutables_rel,
       pop_full_frame_logs_rel, pop_full_frame_call_context] >>
  EVAL_TAC
QED

Theorem pop_full_frame_alloca_inv:
  alloca_inv pop_full_frame_ss
Proof
  EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_no_direct_calls:
  ~fn_directly_calls pop_full_frame_context "internal 0 take()_runtime" g
Proof
  simp[fcgDefsTheory.fn_directly_calls_def, pop_full_frame_fn_lookup,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       pop_full_frame_blocks, venomInstTheory.mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem pop_full_frame_no_calls:
  ~TC (fn_directly_calls pop_full_frame_context)
    "internal 0 take()_runtime" g
Proof
  strip_tac >> drule relationTheory.TC_CASES1_E >>
  simp[pop_full_frame_no_direct_calls]
QED

Theorem pop_full_frame_fn_name:
  pop_full_frame_fn.fn_name = "internal 0 take()_runtime"
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_full_frame_alloca_room:
  alloca_room pop_full_frame_context pop_full_frame_fn pop_full_frame_ss
Proof
  simp_tac bool_ss [alloca_room_def, pop_full_frame_fn_name,
                    pop_full_frame_fn_lookup, pop_full_frame_no_calls] >>
  simp[] >>
  rewrite_tac[pending_alloca_size_def,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       pop_full_frame_blocks] >>
  EVAL_TAC
QED

Theorem pop_full_frame_fmp_room:
  fmp_room pop_full_frame_context pop_full_frame_fn pop_full_frame_ss
Proof
  simp[fmp_room_def, pop_full_frame_fn_name, pop_full_frame_no_calls,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       pop_full_frame_blocks, venomInstTheory.mk_inst_def]
QED

Theorem pop_full_frame_stmt_state_rel:
  stmt_state_rel pop_full_frame_context pop_full_frame_fn
    pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es pop_full_frame_ss
Proof
  simp[stmt_state_rel_def, pop_full_frame_state_rel,
       pop_full_frame_alloca_inv, pop_full_frame_alloca_room,
       pop_full_frame_fmp_room, immutable_alloca_sep_def,
       immutable_base_zero_def, pop_full_frame_specials,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       pop_full_frame_blocks, venomInstTheory.mk_inst_def,
       pop_full_frame_ss_def, init_venom_state_def] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED
