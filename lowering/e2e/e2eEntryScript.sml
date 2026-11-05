(* Shared concrete entry state (PLAN 5.10).
 * Helpers expose field GROUPS: fresh machine, concrete frame environment,
 * source transaction environment, and selected first-function frame.
 * Imported stage owners supply definitions only, never S1-S7 proof facts.
 *)
Theory e2eEntry
Ancestors
  e2eDefs vyperLoweringCorrect codegenCorrectness
  venomState unitTransformDefs unitShapeDefs contextPlanLayoutProps
  contextCodegenRel compileEnv symbolResolve finite_map words vyperArith
  immutableSectionRel

Definition entry_venom_state_def:
  entry_venom_state prog cp es =
    let mp = (FST (HD es.contexts)).msgParams in
    let tp = es.txParams in
      init_venom_state "" with <|
        vs_accounts := es.rollback.accounts;
        vs_transient := es.rollback.tStorage;
        vs_call_ctx := <| cc_caller := mp.caller; cc_address := mp.callee;
                          cc_callvalue := n2w mp.value; cc_calldata := buffer_to_list mp.data;
                          cc_gas := 0; cc_static := mp.static |>;
        vs_tx_ctx := <| tc_origin := tp.origin; tc_gasprice := n2w tp.gasPrice;
                       tc_chainid := n2w tp.chainId;
                       tc_blobhashes := tp.blobHashes |>;
        vs_block_ctx := <| bc_coinbase := tp.blockCoinBase;
                          bc_timestamp := n2w tp.blockTimeStamp;
                          bc_number := n2w tp.blockNumber;
                          bc_prevrandao := tp.prevRandao;
                          bc_gaslimit := n2w tp.blockGasLimit;
                          bc_basefee := n2w tp.baseFeePerGas;
                          bc_blobbasefee := n2w tp.baseFeePerBlobGas;
                          bc_blockhash :=
                            (\n. let idx = tp.blockNumber - n - 1 in
                                 if n < tp.blockNumber /\ tp.blockNumber - 256 <= n /\
                                    idx < LENGTH tp.prevHashes
                                 then EL idx tp.prevHashes else 0w) |>;
        vs_prev_hashes := tp.prevHashes;
        vs_code := mp.code;
        vs_data_section := DROP (LENGTH (assemble prog)) mp.code;
        vs_labels := n2w o_f SND (compute_label_offsets prog);
        vs_fmp := n2w cp.cp_initial_fmp;
        vs_call_entry_fmp := n2w cp.cp_initial_fmp;
        vs_initial_fmp := n2w cp.cp_initial_fmp;
        vs_outcomes := MAP SND (call_trace es);
        vs_gas_readings := gas_readings es;
        vs_requests := [];
        vs_pending_deletions := es.rollback.toDelete |>
End

(* Fresh fields inherited from init_venom_state; FMP fields are permanent. *)
Theorem entry_venom_state_fresh:
  !prog cp es.
  o1_initial_state_ok (entry_venom_state prog cp es) /\
  (entry_venom_state prog cp es).vs_vars = FEMPTY /\
  ~(entry_venom_state prog cp es).vs_halted /\
  (entry_venom_state prog cp es).vs_memory = [] /\
  (entry_venom_state prog cp es).vs_allocas = FEMPTY /\
  (entry_venom_state prog cp es).vs_alloca_next = 0 /\
  initial_codegen_state_rel cp (entry_venom_state prog cp es) /\
  (entry_venom_state prog cp es).vs_logs = [] /\
  (entry_venom_state prog cp es).vs_returndata = [] /\
  (entry_venom_state prog cp es).vs_inst_idx = 0
Proof
  cheat
QED

(* Live frame state, not the saved per-context rollback snapshot. *)
Theorem entry_venom_state_frame_fields:
  !prog cp es.
  (entry_venom_state prog cp es).vs_accounts = es.rollback.accounts /\
  (entry_venom_state prog cp es).vs_transient = es.rollback.tStorage /\
  (entry_venom_state prog cp es).vs_pending_deletions = es.rollback.toDelete /\
  (entry_venom_state prog cp es).vs_code =
    (FST (HD es.contexts)).msgParams.code /\
  (entry_venom_state prog cp es).vs_data_section =
    DROP (LENGTH (assemble prog)) (FST (HD es.contexts)).msgParams.code /\
  (entry_venom_state prog cp es).vs_outcomes = MAP SND (call_trace es) /\
  (entry_venom_state prog cp es).vs_gas_readings = gas_readings es /\
  (entry_venom_state prog cp es).vs_requests = [] /\
  (entry_venom_state prog cp es).vs_pending_deletions = es.rollback.toDelete /\
  (!l. FLOOKUP (entry_venom_state prog cp es).vs_labels l =
       OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l))
Proof
  cheat
QED

(* Keep the actual installed padding; values are related by decoding it. *)
Theorem entry_venom_state_installed_section:
  !tops prog am tx es cp.
  call_state_rel tops (assemble prog) am tx es ==>
  immutables_section_rel tops (account_immutables am tx.target)
    (entry_venom_state prog cp es).vs_data_section /\
  (entry_venom_state prog cp es).vs_code = assemble prog ++
    (entry_venom_state prog cp es).vs_data_section
Proof
  cheat
QED

Theorem entry_venom_state_evm_environment:
  !es ctxt rb rest prog cp.
  es.contexts = (ctxt, rb) :: rest /\
  es.txParams.blockNumber < dimword (:256) ==>
  msg_ctx_rel (entry_venom_state prog cp es).vs_call_ctx ctxt.msgParams /\
  tx_ctx_rel (entry_venom_state prog cp es).vs_tx_ctx es.txParams /\
  block_ctx_rel (entry_venom_state prog cp es).vs_block_ctx es.txParams /\
  blockhash_rel (entry_venom_state prog cp es) es.txParams
Proof
  cheat
QED

(* The source boundary supplies the actual block-number bound, not a new
   top-level premise. Its MIN256 history condition is retained by tx_env_ok. *)
Theorem call_state_rel_block_number_bound:
  call_state_rel tops runtime_bc am tx es ==>
  es.txParams.blockNumber < dimword (:256)
Proof
  cheat
QED

Theorem entry_venom_state_source_environment:
  !tops prog am tx es cp.
  call_state_rel tops (assemble prog) am tx es ==>
  venom_env_rel tx (entry_venom_state prog cp es)
Proof
  cheat
QED

(* Exact initial_state_rel sub-contract. No memory obligation is inferred:
   both fresh memories are empty and the byte relation is reflexive. *)
Theorem entry_venom_state_first_frame:
  !tops prog am tx es fn cp.
  call_state_rel tops (assemble prog) am tx es /\
  get_params (HD fn.fn_blocks).bb_instructions = [] ==>
  initial_state_rel cp prog 0 fn (entry_venom_state prog cp es) es
Proof
  cheat
QED
