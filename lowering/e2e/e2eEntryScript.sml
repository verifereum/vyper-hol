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
                          cc_callvalue := n2w mp.value; cc_calldata := mp.data;
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
        vs_requests := [] |>
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
  simp[entry_venom_state_def, init_venom_state_def,
       o1_initial_state_ok_def, initial_codegen_state_rel_def]
QED

(* Live frame state, not the saved per-context rollback snapshot. *)
Theorem entry_venom_state_frame_fields:
  !prog cp es.
  (entry_venom_state prog cp es).vs_accounts = es.rollback.accounts /\
  (entry_venom_state prog cp es).vs_transient = es.rollback.tStorage /\
  (entry_venom_state prog cp es).vs_code =
    (FST (HD es.contexts)).msgParams.code /\
  (entry_venom_state prog cp es).vs_data_section =
    DROP (LENGTH (assemble prog)) (FST (HD es.contexts)).msgParams.code /\
  (entry_venom_state prog cp es).vs_outcomes = MAP SND (call_trace es) /\
  (entry_venom_state prog cp es).vs_requests = [] /\
  (!l. FLOOKUP (entry_venom_state prog cp es).vs_labels l =
       OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l))
Proof
  simp[entry_venom_state_def, FLOOKUP_o_f] >> rpt gen_tac >>
  Cases_on `FLOOKUP (SND (compute_label_offsets prog)) l` >> simp[]
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
  rw[call_state_rel_def, entry_venom_state_def] >>
  drule installed_code_rel_section >> simp[]
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
  simp[entry_venom_state_def, msg_ctx_rel_def, tx_ctx_rel_def,
       block_ctx_rel_def, blockhash_rel_def, w2n_n2w]
QED

(* The source boundary supplies the actual block-number bound, not a new
   top-level premise. Its MIN256 history condition is retained by tx_env_ok. *)
Theorem call_state_rel_block_number_bound:
  call_state_rel tops runtime_bc am tx es ==>
  es.txParams.blockNumber < dimword (:256)
Proof
  rw[call_state_rel_def, tx_block_fields_rel_def, tx_env_ok_def] >>
  irule lt_dimword_256 >> qexists_tac `255` >> simp[]
QED

Theorem entry_venom_state_source_environment:
  !tops prog am tx es cp.
  call_state_rel tops (assemble prog) am tx es ==>
  venom_env_rel tx (entry_venom_state prog cp es)
Proof
  rw[call_state_rel_def, tx_block_fields_rel_def] >>
  simp[venom_env_rel_def, call_ctx_rel_def, entry_venom_state_def]
QED

(* Exact initial_state_rel sub-contract. No memory obligation is inferred:
   both fresh memories are empty and the byte relation is reflexive. *)
Theorem entry_venom_state_first_frame:
  !tops prog am tx es fn cp.
  call_state_rel tops (assemble prog) am tx es /\
  get_params (HD fn.fn_blocks).bb_instructions = [] ==>
  initial_state_rel cp prog 0 fn (entry_venom_state prog cp es) es
Proof
  rpt strip_tac >>
  drule call_state_rel_block_number_bound >> strip_tac >>
  qpat_x_assum `call_state_rel _ _ _ _ _` mp_tac >>
  simp[call_state_rel_def] >> strip_tac >>
  drule_all entry_venom_state_evm_environment >> strip_tac >>
  gvs[initial_state_rel_def, stack_params_rel_def,
      entry_venom_state_fresh, entry_venom_state_frame_fields,
      asm_pc_to_offset_zero, context_memory_rel_def]
QED
