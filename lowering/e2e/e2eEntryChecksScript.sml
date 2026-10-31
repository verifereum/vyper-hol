(* Focused concrete-entry clients. These are not S1-S7 certificates. *)
Theory e2eEntryChecks
Ancestors
  e2eEntry e2eProducers e2eDefs vyperLoweringCorrect codegenCorrectness
  venomState venomExecSemantics unitShapeDefs unitTransformDefs compileEnv selectorDispatch
  symbolResolve asmSem asmIR asmOracleRegression callTrace extCallOracle
  vfmExecution vfmContext vfmState vfmOperation finite_map finite_set words
Libs
  finite_mapLib wordsLib

val _ = Parse.hide "cp";
val () = computeLib.upd_compset add_finite_map_compset;

(* No empty-oracle specialization: exact arbitrary nonempty outcome suffix. *)
Theorem entry_nonempty_oracle_projection:
  call_trace es = (rq, outcome) :: trace ==>
  (entry_venom_state prog cp es).vs_outcomes = outcome :: MAP SND trace /\
  (entry_venom_state prog cp es).vs_requests = [] /\
  o1_initial_state_ok (entry_venom_state prog cp es)
Proof
  simp[entry_venom_state_frame_fields, entry_venom_state_o1_initial_state_ok]
QED

Theorem entry_live_not_saved_snapshot:
  es.contexts = (ctxt, rb) :: rest /\
  es.rollback.accounts <> rb.accounts /\ es.rollback.tStorage <> rb.tStorage ==>
  (entry_venom_state prog cp es).vs_accounts <> rb.accounts /\
  (entry_venom_state prog cp es).vs_transient <> rb.tStorage
Proof
  simp[entry_venom_state_frame_fields]
QED

(* Concrete distinct LIVE/saved witnesses, including transient storage. *)
Theorem entry_live_snapshot_witness:
  let saved = es.rollback with
        <| accounts := empty_accounts; tStorage := empty_transient_storage |>;
      live = saved with
        <| accounts := update_account 42w
             (empty_account_state with balance := 7) empty_accounts;
           tStorage := (\a k. 5w) |>;
      start = es with <| contexts := [(ctxt, saved)]; rollback := live |>;
      vs = entry_venom_state prog cp start
  in (lookup_account 42w vs.vs_accounts).balance = 7 /\
     vs.vs_transient 42w 0w = 5w /\
     (lookup_account 42w (SND (HD start.contexts)).accounts).balance = 0 /\
     (SND (HD start.contexts)).tStorage 42w 0w = 0w
Proof
  simp[entry_venom_state_frame_fields, lookup_account_def, update_account_def,
       empty_accounts_def, empty_account_state_def,
       empty_transient_storage_def, empty_storage_def]
QED

(* FMP is the plan's permanent initial value, even when nonzero. Labels are
   concrete byte offsets, including a nonempty trailing data-header label. *)
Theorem entry_concrete_code_labels_and_fmp:
  let prog = [AsmOp "STOP"; AsmDataHeader "code_end"];
      cplan = cp with cp_initial_fmp := 96;
      start = es with contexts := [(ctxt with msgParams :=
        ctxt.msgParams with code := [0w; 42w], rb)];
      vs = entry_venom_state prog cplan start
  in vs.vs_code = [0w; 42w] /\ vs.vs_data_section = [42w] /\
     FLOOKUP vs.vs_labels "code_end" = SOME 1w /\
     vs.vs_fmp = 96w /\ vs.vs_call_entry_fmp = 96w /\
     vs.vs_initial_fmp = 96w /\ vs.vs_return_pc_token = 0w
Proof
  simp[entry_venom_state_def, init_venom_state_def] >> EVAL_TAC >>
  simp[FLOOKUP_o_f, FLOOKUP_UPDATE]
QED

(* Both blockhash window edges and history-list bounds matter. *)
Theorem entry_blockhash_window:
  let start = es with txParams := es.txParams with
    <| blockNumber := 258; prevHashes := [11w; 22w] |>;
      vs = entry_venom_state prog cp start
  in vs.vs_prev_hashes = [11w; 22w] /\
     vs.vs_block_ctx.bc_blockhash 257 = 11w /\
     vs.vs_block_ctx.bc_blockhash 256 = 22w /\
     vs.vs_block_ctx.bc_blockhash 255 = 0w /\
     vs.vs_block_ctx.bc_blockhash 1 = 0w /\
     vs.vs_block_ctx.bc_blockhash 258 = 0w /\
     blockhash_rel vs start.txParams
Proof
  simp[entry_venom_state_def, blockhash_rel_def] >> EVAL_TAC
QED

(* The real source boundary's MIN256 condition and es.prevHashes survive. *)
Theorem entry_actual_block_history:
  call_state_rel tops (assemble prog) am tx es ==>
  MIN 256 tx.block_number <=
    LENGTH (entry_venom_state prog cp es).vs_prev_hashes /\
  (entry_venom_state prog cp es).vs_prev_hashes = es.txParams.prevHashes /\
  blockhash_rel (entry_venom_state prog cp es) es.txParams
Proof
  rpt strip_tac >> drule call_state_rel_block_number_bound >> strip_tac >>
  gvs[call_state_rel_def, tx_block_fields_rel_def, tx_env_ok_def] >>
  simp[entry_venom_state_def, blockhash_rel_def, w2n_n2w]
QED

(* Calldata is the frame's actual canonical ABI buffer; no source outcomes
   field is invented. *)
Theorem entry_canonical_abi_buffer:
  es.contexts = (ctxt, rb) :: rest /\
  valid_vyper_call tops tx (buffer_to_list ctxt.msgParams.data) ret ==>
  valid_vyper_call tops tx
    (entry_venom_state prog cp es).vs_call_ctx.cc_calldata ret /\
  (entry_venom_state prog cp es).vs_call_ctx.cc_gas = 0
Proof
  simp[entry_venom_state_def]
QED

(* Actual trace witness at CALL to an ordinary empty account, with all seven
   stack slots present. This tests the observer/projection, not fresh-entry
   stack shape; no Venom GAS reading is added. *)
Definition entry_trace_prog_def:
  entry_trace_prog = [AsmOp "CALL"; AsmOp "STOP"]
End

Definition entry_trace_es_def:
  entry_trace_es =
    let start = make_asm_call_state asm_oracle_initial 0w 100000 0 []
                  (assemble entry_trace_prog) F in
      start with contexts := MAP (\(ctxt, rb).
        (ctxt with stack := [0w; 42w; 1w; 0w; 0w; 0w; 0w], rb)) start.contexts
End

Theorem entry_trace_encoding:
  assemble entry_trace_prog = [0xf1w; 0w] /\
  parse_code 0 FEMPTY [0xf1w; 0w] = FEMPTY |+ (0, Call) |+ (1, Stop)
Proof
  conj_tac >- EVAL_TAC >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def]
QED

val entry_trace_eval_tac =
  simp[entry_trace_es_def, entry_trace_encoding, make_asm_call_state_def,
       asm_oracle_initial_def, empty_call_context_def, make_sub_tx_def,
       initial_context_def, initial_msg_params_def, transfer_value_def,
       step_def, handle_def, get_current_context_def, bind_def, return_def,
       FLOOKUP_UPDATE] >> EVAL_TAC >>
  simp[MEM_fset_REP, fIN_fset_ABS] >> EVAL_TAC;

Theorem entry_trace_step:
  ISL (FST (step entry_trace_es)) /\
  LENGTH (SND (step entry_trace_es)).contexts = 1 /\
  (FST (HD (SND (step entry_trace_es)).contexts)).pc = 1
Proof
  entry_trace_eval_tac
QED

Theorem entry_trace_terminal:
  FST (step (SND (step entry_trace_es))) = INR NONE
Proof
  entry_trace_eval_tac
QED

(* Observer contract for exactly one same-depth CALL followed by termination.
   The actual request/outcome records are not replaced by fabricated lists. *)
Theorem entry_trace_two_step_call:
  step es = (INL (), post) /\ step post = (INR exc, last) /\
  LENGTH es.contexts = LENGTH post.contexts /\
  next_opcode (FST (HD es.contexts)) = SOME Call /\
  7 <= LENGTH (FST (HD es.contexts)).stack /\
  ~computed_precompile (request_of es) ==>
  call_trace es =
    [(request_of es, outcome_of post (LENGTH (FST (HD es.contexts)).logs))]
Proof
  rpt strip_tac >>
  simp[call_trace_def, full_call_trace_def, frame_obs_def] >>
  simp[Once frame_obs_tr_def, observe_def, observable_call_def] >>
  simp[Once frame_obs_tr_def, observe_def]
QED

Theorem entry_actual_nonempty_trace:
  call_trace entry_trace_es <> []
Proof
  mp_tac entry_trace_step >> mp_tac entry_trace_terminal >>
  Cases_on `step entry_trace_es` >>
  rename1 `step entry_trace_es = (first_result, post_state)` >>
  Cases_on `first_result` >> gvs[] >> rpt strip_tac >>
  Cases_on `step post_state` >>
  rename1 `step post_state = (last_result, last_state)` >> gvs[] >>
  `call_trace entry_trace_es =
    [(request_of entry_trace_es,
      outcome_of post_state (LENGTH (FST (HD entry_trace_es.contexts)).logs))]` by
    (irule entry_trace_two_step_call >> simp[] >>
     simp[entry_trace_es_def, make_asm_call_state_def, next_opcode_def,
          entry_trace_encoding, initial_context_def, initial_msg_params_def,
          request_of_def, computed_precompile_def, FLOOKUP_UPDATE] >> EVAL_TAC) >>
  gvs[]
QED

Theorem entry_actual_nonempty_outcomes:
  (entry_venom_state entry_trace_prog cp entry_trace_es).vs_outcomes <> [] /\
  (entry_venom_state entry_trace_prog cp entry_trace_es).vs_requests = []
Proof
  simp[entry_venom_state_frame_fields, entry_actual_nonempty_trace]
QED
