(*
 * The entry relations of whole-context codegen correctness: how the
 * Venom state at a context's entry corresponds to the EVM frame that runs
 * the generated code, and the assembly state that frame starts in.
 * codegenCorrectness re-exports each definition under its own name.
 *
 * TOP-LEVEL:
 *   initial_ctx_rel   - the Venom/EVM entry relation of codegen_correct
 *   entry_asm_state   - the assembly state the generated code starts in
 *)

Theory codegenEntryRel
Ancestors
  asmToBytecodeProps codegen vfmExecution
  codegenRel asmSem asmWf stackPlanGen stackPlanTypes planExec
  symbolResolve venomExecSemantics venomState venomInst contextCodegenRel
  list rich_list finite_map arithmetic
  frameOutcome callTrace unitShapeDefs vfmExecutionProp

(* Call context correspondence: Venom call context matches EVM message params *)
Definition msg_ctx_rel_def:
  msg_ctx_rel cc mp ⇔
    cc.cc_caller = mp.caller ∧
    cc.cc_address = mp.callee ∧
    cc.cc_callvalue = n2w mp.value ∧
    cc.cc_calldata = buffer_to_list mp.data ∧
    cc.cc_static = mp.static
End

(* Tx context correspondence: Venom tx context matches EVM tx parameters *)
Definition tx_ctx_rel_def:
  tx_ctx_rel tc tp ⇔
    tc.tc_origin = tp.origin ∧
    tc.tc_gasprice = n2w tp.gasPrice ∧
    tc.tc_chainid = n2w tp.chainId ∧
    tc.tc_blobhashes = tp.blobHashes
End

(* Block context correspondence: Venom block context matches EVM block parameters *)
Definition block_ctx_rel_def:
  block_ctx_rel bc tp ⇔
    bc.bc_coinbase = tp.blockCoinBase ∧
    bc.bc_timestamp = n2w tp.blockTimeStamp ∧
    bc.bc_number = n2w tp.blockNumber ∧
    bc.bc_prevrandao = tp.prevRandao ∧
    bc.bc_gaslimit = n2w tp.blockGasLimit ∧
    bc.bc_basefee = n2w tp.baseFeePerGas ∧
    bc.bc_blobbasefee = n2w tp.baseFeePerBlobGas
End

(* Blockhash correspondence: Venom blockhash lookup matches EVM prevHashes.
   Requires blockNumber < dimword(:256) for well-formed n2w conversion. *)
Definition blockhash_rel_def:
  blockhash_rel vs tp ⇔
    vs.vs_prev_hashes = tp.prevHashes ∧
    tp.blockNumber < dimword (:256) ∧
    ∀n. vs.vs_block_ctx.bc_blockhash n =
      let bn = w2n vs.vs_block_ctx.bc_number in
      let idx = bn - n - 1 in
      if n < bn ∧ bn − 256 ≤ n ∧
         idx < LENGTH vs.vs_prev_hashes
      then EL idx vs.vs_prev_hashes
      else 0w
End

(* Stack parameter correspondence: function PARAM variables match EVM stack.
   First param deepest, last param TOS. *)
Definition stack_params_rel_def:
  stack_params_rel fn vs stack ⇔
    let params = get_params (HD fn.fn_blocks).bb_instructions in
    LENGTH params = LENGTH stack ∧
    ∀i. i < LENGTH params ⇒
      FLOOKUP vs.vs_vars (HD (EL i params).inst_outputs) =
        SOME (EL i (REVERSE stack))
End

(* At a selected function-region entry, Venom and EVM states agree on
   shared fields.  [off] is an assembly-instruction index; the EVM PC is
   the corresponding byte offset in [prog]. *)
Definition initial_state_rel_def:
  initial_state_rel cp prog off fn vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         stack_params_rel fn vs ctxt.stack ∧
         (* Live accounts and transient storage *)
         es.rollback.accounts = vs.vs_accounts ∧
         es.rollback.tStorage = vs.vs_transient ∧
         es.rollback.toDelete = vs.vs_pending_deletions ∧
         vs.vs_call_ctx.cc_created_in_tx =
           account_empty (lookup_account ctxt.msgParams.callee es.originalAccounts) ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         (* Equality is required only outside every context spill region. *)
         context_memory_rel cp vs.vs_memory (buffer_to_list ctxt.memory) ∧
         (* Translate the selected instruction index to an EVM byte PC. *)
         ctxt.pc = asm_pc_to_offset prog off ∧
         ctxt.jumpDest = NONE ∧
         (* Venom state: not halted, at instruction 0 *)
         vs.vs_halted = F ∧
         vs.vs_inst_idx = 0 ∧
         msg_ctx_rel vs.vs_call_ctx ctxt.msgParams ∧
         tx_ctx_rel vs.vs_tx_ctx es.txParams ∧
         block_ctx_rel vs.vs_block_ctx es.txParams ∧
         blockhash_rel vs es.txParams ∧
         vs.vs_code = ctxt.msgParams.code ∧
         (∀a. ctxt.msgParams.outputTo ≠ Code a)
     | [] => F)
End

(* Moved from e2eDefs without changing the permanent FMP/token contract. *)
Definition initial_codegen_state_rel_def:
  initial_codegen_state_rel cp vs <=>
    vs.vs_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_call_entry_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_return_pc_token = 0w
End

(* First function, fresh non-static frame, live state, exact deployed code,
   concrete labels, and the outcomes actually traced from our frame's run. *)
Definition initial_ctx_rel_def:
  initial_ctx_rel cp prog ctx vs es <=>
    ?fn fns ctxt rb rest.
      ctx.ctx_functions = fn :: fns /\ es.contexts = (ctxt, rb) :: rest /\
      initial_state_rel cp prog 0 fn vs es /\
      initial_codegen_state_rel cp vs /\
      wf_state es /\ (?d. es.msdomain = Collect d) /\
      ~ctxt.msgParams.static /\
      ctxt.msgParams.code = assemble prog ++ vs.vs_data_section /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code /\
      vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\ ctxt.logs = [] /\
      (!l. FLOOKUP vs.vs_labels l =
           OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
      vs.vs_outcomes = MAP SND (call_trace es) /\ vs.vs_requests = [] /\
      vs.vs_gas_readings = gas_readings es
End

(* The assembly state of the EVM frame es at the entry of the generated
   code, with Venom's view of everything the assembly semantics keeps
   abstractly (contexts, oracle outcomes and GAS readings): the frame's
   stack and memory, PC 0, and the rest from vs, as initial_ctx_rel
   relates them to es. *)
Definition entry_asm_state_def:
  entry_asm_state vs es =
    <| as_stack := (FST (HD es.contexts)).stack;
       as_memory := buffer_to_list (FST (HD es.contexts)).memory;
       as_accounts := vs.vs_accounts;
       as_transient := vs.vs_transient;
       as_returndata := vs.vs_returndata;
       as_logs := vs.vs_logs;
       as_pc := 0;
       as_call_ctx := vs.vs_call_ctx;
       as_tx_ctx := vs.vs_tx_ctx;
       as_block_ctx := vs.vs_block_ctx;
       as_code := vs.vs_code;
       as_prev_hashes := vs.vs_prev_hashes;
       as_outcomes := vs.vs_outcomes;
       as_requests := vs.vs_requests;
       as_pending_deletions := vs.vs_pending_deletions;
       as_gas_readings := vs.vs_gas_readings |>
End
