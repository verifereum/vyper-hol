(*
 * The assembly run against the EVM frame that runs its bytecode, for
 * codegenAsmRunCall.
 *
 * The frame starts at es0 and runs the code assemble prog ++ data, which
 * is assemble (prog ++ [AsmDataItem data]); the assembly runs prog alone.
 *
 * TOP-LEVEL:
 *   asm_frame_prog_ok     - the program facts the frame simulation needs
 *   asm_frame_rel         - assembly state as against EVM state es of the
 *                           frame that started at es0
 *   asm_frame_step_ok     - one assembly step against the rest of the frame
 *   asm_frame_rel_entry   - entry_asm_state starts the relation
 *   frame_outcome_mid     - a frame outcome taken from mid-frame is the
 *                           frame's outcome
 *   frame_resource_starved_mid - likewise for starvation
 *)

Theory asmFrameRel
Ancestors
  codegenEntryRel asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  frameOutcome callTrace vfmExecution vfmExecutionProp

(* Well-formed instruction encodings, with data confined to the suffix. *)
Definition asm_frame_prog_ok_def:
  asm_frame_prog_ok prog <=>
    asm_encoding_wf prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog))
End

(* es is the frame es0 part way through: the same depth, saved rollback,
   outer contexts, message and txParams; its head context is as by
   asm_evm_rel over the frame's whole code; and the call outcomes and GAS
   readings the assembly has left are the ones the rest of es's run
   observes, while its requests so far and the rest's make es0's. *)
Definition asm_frame_rel_def:
  asm_frame_rel prog data es0 as es <=>
    ?c0 c rb rest.
      es0.contexts = (c0, rb) :: rest /\ es.contexts = (c, rb) :: rest /\
      c0.logs = [] /\ c.msgParams = c0.msgParams /\ ~c0.msgParams.static /\
      (as.as_call_ctx.cc_created_in_tx =
        account_empty (lookup_account c.msgParams.callee es.originalAccounts)) /\
      (~as.as_call_ctx.cc_created_in_tx ==>
        account_already_created (lookup_account c.msgParams.callee
          es.rollback.accounts)) /\
      es.txParams = es0.txParams /\ wf_state es /\
      (?d. es.msdomain = Collect d) /\
      asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
      as.as_outcomes = MAP SND (call_trace es) /\
      as.as_gas_readings = gas_readings es /\
      as.as_requests ++ call_requests es = call_requests es0
End

(* The step of prog at as.as_pc: either the frame starves from es, or the
   frame's run from es ends as the step does (codegen_asm_run_call's
   clauses), or the step continues and the relation holds again at a
   state the frame's run passes through. *)
Definition asm_frame_step_ok_def:
  asm_frame_step_ok prog data es0 as es <=>
    (?r es'. run_call es = SOME (r, es') /\ frame_resource_starved es0 r es') \/
    case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                  (EL as.as_pc prog) as of
      AsmOK as1 =>
        ?es1. run_call es1 = run_call es /\ asm_frame_rel prog data es0 as1 es1
    | AsmHalt as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          frame_outcome es0 r es' NONE as1.as_returndata as1.as_logs /\
          es'.rollback.accounts = as1.as_accounts /\
          es'.rollback.toDelete = as1.as_pending_deletions /\
          es'.rollback.tStorage = as1.as_transient /\
          as1.as_requests = call_requests es0
    | AsmRevert as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          ?lgs. frame_outcome es0 r es' (SOME Reverted) as1.as_returndata lgs
    | AsmFault as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          ?exc lgs. exc <> Reverted /\ frame_outcome es0 r es' (SOME exc) [] lgs
    | AsmError _ => T
End

(* frame_outcome reads only the head's logs and message, the saved
   rollback, the outer contexts and txParams of its start state. *)
Theorem frame_outcome_mid:
  es0.contexts = (c0, rb) :: rest /\ es.contexts = (c, rb) :: rest /\
  c0.logs = [] /\ c.msgParams = c0.msgParams /\ es.txParams = es0.txParams /\
  frame_outcome es r es' exc out lgs ==>
  frame_outcome es0 r es' exc out (c.logs ++ lgs)
Proof
  rw[frame_outcome_def] >> gvs[] >>
  Cases_on `rest` >> gvs[] >>
  rename1 `(_, _) :: rest'` >> PairCases_on `h` >> gvs[] >>
  metis_tac[]
QED

Theorem frame_resource_starved_mid:
  es0.contexts = (c0, rb) :: rest /\ es.contexts = (c, rb) :: rest /\
  c0.logs = [] /\ c.msgParams = c0.msgParams /\ es.txParams = es0.txParams /\
  frame_resource_starved es r es' ==>
  frame_resource_starved es0 r es'
Proof
  rw[frame_resource_starved_def] >> metis_tac[frame_outcome_mid]
QED

(* The frame starts in the relation with its own entry assembly state. *)
Theorem asm_frame_rel_entry:
  initial_ctx_rel cplan prog ctx vs es /\
  (vs.vs_call_ctx.cc_created_in_tx = account_empty
    (lookup_account (FST (HD es.contexts)).msgParams.callee es.originalAccounts)) /\
  (vs.vs_call_ctx.cc_created_in_tx \/ account_already_created
    (lookup_account (FST (HD es.contexts)).msgParams.callee
      es.rollback.accounts)) ==>
  asm_frame_rel prog vs.vs_data_section es (entry_asm_state vs es) es
Proof
  rw[initial_ctx_rel_def, initial_state_rel_def, asm_frame_rel_def,
     asm_evm_rel_def, entry_asm_state_def, msg_ctx_rel_def, tx_ctx_rel_def,
     block_ctx_rel_def, blockhash_rel_def, data_suffix_assemble] >>
  gvs[asm_pc_to_offset_def, CONJ_ASSOC]
QED
