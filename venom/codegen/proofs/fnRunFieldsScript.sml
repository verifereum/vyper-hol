(*
 * State fields a function run never changes, for the IntRet clause of
 * fnEntryStep$fn_entry_block_step (fn_return_state_rel).
 *
 * TOP-LEVEL:
 *   run_blocks_intret_fields - an IntRet run keeps the call, tx and block
 *                              context, code and prev hashes
 *)

Theory fnRunFields
Ancestors
  venomExecSemantics venomState venomInst venomInstProps

(* No instruction changes these fields: the non-terminators by
   venomInstProps' step_preserves_* (INVOKE included), and the terminators
   only move control, halt, or return. *)
Theorem run_blocks_intret_fields:
  !fuel ctx fn vs ret vs'.
    run_blocks fuel ctx fn vs = IntRet ret vs' ==>
    vs'.vs_call_ctx = vs.vs_call_ctx /\ vs'.vs_tx_ctx = vs.vs_tx_ctx /\
    vs'.vs_block_ctx = vs.vs_block_ctx /\ vs'.vs_code = vs.vs_code /\
    vs'.vs_prev_hashes = vs.vs_prev_hashes
Proof
  cheat
QED
