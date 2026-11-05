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
  opcodeClass venomInstProofs1 venomExecProofs

Theorem step_inst_ok_fields[local]:
  !fuel ctx inst s t.
    step_inst fuel ctx inst s = OK t ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
    t.vs_prev_hashes = s.vs_prev_hashes
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >>
      gvs[is_terminator_def] >>
      gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs(),
          jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  metis_tac[venomInstPropsTheory.step_preserves_call_ctx,
            venomInstPropsTheory.step_preserves_tx_ctx,
            venomInstPropsTheory.step_preserves_block_ctx,
            venomInstPropsTheory.step_preserves_code,
            venomInstPropsTheory.step_preserves_prev_hashes]
QED

Theorem step_inst_intret_fields[local]:
  !fuel ctx inst s ret t.
    step_inst fuel ctx inst s = IntRet ret t ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
    t.vs_prev_hashes = s.vs_prev_hashes
Proof
  rpt gen_tac >> disch_tac >>
  gvs[step_inst_def, AllCaseEqs()] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_preserves_non_memory >> simp[]
QED

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
