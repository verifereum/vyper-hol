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

Theorem exec_block_return_fields[local]:
  !fuel ctx bb s t.
    (exec_block fuel ctx bb s = OK t \/
     (?ret. exec_block fuel ctx bb s = IntRet ret t)) ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
    t.vs_prev_hashes = s.vs_prev_hashes
Proof
  rpt gen_tac >>
  map_every qid_spec_tac [`t`, `s`] >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >> gen_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >- (rename1 `step_inst fuel ctx inst s = OK u` >>
      drule step_inst_ok_fields >> strip_tac >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
      simp[] >> disch_tac >>
      first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
      (impl_tac >- (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac)) >>
      disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[] >> disch_then drule >> simp[]) >>
  rename1 `step_inst fuel ctx inst s = IntRet ret u` >>
  strip_tac >> gvs[] >> drule step_inst_intret_fields >> simp[]
QED

Theorem run_block_return_fields[local]:
  !fuel ctx bb s t.
    (run_block fuel ctx bb s = OK t \/
     (?ret. run_block fuel ctx bb s = IntRet ret t)) ==>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
    t.vs_prev_hashes = s.vs_prev_hashes
Proof
  rpt gen_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  simp[run_block_def] >> disch_tac >>
  drule exec_block_return_fields >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
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
  Induct_on `fuel`
  >- simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  rpt gen_tac >>
  once_rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `lookup_block vs.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `run_block fuel ctx bb vs` >> simp[]
  >- (rename1 `run_block fuel ctx bb vs = OK u` >>
      Cases_on `u.vs_halted` >> simp[] >> disch_tac >>
      `u.vs_call_ctx = vs.vs_call_ctx /\ u.vs_tx_ctx = vs.vs_tx_ctx /\
       u.vs_block_ctx = vs.vs_block_ctx /\ u.vs_code = vs.vs_code /\
       u.vs_prev_hashes = vs.vs_prev_hashes` by
        (irule run_block_return_fields >> metis_tac[]) >>
      first_x_assum drule >> simp[]) >>
  strip_tac >> gvs[] >>
  irule run_block_return_fields >> metis_tac[]
QED
