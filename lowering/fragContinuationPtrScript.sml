(* Direct non-Error continuations at block entry exclude PHI prefixes. *)
Theory fragContinuationPtr
Ancestors fragExec venomExecSemantics venomInst venomState

Theorem run_from_nonerror_no_phi:
  !fuel ctx fn s bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    ~s.vs_halted /\ s.vs_inst_idx = 0 /\
    (!e. run_from fuel ctx fn s <> Error e) ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bb.bb_instructions` >- simp[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >-
    (qpat_x_assum `!e. run_from fuel ctx fn s <> Error e`
       (qspec_then `"phi outside prefix"` mp_tac) >>
     simp[run_from_def, Once exec_block_def, get_instruction_def,
          step_inst_non_invoke, Once step_inst_base_def]) >>
  simp[phi_prefix_length_def]
QED
