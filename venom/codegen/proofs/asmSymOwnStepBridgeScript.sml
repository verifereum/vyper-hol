(* Fetched own-code steps, conditional on the CODECOPY simulation.
   This separates opcode dispatch from the copy implementation. *)
Theory asmSymOwnStepBridge
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes asmSymOwnStep

Theorem asm_sym_step_own_from_copy:
  (!c t bytes.
     asm_static_wf p /\ asm_sym_rel p env c t /\ bytes = c.as_code ==>
     asm_sym_step_rel p env (sym_codecopy_own p env bytes t)
       (asm_step_op (build_offset_to_pc p) "CODECOPY" c)) ==>
  !cs ss own.
    asm_static_wf p /\ asm_sym_rel p env cs ss /\ cs.as_code = own /\
    cs.as_pc < LENGTH p ==>
    asm_sym_step_rel p env
      (sym_step_own p env own (EL cs.as_pc p) ss)
      (asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
         (EL cs.as_pc p) cs)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all asm_sym_step >> strip_tac >>
  Cases_on `EL cs.as_pc p` >>
  gvs[sym_step_own_def] >>
  rename1 `AsmOp name` >>
  Cases_on `name = "CODECOPY"`
  >- (gvs[sym_step_op_own_def, asm_step_def] >>
      first_x_assum irule >> simp[]) >>
  Cases_on `name = "CODESIZE"`
  >- (gvs[] >>
      `asm_sym_rel_own (SND (compute_label_offsets p)) p env cs.as_code cs ss`
        by simp[asm_sym_rel_own_canonical] >>
      mp_tac (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
        `own` |-> `cs.as_code`, `otp` |-> `build_offset_to_pc p`]
        sym_codesize_own_sim) >>
      simp[] >> strip_tac >>
      gvs[sym_step_own_def, sym_step_op_own_def, asm_step_def,
          asm_sym_step_rel_def, asm_sym_rel_own_canonical]) >>
  gvs[sym_step_op_own_def, sym_step_def]
QED
