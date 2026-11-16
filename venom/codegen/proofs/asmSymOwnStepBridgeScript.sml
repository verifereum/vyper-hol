(* Fetched own-code steps, conditional on the CODECOPY simulation.
   This separates opcode dispatch from the copy implementation. *)
Theory asmSymOwnStepBridge
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes

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
  >- (gvs[sym_step_op_own_def, asm_step_def] >>
      simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
           asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
           asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
           asm_push_val_def, sym_set_stack_def, asm_sym_step_rel_def] >>
      gvs[asm_sym_rel_def, asm_next_def, sval_conc_def] >>
      conj_tac
      >- (rename1 `LENGTH memory = LENGTH cs.as_memory` >>
          qexists `memory` >> simp[]) >>
      metis_tac[]) >>
  gvs[sym_step_op_own_def, sym_step_def]
QED
