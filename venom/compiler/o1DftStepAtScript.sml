(*
 * DFT's step contract at walk run 7, from the plain step contract
 * (o1DftStep) and row 8 of its output (dft_step_row).
 *)
Theory o1DftStepAt
Ancestors
  o1DftStep o1PassContract venomPassSchedule dftCorrectnessFinal
  venomFnScheduleRunnerProps list

(* dft_fn keeps every opcode and puts each block's pseudo-instructions
   first, so it keeps no-ALLOCA and gives the pseudo prefix of row 8. *)
Theorem dft_step_row:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 7 fn ==>
  o1_fn_row 8 out.fpo_function
Proof
  simp[fn_pass_step_def] >> strip_tac >> gvs[] >>
  `MEM fn observed.cu_context.ctx_functions` by
    metis_tac[lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  gvs[o1_fn_row_def, dft_fn_pseudos_prefix, EVERY_MEM] >>
  rpt strip_tac >> drule_all dft_shape_instruction_source >> strip_tac >>
  gvs[] >> metis_tac[flip_operands_not_alloca]
QED

Theorem dft_step_contract_at:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT)
Proof
  simp[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  `o1_fn_row 8 out.fpo_function` by metis_tac[dft_step_row] >>
  assume_tac dft_step_contract >>
  fs[o1_step_contract_def] >> metis_tac[]
QED
