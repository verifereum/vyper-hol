(*
 * DFT's step contract at walk run 7, from the plain step contract
 * (o1DftStep) and row 8 of its output (dft_step_row).
 *)
Theory o1DftStepAt
Ancestors
  o1DftStep o1PassContract venomPassSchedule

(* dft_fn keeps every opcode and puts each block's pseudo-instructions
   first, so it keeps no-ALLOCA and gives the pseudo prefix of row 8. *)
Theorem dft_step_row:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 7 fn ==>
  o1_fn_row 8 out.fpo_function
Proof
  cheat
QED

Theorem dft_step_contract_at:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT)
Proof
  simp[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  `o1_fn_row 8 out.fpo_function` by metis_tac[dft_step_row] >>
  assume_tac dft_step_contract >>
  fs[o1_step_contract_def] >> metis_tac[]
QED
