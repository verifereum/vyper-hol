(*
 * DFT's step contract at walk run 7: row 7 makes the function SSA with
 * its pseudo-instructions first, which the shape part (o1DftStep's
 * dft_step_contract_ssa) needs, and dft_fn gives row 8 (dft_step_row).
 *)
Theory o1DftStepAt
Ancestors
  o1DftStep o1PassContract venomPassSchedule dftCorrectnessFinal
  venomFnScheduleRunnerProps dftSsaPreserve dftScheduleOrder list

(* dft_fn reschedules within blocks, keeping each use after its
   definition, so it keeps SSA. *)
Theorem dft_fn_wf_ssa:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==> wf_ssa (dft_fn fn)
Proof
  strip_tac >>
  `dft_fn fn = fn with fn_blocks := (dft_fn fn).fn_blocks` by
    (rewrite_tac[dftDefsTheory.dft_fn_def, LET_THM] >>
     CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  irule dftSsaPreserveTheory.dft_block_rel_wf_ssa >> simp[] >>
  metis_tac[dftScheduleOrderTheory.dft_fn_block_rel]
QED

(* dft_fn keeps every opcode, so row 7 gives row 8 (no ALLOCA), and like
   every pass but FmpLowering it keeps the FMP convention. *)
Theorem dft_step_row:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 7 fn ==>
  o1_fn_row 8 out.fpo_function
Proof
  strip_tac >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >>
     gvs[o1_fn_row_def, fn_pass_tag_def]) >>
  fs[fn_pass_step_def] >> gvs[] >>
  `MEM fn observed.cu_context.ctx_functions` by
    metis_tac[lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  gvs[o1_fn_row_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all dft_shape_instruction_source >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[flip_operands_not_alloca]
QED

Theorem dft_step_contract_at:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT)
Proof
  simp[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  `o1_fn_row 8 out.fpo_function` by metis_tac[dft_step_row] >>
  `wf_ssa fn /\ fn_pseudos_prefix fn` by gvs[o1_fn_row_def] >>
  drule_all dft_step_contract_ssa >> simp[]
QED
