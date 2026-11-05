(*
 * DFT's stage facts at run 7 from its function relation: under row 7
 * (wf_ssa, no ALLOCA, pseudo-instructions first) every function of C' is
 * a DFT schedule of its function in C (dft_fn_rel), and the schedule is
 * SSA.
 *)
Theory o1DftStageSsa
Ancestors
  dftContractGas dftAbortOrder dftRunRel dftScheduleOrder
  o1PassContract venomPassSchedule venomWf list

Theorem dft_stage_fn_rel:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==>
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions
Proof
  strip_tac >> drule ctx_pass_stage_dft >> strip_tac >> simp[] >>
  `LIST_REL dft_fallible_order_kept C.ctx_functions C'.ctx_functions` by
    (gvs[LIST_REL_EL_EQN, o1_ctx_shape_def, EVERY_EL, o1_fn_shape_def,
         o1_pre_def, o1_fn_row_def] >>
     rpt strip_tac >> gvs[] >> irule dft_fn_fallible_order_kept >>
     metis_tac[]) >>
  irule dft_fn_rel_stage >> simp[EVERY_MEM] >>
  gvs[o1_pre_def, o1_fn_row_def, EVERY_MEM] >> rw[] >> metis_tac[]
QED

Theorem dft_stage_wf_ssa:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==>
  EVERY wf_ssa C'.ctx_functions
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  irule dft_out_wf_ssa >> metis_tac[]
QED
