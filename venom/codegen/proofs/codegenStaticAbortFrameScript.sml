(* Assembly exceptions compose with the actual EVM frame run and its requests.
   This boundary is independent of the source static-abort simulation. *)
Theory codegenStaticAbortFrame
Ancestors
  codegenEntryRel codegenAsmProgOk asmFrameRel asmFrameRun
  codegenRequestPrefix asmSem asmWf symbolResolve frameOutcome callTrace
  vfmExecution vfmExecutionProp vfmDecreasesGas

Theorem codegen_static_abort_frame:
  !rpolicy unit cp prog vs es n ast reqs.
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    initial_ctx_rel cp prog unit.cu_context vs es /\
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n (entry_asm_state vs es) = AsmRevert ast \/
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n (entry_asm_state vs es) = AsmFault ast) /\
    ast.as_requests = reqs ==>
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= reqs
Proof
  rpt gen_tac >> strip_tac >> (
  drule_all codegen_assembly_frame_prog_ok >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  (Q.SUBGOAL_THEN `vs.vs_call_ctx.cc_created_in_tx \/ account_already_created
     (lookup_account (FST (HD es.contexts)).msgParams.callee
       es.rollback.accounts)` assume_tac
   >- (gvs[initial_ctx_rel_def] >> metis_tac[])) >>
  drule_all asm_frame_rel_entry >> strip_tac >>
  reverse conj_tac
  >- metis_tac[asm_frame_run_requests] >>
  Cases_on `run_call es` >- fs[run_call_eq_tr] >>
  rename1 `run_call es = SOME res` >> PairCases_on `res` >>
  qexistsl_tac [`res0`, `res1`] >> simp[] >>
  qspecl_then [`n`, `prog`, `vs.vs_data_section`, `es`, `entry_asm_state vs es`,
               `es`, `res0`, `res1`] mp_tac asm_frame_run >>
  simp[] >> metis_tac[])
QED
