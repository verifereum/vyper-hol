Theory staticAbortFrameException
Ancestors
  asmFrameRel asmFrameRun codegenRequestPrefix asmSem symbolResolve
  frameOutcome callTrace vfmExecution vfmExecutionProp vfmDecreasesGas list

Theorem asm_frame_exception_requests:
  !prog data es s n ast reqs.
    asm_frame_prog_ok prog /\
    asm_frame_rel prog data es s es /\
    (asm_steps (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog n s = AsmRevert ast \/
     asm_steps (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog n s = AsmFault ast) /\
    ast.as_requests <<= reqs ==>
    (?r es'. run_call es = SOME (r,es') /\
      (frame_resource_starved es r es' \/
       ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs)) /\
    call_requests es <<= reqs
Proof
  rpt gen_tac >> strip_tac >>
  (reverse conj_tac
   >- (`call_requests es <<= ast.as_requests` by
         metis_tac[asm_frame_run_requests] >>
       metis_tac[isPREFIX_TRANS]) >>
   Cases_on `run_call es` >- fs[run_call_eq_tr] >>
   rename1 `run_call es = SOME res` >> PairCases_on `res` >>
   qexistsl_tac [`res0`, `res1`] >> simp[] >>
   qspecl_then [`n`, `prog`, `data`, `es`, `s`, `es`, `res0`, `res1`]
     mp_tac asm_frame_run >>
   simp[] >> metis_tac[])
QED
