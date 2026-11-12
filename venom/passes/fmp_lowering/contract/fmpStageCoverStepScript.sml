(*
 * FmpLowering's coverage (fmpStageCoverage): the invariant fmp_cov holds
 * at the context entry and is kept by a step within a block.  A step from
 * a state inside an inserted run moves along the run; a step from a
 * related point uses the step lemmas of fmpStageOpSteps and
 * fmpStageFmpSteps on the source step fmpStageCoverBack gives (first
 * restoring with fmp_stage_restore where the lemma needs restored = T); a
 * step in a revert forwarding's tail stays in it.
 *
 * TOP-LEVEL:
 *   fmp_cov_entry - the target's entry state is covered
 *   fmp_cov_next  - a non-terminator, non-INVOKE target step keeps fmp_cov
 *)
Theory fmpStageCoverStep
Ancestors
  fmpStageCoverInv fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem
  fmpStageBlockSim fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase
  fmpStageControl fmpStageRel ptrDiscipline contextCodegenRel o1PassContract
  passSimulationDefs venomExecSemantics venomState venomInst finite_map
  words list

Theorem fmp_cov_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>) t /\
  active_inst fn' ti t ==>
  fmp_cov D C C' vs vs' fmp eom [] fn' t
Proof
  cheat
QED

Theorem fmp_cov_next:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  cheat
QED
