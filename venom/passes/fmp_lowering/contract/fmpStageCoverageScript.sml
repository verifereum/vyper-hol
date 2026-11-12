(*
 * FmpLowering's lowered memory phase: every reachable instruction of the
 * lowered context C', run from the real state, accesses memory below the
 * static layout's end eom or at or above the real initial fmp.  Static
 * accesses of the raw input are unchanged; its dynamic ones lie in a live
 * DALLOCA site (row 3's access_ok) and are relocated to at or above the
 * real initial fmp; the inserted instructions access no memory.
 *
 * The proof is backward, by rule induction on the target's small-step
 * frame_reachable (concretize's ptr_raw_reachable_frame reaches it from
 * raw_reachable).  Every target state is covered (fmp_cov): it runs only
 * inserted instructions before a state related to a reachable source
 * point, or it sits in a revert forwarding's tail.  The step lemmas of
 * fmpStageOpSteps, fmpStageFmpSteps and fmpStageBlockSim move the source
 * point; fmpStageCoverBack gives them the terminating source step they
 * assume; fmpStageCoverMem gives each covered state its memory fact.
 *
 * TOP-LEVEL:
 *   fmp_cov                        - the coverage invariant
 *   fmp_stage_coverage             - every target frame state is covered
 *   fmp_lowering_stage_lowered_mem
 *)
Theory fmpStageCoverage
Ancestors
  fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem fmpStageBlockSim fmpStageFmpSteps
  fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  concretizePtrCoverageStaticMemReachability unitMemInv ptrDiscipline
  contextCodegenRel o1PassContract venomPassSchedule venomCompilerTypes
  passSimulationDefs venomExecSemantics venomState venomInst
  finite_map words list

(* The target's call stack mirrors the source's: each saved target frame
   is the state ts saved at the matching source call, in the lowered
   caller, at its INVOKE. *)
Definition fmp_cov_stack_def:
  (fmp_cov_stack C' [] [] [] <=> T) /\
  (fmp_cov_stack C' (f::stk) ((tc,lc)::ts) (g::stk') <=>
     g.cf_state = tc /\
     lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME g.cf_fn /\
     active_inst g.cf_fn g.cf_inst tc /\
     fmp_cov_stack C' stk ts stk') /\
  (fmp_cov_stack C' _ _ _ <=> F)
End

(* A target state of the lowered fn' is covered when it runs only
   inserted instructions, in its block, up to a state t1 related to a
   reachable source point, or when it is past the RETURNDATACOPY of a
   revert forwarding of its block. *)
Definition fmp_cov_def:
  fmp_cov D C C' vs vs' fmp eom stk' fn' t <=>
    (?stk PG G tn fn inst s sm lo t1 ts restored bb'.
       frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
       ~s.vs_halted /\
       fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
         stk PG G tn fn s lo t1 ts /\
       lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       fmp_cov_stack C' stk ts stk' /\
       t.vs_current_bb = t1.vs_current_bb /\
       lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       t.vs_inst_idx <= t1.vs_inst_idx /\
       (!k. fmp_target_run k C' fn.fn_name t
              (t1.vs_inst_idx - t.vs_inst_idx) t1) /\
       !i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb'.bb_instructions /\
           fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) \/
    (?bb' p j. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       revert_forward_pair bb' p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j)
End

Theorem fmp_stage_coverage:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable vs' C' stk' PG' G' tn' fn' ti t ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn' t
Proof
  cheat
QED

Theorem fmp_cov_mem:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t ==>
  lowered_mem_fact eom C' fn' ti t
Proof
  cheat
QED

Theorem fmp_lowering_stage_lowered_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' /\ max_live_eom C = SOME eom ==>
  mem_inv (lowered_mem_fact eom) C' vs'
Proof
  cheat
QED
