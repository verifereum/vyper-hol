(*
 * The symbolic fuel induction: the two steps of fnEntryStep and fnBlockStep
 * with the symbolic run added, and their closure over all fuel.  The
 * concrete function-level statements at each fuel come from codegen's own
 * steps (fn_entry_block_step, fn_block_frame_step).
 *
 * TOP-LEVEL:
 *   sym_fn_entry_block_step  - sym_fn_sim_at (SUC fuel) from the four
 *                              function statements at fuel
 *   sym_fn_block_frame_step  - sym_fn_frame_sim_at (SUC fuel), likewise
 *   sym_fn_sims_all          - all four at every fuel
 *)
Theory symFnStep
Ancestors
  symBlockBody symFrameBoundary symFnSimSpec codegenSymRel fnEntryStep
  fnBlockStep fnBlockStepHelpers fnBlockBody fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomExecSemantics
  venomState

Theorem sym_fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_frame_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_sims_all:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel
Proof
  Induct
  >- (simp[gen_fn_sim_at_def, gen_fn_frame_sim_at_def, sym_fn_sim_at_def,
           sym_fn_frame_sim_at_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_entry_block_step, fn_block_frame_step,
            sym_fn_entry_block_step, sym_fn_block_frame_step]
QED
