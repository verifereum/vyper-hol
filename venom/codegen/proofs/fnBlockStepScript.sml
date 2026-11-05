(*
 * The step of the fuel induction behind
 * venomToAsmProps$gen_fn_frame_simulation: one non-entry block, run from
 * a block boundary where fn_frame_inv holds, simulated by its DFS code.
 *
 * TOP-LEVEL (CHEATED, a skeleton piece):
 *   fn_block_frame_step - gen_fn_frame_sim_at (SUC fuel) from both
 *                         function theorems at fuel
 *)

Theory fnBlockStep
Ancestors
  fnBlockBody fnFrameSinglePred fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics

(* run_blocks (SUC fuel) runs the current block with run_block fuel and
   continues with run_blocks fuel from its OK result (run_blocks_unfold);
   an INVOKE inside the block runs its callee with run_function fuel.  So
   the hypotheses are the callee simulation (gen_fn_sim_at fuel) and the
   rest of the run from the successor (gen_fn_frame_sim_at fuel).

   Why it should hold: the block's code is its DFS plan (dfs_block_code_placed),
   and the lineage state the run arrived with regenerates that code
   (lineage_state_block_plan).  The block runs as its PHI prefix
   (phi_prefix_frame_sim), then one instruction at a time against
   fn_frame_inv: gen_inst_frame_sim and gas_inst_frame_sim for ordinary
   steps, gen_invoke_frame_sim with the callee hypothesis for INVOKE, and
   at the end gen_jmp_frame_sim / gen_jnz_frame_sim (successor), the halt
   and abort steps (fnFrameTerminal), revert_forward_frame_sim, or
   gen_ret_frame_sim (IntRet).  At a successor the step re-establishes the
   block-boundary premises of gen_fn_frame_sim_at for it (lineage_entry
   from this block, dfs_block_state, the alias premise by
   lineage_alias_successor), and the successor run's assembly steps are
   added to the block's (asm_steps_add_ok). *)
Theorem fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_frame_sim_at (SUC fuel)
Proof
  cheat
QED
