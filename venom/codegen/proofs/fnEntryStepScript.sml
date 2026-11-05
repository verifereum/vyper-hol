(*
 * The step of the fuel induction behind venomToAsmProps$gen_fn_simulation:
 * the entry block, run from fn_entry_state_rel, simulated by the code at
 * the start of the function's region.
 *
 * TOP-LEVEL (CHEATED, a skeleton piece):
 *   fn_entry_block_step - gen_fn_sim_at (SUC fuel) from both function
 *                         theorems at fuel
 *)

Theory fnEntryStep
Ancestors
  fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockBody fnEntryPlan fnEntryPc fnEntryParams fnRunFields

(* As for fn_block_frame_step, but for the entry block, which
   gen_fn_frame_sim_at excludes.

   Why it should hold: region i's plan is the function planner's output
   for some label counter (fnEntryPlan$region_fn_plan) and starts with
   the entry block's code, planned from the initial state ps0: its label,
   its parameter code, then its instructions' code
   (fnEntryPlan$entry_block_plan).  The premise's asm_block_at puts that
   code at as.as_pc, which is where the entry label resolves
   (fnEntryPc$entry_pc_placed).  The entry block has no PHIs
   (fnEntryParams$entry_run_block), and the parameter prefix turns
   fn_entry_state_rel into fn_frame_inv at ps1 with mem0 = as.as_memory
   (fnEntryParams$entry_prefix_frame_sim, which also gives Inv, the
   labels and the alias premise at the state vs_p after it).  So
   run_blocks (SUC fuel) from vs is block_rest from vs_p, which
   fnBlockBody$block_body_frame_sim simulates (bb = HD fn.fn_blocks,
   ps_l = ps_dfs = ps0 with its own cleanup fields, k = the parameter
   count, ps = ps1, prefix_ops = the parameter code); its steps are added
   to the prefix's.  Its IntRet clause gives fn_return_state_rel: the
   spill-byte clause is the frame's against mem0, and the call, tx and
   block context, code and prev-hash clauses hold because the run never
   changes those fields (fnRunFields$run_blocks_intret_fields) and
   fn_entry_state_rel equates them with as's. *)
Theorem fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_sim_at (SUC fuel)
Proof
  cheat
QED
