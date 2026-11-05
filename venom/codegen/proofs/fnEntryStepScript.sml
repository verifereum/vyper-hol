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
  venomExecSemantics

(* As for fn_block_frame_step, but for the entry block, which
   gen_fn_frame_sim_at excludes.

   Why it should hold: the region's plan starts with the entry block's
   code (fn_region_placed), planned from the function planner's initial
   state for some label counter, which generate_context_plan fixes for
   region i (that is the lbl_ctr gen_fn_frame_sim_at asks for).  The
   parameter prefix turns fn_entry_state_rel into fn_frame_inv with
   mem0 = as.as_memory (entry_params_frame_sim); the rest of the block
   runs as in fn_block_frame_step.  At the successor the run continues by
   gen_fn_frame_sim_at fuel, whose IntRet clause gives
   fn_return_state_rel: its spill-byte clause is the frame's against
   mem0, and its call, tx and block context, code and prev-hash clauses
   hold because the Venom run never changes those fields and
   fn_entry_state_rel equates them with as's. *)
Theorem fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_sim_at (SUC fuel)
Proof
  cheat
QED
